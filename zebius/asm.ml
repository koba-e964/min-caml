(* 2オペランドではなく3オペランドのx86アセンブリもどき *)

type id_or_imm = V of Id.t | C of int
type t = (* 命令の列 (caml2html: sparcasm_t) *)
  | Ans of exp
  | Let of (Id.t * Type.t) * exp * t
and exp = (* 一つ一つの命令に対応する式 (caml2html: sparcasm_exp) *)
  | Nop
  | Set of int
  | SetF of float
  | SetL of Id.l
  | Mov of Id.t
  | Neg of Id.t
  | Add of Id.t * id_or_imm
  | Sub of Id.t * Id.t
  | Arith of Syntax.a_op * Id.t * id_or_imm (* immediate only *)
  | Ld of Id.t (* @addr *)
  | St of Id.t * Id.t (* op1 = @op2 *)
  | FMovD of Id.t
  | FNegD of Id.t
  | FAddD of Id.t * Id.t
  | FSubD of Id.t * Id.t
  | FMulD of Id.t * Id.t
  | FDivD of Id.t * Id.t
  | LdF of Id.t
  | StF of Id.t * Id.t
  | Comment of string
  (* virtual instructions *)
  | IfEq of Id.t * Id.t * t * t
  | IfLE of Id.t * Id.t * t * t
  | IfFEq of Id.t * Id.t * t * t
  | IfFLE of Id.t * Id.t * t * t
  (* closure address, integer arguments, and float arguments *)
  | CallCls of Id.t * Id.t list * Id.t list
  | CallDir of Id.l * Id.t list * Id.t list
  | Save of Id.t * Id.t (* レジスタ変数の値をスタック変数へ保存 (caml2html: sparcasm_save) *)
  | Restore of Id.t (* スタック変数から値を復元 (caml2html: sparcasm_restore) *)
type vardef = { vname : Id.l; vtype : Type.t; vbody : t }
type fundef = { name : Id.l; args : Id.t list; fargs : Id.t list; body : t; ret : Type.t }
(* プログラム全体 = 浮動小数点数テーブル + トップレベル関数 + メインの式 (caml2html: sparcasm_prog) *)
type prog = Prog of (Id.l * float) list * vardef list * fundef list * t

let fletd(x, e1, e2) = Let((x, Type.Float), e1, e2)
let seq(e1, e2) = Let((Id.gentmp Type.Unit, Type.Unit), e1, e2)

let regs = Array.init 12 (fun i -> Printf.sprintf "R%d" i)
let fregs = Array.init 16 (fun i -> Printf.sprintf "FR%d" i)
let allregs = Array.to_list regs
let allfregs = Array.to_list fregs
let reg_cl = regs.(Array.length regs - 1) (* closure address (caml2html: sparcasm_regcl) *)
(*
let reg_sw = regs.(Array.length regs - 1) (* temporary for swap *)
let reg_fsw = fregs.(Array.length fregs - 1) (* temporary for swap *)
*)
let reg_sp = "R15" (* stack pointer *)
let reg_hp = "min_caml_hp" (* heap pointer (caml2html: sparcasm_reghp) *)
(* let reg_ra = "%eax" (* return address *) *)
let is_reg x = (x.[0] = 'R' || x = reg_hp)

(* super-tenuki *)
let rec remove_and_uniq xs = function
  | [] -> []
  | x :: ys when S.mem x xs -> remove_and_uniq xs ys
  | x :: ys -> x :: remove_and_uniq (S.add x xs) ys

(* free variables in the order of use (for spilling) (caml2html: sparcasm_fv) *)
let fv_id_or_imm = function V(x) -> [x] | _ -> []
let rec fv_exp = function
  | Nop | Set(_) | SetF _ | SetL(_) | Comment(_) | Restore(_) -> []
  | Mov(x) | Neg(x) | FMovD(x) | FNegD(x) | Save(x, _)  | Ld x | LdF x | Arith (_, x,_) -> [x]
  | Add(x, y') -> x :: fv_id_or_imm y'
  | St(x, y) | StF(x, y) | Sub(x, y) | FAddD(x, y) | FSubD(x, y) | FMulD(x, y) | FDivD(x, y) -> [x; y]
  | IfEq(x, y', e1, e2) | IfLE(x, y', e1, e2) -> x :: y' :: remove_and_uniq S.empty (fv e1 @ fv e2) (* uniq here just for efficiency *)
  | IfFEq(x, y, e1, e2) | IfFLE(x, y, e1, e2) -> x :: y :: remove_and_uniq S.empty (fv e1 @ fv e2) (* uniq here just for efficiency *)
  | CallCls(x, ys, zs) -> x :: ys @ zs
  | CallDir(_, ys, zs) -> ys @ zs
and fv = function
  | Ans(exp) -> fv_exp exp
  | Let((x, t), exp, e) ->
      fv_exp exp @ remove_and_uniq (S.singleton x) (fv e)
let fv e = remove_and_uniq S.empty (fv e)

let rec concat e1 xt e2 =
  match e1 with
  | Ans(exp) -> Let(xt, exp, e2)
  | Let(yt, exp, e1') -> Let(yt, exp, concat e1' xt e2)

let align i = (if i mod 8 = 0 then i else i + 4)

let rec string_of_list ls = match ls with
  | []        -> ""
  |  hd :: tl -> List.fold_left (fun x y -> x ^ "," ^ y) hd tl
let rec show_asm_t (syn : t) : string = match syn with
  | Ans x -> show_exp x
  | Let ((id,ty), x, t) -> "let " ^ id ^ " : " ^ Type.show_type_t ty ^ " := " ^ show_exp x ^ " in\n" ^ show_asm_t t
and show_ii = function
  | V name -> "V:" ^ name
  | C i    -> "C:" ^ string_of_int i
and show_exp x = match x with
  | Nop -> "nop"
  | Set i -> "set " ^ string_of_int i
  | SetF f -> "setf " ^ string_of_float f
  | SetL (Id.L i) -> "set_l " ^ i
  | Mov id -> "mov " ^ id
  | Neg id -> "neg " ^ id
  | Add (id, v) -> "add " ^ id ^ ", " ^ show_ii v
  | Sub (id, v) -> "sub " ^ id ^ ", " ^ v
  | Arith (Syntax.AMul, id, v) -> "mul " ^ id ^ ", " ^ show_ii v
  | Arith (Syntax.ADiv, id, v) -> "div " ^ id ^ ", " ^ show_ii v
  | Ld (id) -> "ld " ^ id 
  | St (id1, id2) -> "st " ^ id1 ^ ", @" ^ id2
  | FMovD id -> "flop"
  | FNegD id -> "flop"
  | FAddD (id1,id2) -> "flop"
  | FSubD (id1,id2) -> "flop"
  | FMulD (id1,id2) -> "flop"
  | FDivD (id1,id2) -> "flop"
  | LdF (id1) -> "ldf " ^ id1
  | StF (id1,id2) -> "stf " ^ id1 ^ ", @" ^ id2
  | Comment str -> "comment " ^ str
  | IfEq (id, v, x, y) -> "if " ^ id ^ " = " ^ v ^ "\nthen " ^ show_asm_t x ^ "\nelse " ^ show_asm_t y
  | IfLE (id, v, x, y) -> "if " ^ id ^ " <= " ^ v ^ "\nthen " ^ show_asm_t x ^ "\nelse " ^ show_asm_t y
  | IfFEq (id1,id2,x,y) -> "if " ^ id1 ^ " .= " ^ id2 ^ "\nthen " ^ show_asm_t x ^ "\nelse " ^ show_asm_t y
  | IfFLE (id1,id2,x,y) -> "if " ^ id1 ^ " .<= " ^ id2 ^ "\nthen " ^ show_asm_t x ^ "\nelse " ^ show_asm_t y
  | CallCls (idl, ls1, ls2) -> "call_cls " ^ idl ^ List.fold_left (fun x y -> x ^ "," ^ y) "" (ls1 @ ls2)
  | CallDir (Id.L idl, ls1, ls2) -> "call_dir " ^ idl ^ List.fold_left (fun x y -> x ^ "," ^ y) "" (ls1 @ ls2)
  | Save (id1, id2) -> "save " ^ id1 ^ ", " ^ id2
  | Restore id -> "restore " ^ id
and show_vardef { vname = Id.L n; vtype = ty; vbody = exp } =
  "vardef " ^ n ^ " : " ^ Type.show_type_t ty ^ " :=\n" ^ show_asm_t exp ^ "\n"
and show_fundef f = match f with
  | { name = Id.L id; args = ls; fargs; body; ret } -> "fundef " ^ id ^ "(" ^ string_of_list (ls @ fargs) ^ ") : "  ^ Type.show_type_t ret ^ " {\n" ^ show_asm_t body ^ "\n}"
let show_prog (Prog (ls, vardefs, fundefs, t)) = 
  List.fold_left (fun x y -> x ^ show_fundef y ^ "\n") (List.fold_left (fun x y -> x ^ show_vardef y ^ "\n") "" vardefs) fundefs ^ show_asm_t t

