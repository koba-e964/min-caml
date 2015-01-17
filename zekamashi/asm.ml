(* PowerPC assembly with a few virtual instructions *)

type id_or_imm = V of Id.t | C of int
type t = (* 命令の列 *)
  | Ans of exp
  | Let of (Id.t * Type.t) * exp * t
and exp = (* 一つ一つの命令に対応する式 *)
  | Nop
  | Li of int
  | FLi of float
  | SetL of Id.l
  | Mr of Id.t
  | Neg of Id.t
  | Add of Id.t * id_or_imm
  | Sub of Id.t * id_or_imm
  | Arith of Syntax.a_op * Id.t * id_or_imm
  | Slw of Id.t * id_or_imm
  | Lwz of Id.t * id_or_imm
  | Stw of Id.t * Id.t * id_or_imm
  | FMr of Id.t 
  | FNeg of Id.t
  | FAdd of Id.t * Id.t
  | FSub of Id.t * Id.t
  | FMul of Id.t * Id.t
  | FDiv of Id.t * Id.t
  | Lfd of Id.t * id_or_imm
  | Stfd of Id.t * Id.t * id_or_imm
  | Comment of string
  (* virtual instructions *)
  | IfEq of Id.t * id_or_imm * t * t
  | IfLE of Id.t * id_or_imm * t * t
  | IfGE of Id.t * id_or_imm * t * t
  | IfFEq of Id.t * Id.t * t * t
  | IfFLE of Id.t * Id.t * t * t
  (* closure address, integer arguments, and float arguments *)
  | CallCls of Id.t * Id.t list * Id.t list
  | CallDir of Id.l * Id.t list * Id.t list
  | Save of Id.t * Id.t (* レジスタ変数の値をスタック変数へ保存 *)
  | Restore of Id.t (* スタック変数から値を復元 *)
type fundef =
    { name : Id.l; args : Id.t list; fargs : Id.t list; body : t; ret : Type.t }
type vardef =
    { vname : Id.l * Type.t; vbody : t }
(* プログラム全体 = 浮動小数点数テーブル + トップレベル関数 + メインの式 *)
type prog = Prog of vardef list * fundef list * t

(* shorthand of Let for float *)
(* fletd : Id.t * exp * t -> t *)
let fletd (x, e1, e2) = Let ((x, Type.Float), e1, e2)
(* shorthand of Let for unit *)
(* seq : exp * t -> t *)
let seq (e1, e2) = Let ((Id.gentmp Type.Unit, Type.Unit), e1, e2)

(* let regs = Array.init 27 (fun i -> Printf.sprintf "%%R%d" i) *)
(* TODO ad-hoc modification, see emit.ml *)
let regs = Array.append (Array.init 25 (fun i -> Printf.sprintf "%%R%d" i)) (Array.make 1 "%R26")
let fregs = Array.init 30 (fun i -> Printf.sprintf "%%f%d" i)
let allregs = Array.to_list regs
let allfregs = Array.to_list fregs
let reg_cl = regs.(Array.length regs - 1) (* closure address *)
let reg_sw = regs.(Array.length regs - 2) (* temporary for swap *)
let reg_fsw = fregs.(Array.length fregs - 1) (* temporary for swap *)
let reg_hp = "%R27"
let reg_sp = "%R30"
let reg_tmp = "%R28"
let freg_tmp = "%f30"

let wordsize = 4

(* is_reg : Id.t -> bool *)
let is_reg x = x.[0] = '%'

(* remove_and_uniq : S.t -> Id.t list -> Id.t list *)
let rec remove_and_uniq xs = function 
  | [] -> []
  | x :: ys when S.mem x xs -> remove_and_uniq xs ys
  | x :: ys -> x :: remove_and_uniq (S.add x xs) ys

(* free variables in the order of use (for spilling) *)
(* fv_id_or_imm : id_or_imm -> Id.t list *)
let fv_id_or_imm = function V (x) -> [x] | _ -> []
(* fv_exp : Id.t list -> t -> S.t list *)
let rec fv_exp = function
  | Nop | Li (_) | FLi (_) | SetL (_) | Comment (_) | Restore (_) -> []
  | Mr (x) | Neg (x) | FMr (x) | FNeg (x) | Save (x, _) -> [x]
  | Add (x, y') | Sub (x, y') | Arith (_, x, y') | Slw (x, y') | Lfd (x, y') | Lwz (x, y') -> 
      x :: fv_id_or_imm y'
  | FAdd (x, y) | FSub (x, y) | FMul (x, y) | FDiv (x, y) ->
      [x; y]
  | Stw (x, y, z') | Stfd (x, y, z') -> x :: y :: fv_id_or_imm z'
  | IfEq (x, y', e1, e2) | IfLE (x, y', e1, e2) | IfGE (x, y', e1, e2) -> 
      x :: fv_id_or_imm y' @ remove_and_uniq S.empty (fv e1 @ fv e2)
  | IfFEq (x, y, e1, e2) | IfFLE (x, y, e1, e2) ->
      x :: y :: remove_and_uniq S.empty (fv e1 @ fv e2)
  | CallCls (x, ys, zs) -> x :: ys @ zs
  | CallDir (_, ys, zs) -> ys @ zs
and fv = function 
  | Ans (exp) -> fv_exp exp
  | Let ((x, t), exp, e) ->
      fv_exp exp @ remove_and_uniq (S.singleton x) (fv e)

(* fv : t -> Id.t list *)
let fv e = remove_and_uniq S.empty (fv e)

(* concat : t -> Id.t * Type.t -> t -> t *)
let rec concat e1 xt e2 = match e1 with
  | Ans (exp) -> Let (xt, exp, e2)
  | Let (yt, exp, e1') -> Let (yt, exp, concat e1' xt e2)

(* align : int -> int *)
let align i = i (* No need of alignment *)


let show_id_or_imm = function
  | V x -> "V:" ^ x
  | C i -> "C:" ^ string_of_int i

let rec show_exp = function
  | Nop -> "nop"
  | Li x -> "li " ^ string_of_int x
  | FLi f -> "fli " ^ string_of_float f
  | SetL (Id.L l) -> "setl " ^ l 
  | Comment (_) -> "(* *)"
  | Restore x -> "restore " ^ x
  | Mr x -> "mr " ^ x
  | Neg x -> "neg " ^ x
  | FMr x -> "fmr " ^ x
  | FNeg x -> "fneg " ^ x
  | Save (x, y) -> "save " ^ x ^ ", " ^ y
  | Add (x, y') -> "+ " ^ x ^ show_id_or_imm y'
  | Sub (x, y') -> "- " ^ x ^ show_id_or_imm y'
  | Arith (Syntax.AMul, x, y') -> "+ " ^ x ^ show_id_or_imm y'
  | Arith (Syntax.ADiv, x, y') -> "- " ^ x ^ show_id_or_imm y'
  | Slw (x, y') -> "<< " ^ x ^ show_id_or_imm y'
  | Lfd (x, y') -> "lfd " ^ x ^ "+" ^ show_id_or_imm y'
  | Lwz (x, y') ->  "lwz " ^ x ^ "+" ^ show_id_or_imm y'
  | FAdd (x, y) | FSub (x, y) | FMul (x, y) | FDiv (x, y) ->
      "flop "
  | Stw (x, y, z') | Stfd (x, y, z') -> "store"
  | IfEq (x, y', e1, e2) | IfLE (x, y', e1, e2) | IfGE (x, y', e1, e2) -> 
      "conditional"
  | IfFEq (x, y, e1, e2) | IfFLE (x, y, e1, e2) ->
      "float conditional"
  | CallCls (nm, ys, zs) -> "call-cls " ^ nm ^ "(" ^ string_of_list ys ^ ") (" ^ string_of_list zs ^ ")"
  | CallDir (Id.L nm, ys, zs) -> "call-dir " ^ nm ^ "(" ^ string_of_list ys ^ ") (" ^ string_of_list zs ^ ")"
and show_asm_t = function
  | Ans e -> show_exp e
  | Let ((nm, ty), e1, e2) ->
     "let " ^ nm ^ " := " ^ show_exp e1 ^ "\n" ^ show_asm_t e2

and show_vardef { vname = (Id.L n, ty); vbody = exp } =
  "vardef " ^ n ^ " : " ^ Type.show_type_t ty ^ " :=\n" ^ show_asm_t exp ^ "\n"
and string_of_list ls = match ls with
  | []        -> ""
  |  hd :: tl -> List.fold_left (fun x y -> x ^ "," ^ y) hd tl

let show_fundef { name = Id.L id; args = ls; fargs; body; ret }
  = "fundef " ^ id ^ "(" ^ string_of_list (ls @ fargs) ^ ") : "  ^ Type.show_type_t ret ^ " {\n" ^ show_asm_t body ^ "\n}"

let show_prog (Prog (vardefs, fundefs, expr)) =
  List.fold_left (fun x y -> x ^ show_fundef y ^ "\n") "" fundefs
  ^ List.fold_left (fun x y -> x ^ show_vardef y ^ "\n") "" vardefs
  ^ show_asm_t expr



