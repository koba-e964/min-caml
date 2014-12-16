open Asm
open Inst

let gethi (x : float) : int32 = Int32.shift_right_logical (Int32.bits_of_float x) 16
let getlo (x : float) : int32 = Int32.logand (Int32.bits_of_float x) (Int32.of_int 0xffff)

let stackset = ref S.empty (* すでに Save された変数の集合 *)
let stackmap = ref [] (* Save された変数のスタックにおける位置 *)
let save x = 
  stackset := S.add x !stackset;
  if not (List.mem x !stackmap) then
    stackmap := !stackmap @ [x]
let savef x = 
  stackset := S.add x !stackset;
  if not (List.mem x !stackmap) then
    (let pad = 
       if List.length !stackmap mod 2 = 0 then [] else [Id.gentmp Type.Int] in
       stackmap := !stackmap @ pad @ [x; x])
let locate x = 
  let rec loc = function 
    | [] -> []
    | y :: zs when x = y -> 0 :: List.map succ (loc zs)
    | y :: zs -> List.map succ (loc zs) in
    loc !stackmap
let offset x = 4 * List.hd (locate x)
let stacksize () = align ((List.length !stackmap + 1) * 4)

let insts = Queue.create ()

let emit_inst (inst : zek_inst) = Queue.add inst insts


let reg r = 
  if is_reg r
  then String.sub r 1 (String.length r - 1)
  else r 

let reg_of_string r = 
  if is_reg r
  then Reg (int_of_string (String.sub r 2 (String.length r - 2)))
  else failwith "invalid regname" 

let rsp = Reg 30
let rtmp = Reg 28
let rlr = Reg 29

let ri_of_ri r = match r with
  | V x ->
    if is_reg x
    then RIReg (int_of_string (String.sub x 2 (String.length x - 2)))
    else failwith "invalid regname"
  | C i -> RIImm i



let load_label r label =
  "\tlis\t" ^ (reg r) ^ ", ha16(" ^ label ^ ")\n" ^
  "\taddi\t" ^ (reg r) ^ ", " ^ (reg r) ^ ", lo16(" ^ label ^ ")\n"

(* 関数呼び出しのために引数を並べ替える (register shuffling) *)
let rec shuffle sw xys = 
  (* remove identical moves *)
  let (_, xys) = List.partition (fun (x, y) -> x = y) xys in
    (* find acyclic moves *)
    match List.partition (fun (_, y) -> List.mem_assoc y xys) xys with
      | ([], []) -> []
      | ((x, y) :: xys, []) -> (* no acyclic moves; resolve a cyclic move *)
	  (y, sw) :: (x, y) :: 
	    shuffle sw (List.map (function 
				    | (y', z) when y = y' -> (sw, z)
				    | yz -> yz) xys)
      | (xys, acyc) -> acyc @ shuffle sw xys

type dest = Tail | NonTail of Id.t (* 末尾かどうかを表すデータ型 *)
let rec g oc = function (* 命令列のアセンブリ生成 *)
  | (dest, Ans (exp)) -> g' oc (dest, exp)
  | (dest, Let((x, t), exp, e)) -> g' oc (NonTail (x), exp); g oc (dest, e)
and g' oc = function (* 各命令のアセンブリ生成 *)
    (* 末尾でなかったら計算結果を dest にセット *)
  | (NonTail(_), Nop) -> ()
  | (NonTail(x), Li(i)) when i >= -32768 && i < 32768 -> 
      (* Printf.fprintf oc "\tli\t%s, %d\n" (reg x) i *)
      emit_inst (Inst.li i (reg_of_string x))
  | (NonTail(x), Li(i)) ->
      let n = i lsr 16 in
      let m = i lxor (n lsl 16) in
      let r = reg_of_string x in
        emit_inst (Lda (r, n, Reg 31));
        emit_inst (Ldah (r, m, r))
        
  | (NonTail(x), FLi(Id.L(l))) ->
      let s = load_label reg_tmp l in
      Printf.fprintf oc "%s\tlfd\t%s, 0(%s)\n" s (reg x) reg_tmp
  | (NonTail(x), SetL(Id.L(y))) -> 
      let s = load_label x y in
      Printf.fprintf oc "%s" s
  | (NonTail(x), Mr(y)) when x = y -> ()
  | (NonTail(x), Mr(y)) -> Printf.fprintf oc "\tmr\t%s, %s\n" (reg x) (reg y)
  | (NonTail(x), Neg(y)) -> Printf.fprintf oc "\tneg\t%s, %s\n" (reg x) (reg y)
  | (NonTail(x), Add (y, z)) -> 
      emit_inst (Addl (reg_of_string y, ri_of_ri z, reg_of_string x))
  | (NonTail(x), Sub (y, z)) -> 
      emit_inst (Subl (reg_of_string y, ri_of_ri z, reg_of_string x))
  | (NonTail(x), Arith (Syntax.AMul, y, C 2)) ->
      let Reg ry = reg_of_string y in
      emit_inst (Addl (Reg ry, RIReg ry, reg_of_string x))
  | (NonTail(x), Arith (_, y, z)) -> 
      failwith "arith is not supported (emit.ml)"
  | (NonTail(x), Slw(y, V(z))) -> 
      Printf.fprintf oc "\tslw\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), Slw(y, C(z))) -> 
      Printf.fprintf oc "\tslwi\t%s, %s, %d\n" (reg x) (reg y) z
  | (NonTail(x), Lwz(y, V(z))) ->
      Printf.fprintf oc "\tlwzx\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), Lwz(y, C(z))) -> 
      (* Printf.fprintf oc "\tlwz\t%s, %d(%s)\n" (reg x) z (reg y) *)
      emit_inst (Ldl (reg_of_string x, z, reg_of_string y));
  | (NonTail(_), Stw(x, y, V(z))) ->
      Printf.fprintf oc "\tstwx\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | (NonTail(_), Stw(x, y, C(z))) -> 
      (* Printf.fprintf oc "\tstw\t%s, %d(%s)\n" (reg x) z (reg y) *)
      emit_inst (Stl (reg_of_string x, z, reg_of_string y));
  | (NonTail(x), FMr(y)) when x = y -> ()
  | (NonTail(x), FMr(y)) -> Printf.fprintf oc "\tfmr\t%s, %s\n" (reg x) (reg y)
  | (NonTail(x), FNeg(y)) -> 
      Printf.fprintf oc "\tfneg\t%s, %s\n" (reg x) (reg y)
  | (NonTail(x), FAdd(y, z)) -> 
      Printf.fprintf oc "\tfadd\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), FSub(y, z)) -> 
      Printf.fprintf oc "\tfsub\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), FMul(y, z)) -> 
      Printf.fprintf oc "\tfmul\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), FDiv(y, z)) -> 
      Printf.fprintf oc "\tfdiv\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), Lfd(y, V(z))) ->
      Printf.fprintf oc "\tlfdx\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), Lfd(y, C(z))) -> 
      Printf.fprintf oc "\tlfd\t%s, %d(%s)\n" (reg x) z (reg y)
  | (NonTail(_), Stfd(x, y, V(z))) ->
      Printf.fprintf oc "\tstfdx\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | (NonTail(_), Stfd(x, y, C(z))) ->
      Printf.fprintf oc "\tstfd\t%s, %d(%s)\n" (reg x) z (reg y)
  | (NonTail(_), Asm.Comment(s)) -> emit_inst (Inst.Comment s)
  (* 退避の仮想命令の実装 *)
  | (NonTail(_), Save(x, y))
      when List.mem x allregs && not (S.mem y !stackset) ->
      save y;
	(* Printf.fprintf oc "\tstw\t%s, %d(%s)\n" (reg x) (offset y) reg_sp *)
      emit_inst (Stl (reg_of_string x, offset y, rsp))

  | (NonTail(_), Save(x, y)) 
      when List.mem x allfregs && not (S.mem y !stackset) ->
      savef y;
	Printf.fprintf oc "\tstfd\t%s, %d(%s)\n" (reg x) (offset y) reg_sp
  | (NonTail(_), Save(x, y)) -> assert (S.mem y !stackset); ()
  (* 復帰の仮想命令の実装 *)
  | (NonTail(x), Restore(y)) when List.mem x allregs ->
      (* Printf.fprintf oc "\tlwz\t%s, %d(%s)\n" (reg x) (offset y) reg_sp *)
      emit_inst (Ldl (reg_of_string x, offset y, rsp))
  | (NonTail(x), Restore(y)) ->
      assert (List.mem x allfregs);
      Printf.fprintf oc "\tlfd\t%s, %d(%s)\n" (reg x) (offset y) reg_sp
  (* 末尾だったら計算結果を第一レジスタにセット *)
  | (Tail, (Nop | Stw _ | Stfd _ | Asm.Comment _ | Save _ as exp)) ->
      g' oc (NonTail(Id.gentmp Type.Unit), exp);
      Printf.fprintf oc "\tblr\n";
  | (Tail, (Li _ | SetL _ | Mr _ | Neg _ | Add _ | Sub _ | Arith _ | Slw _ |
            Lwz _ as exp)) -> 
      g' oc (NonTail(regs.(0)), exp);
      emit_inst (Ret (rtmp, rlr))
  | (Tail, (FLi _ | FMr _ | FNeg _ | FAdd _ | FSub _ | FMul _ | FDiv _ |
            Lfd _ as exp)) ->
      g' oc (NonTail(fregs.(0)), exp);
      emit_inst (Ret (rtmp, rlr))
  | (Tail, (Restore(x) as exp)) ->
      (match locate x with
	 | [i] -> g' oc (NonTail(regs.(0)), exp)
	 | [i; j] when (i + 1 = j) -> g' oc (NonTail(fregs.(0)), exp)
	 | _ -> assert false);
      Printf.fprintf oc "\tblr\n";
  | (Tail, IfEq(x, y, e1, e2)) ->
      emit_inst (Cmp (CEQ, reg_of_string x, ri_of_ri y, rtmp));
      g'_tail_if oc e1 e2 "beq" NE
  | (Tail, IfLE(x, y, e1, e2)) ->
      emit_inst (Cmp (CLE, reg_of_string x, ri_of_ri y, rtmp));
      g'_tail_if oc e2 e1 "ble" LE
  | (Tail, IfGE(x, y, e1, e2)) ->
      emit_inst (Cmp (CLT, reg_of_string x, ri_of_ri y, rtmp));
      g'_tail_if oc e1 e2 "bge" GE
  | (Tail, IfFEq(x, y, e1, e2)) ->
      Printf.fprintf oc "\tfcmpu\tcr7, %s, %s\n" (reg x) (reg y);
      g'_tail_if oc e1 e2 "beq" NE
  | (Tail, IfFLE(x, y, e1, e2)) ->
      Printf.fprintf oc "\tfcmpu\tcr7, %s, %s\n" (reg x) (reg y);
      g'_tail_if oc e2 e1 "ble" LE
  | (NonTail(z), IfEq(x, V(y), e1, e2)) ->
      Printf.fprintf oc "\tcmpw\tcr7, %s, %s\n" (reg x) (reg y);
      g'_non_tail_if oc (NonTail(z)) e1 e2 "beq" NE
  | (NonTail(z), IfEq(x, C(y), e1, e2)) ->
      Printf.fprintf oc "\tcmpwi\tcr7, %s, %d\n" (reg x) y;
      g'_non_tail_if oc (NonTail(z)) e1 e2 "beq" NE
  | (NonTail(z), IfLE(x, V(y), e1, e2)) ->
      Printf.fprintf oc "\tcmpw\tcr7, %s, %s\n" (reg x) (reg y);
      g'_non_tail_if oc (NonTail(z)) e2 e1 "ble" LE
  | (NonTail(z), IfLE(x, C(y), e1, e2)) ->
      Printf.fprintf oc "\tcmpwi\tcr7, %s, %d\n" (reg x) y;
      g'_non_tail_if oc (NonTail(z)) e2 e1 "ble" LE
  | (NonTail(z), IfGE(x, V(y), e1, e2)) ->
      Printf.fprintf oc "\tcmpw\tcr7, %s, %s\n" (reg x) (reg y);
      g'_non_tail_if oc (NonTail(z)) e2 e1 "bge" GE
  | (NonTail(z), IfGE(x, C(y), e1, e2)) ->
      Printf.fprintf oc "\tcmpwi\tcr7, %s, %d\n" (reg x) y;
      g'_non_tail_if oc (NonTail(z)) e2 e1 "bge" GE
  | (NonTail(z), IfFEq(x, y, e1, e2)) ->
      Printf.fprintf oc "\tfcmpu\tcr7, %s, %s\n" (reg x) (reg y);
      g'_non_tail_if oc (NonTail(z)) e1 e2 "beq" NE
  | (NonTail(z), IfFLE(x, y, e1, e2)) ->
      Printf.fprintf oc "\tfcmpu\tcr7, %s, %s\n" (reg x) (reg y);
      g'_non_tail_if oc (NonTail(z)) e2 e1 "ble" LE
  (* 関数呼び出しの仮想命令の実装 *)
  | (Tail, CallCls(x, ys, zs)) -> (* 末尾呼び出し *)
      failwith "not yet implemented (callcls)";
      g'_args oc [(x, reg_cl)] ys zs;
      (* Printf.fprintf oc "\tlwz\t%s, 0(%s)\n" (reg reg_sw) (reg reg_cl); *)
      emit_inst (Ldl (reg_of_string reg_sw, 0, reg_of_string reg_cl));
      Printf.fprintf oc "\tmtctr\t%s\n\tbctr\n" (reg reg_sw);
  | (Tail, CallDir(Id.L(x), ys, zs)) -> (* 末尾呼び出し *)
      g'_args oc [] ys zs;
      (* Printf.fprintf oc "\tb\t%s\n" x *)
      emit_inst (Br (rtmp, x))
  | (NonTail(a), CallCls(x, ys, zs)) ->
      failwith "not yet implemented (callcls)";
      Printf.fprintf oc "\tmflr\t%s\n" reg_tmp;
      g'_args oc [(x, reg_cl)] ys zs;
      let ss = stacksize () in
	(* Printf.fprintf oc "\tstw\t%s, %d(%s)\n" reg_tmp (ss - 4) reg_sp; *)
        emit_inst (Stl (rtmp, ss - 4, rsp));
	(* Printf.fprintf oc "\taddi\t%s, %s, %d\n" reg_sp reg_sp ss; *)
        emit_inst (Addl (rsp, RIImm ss, rsp));
	Printf.fprintf oc "\tlwz\t%s, 0(%s)\n" reg_tmp (reg reg_cl);
	Printf.fprintf oc "\tmtctr\t%s\n" reg_tmp;
	Printf.fprintf oc "\tbctrl\n";
	Printf.fprintf oc "\tsubi\t%s, %s, %d\n" reg_sp reg_sp ss;
	Printf.fprintf oc "\tlwz\t%s, %d(%s)\n" reg_tmp (ss - 4) reg_sp;
	(if List.mem a allregs && a <> regs.(0) then 
	   Printf.fprintf oc "\tmr\t%s, %s\n" (reg a) (reg regs.(0)) 
	 else if List.mem a allfregs && a <> fregs.(0) then 
	   Printf.fprintf oc "\tfmr\t%s, %s\n" (reg a) (reg fregs.(0)));
	(* Printf.fprintf oc "\tmtlr\t%s\n" reg_tmp *)
        emit_inst (Inst.mov rtmp rlr)
  | (NonTail(a), CallDir(Id.L(x), ys, zs)) -> 
      (* Printf.fprintf oc "\tmflr\t%s\n" reg_tmp; *)
      g'_args oc [] ys zs;
      let ss = stacksize () in
	(* Printf.fprintf oc "\tstw\t%s, %d(%s)\n" reg_tmp (ss - 4) reg_sp; *)
        emit_inst (Stl (rlr, ss - 4, rsp));
	(* Printf.fprintf oc "\taddi\t%s, %s, %d\n" reg_sp reg_sp ss; *)
        emit_inst (Addl (rsp, RIImm ss, rsp));
	(* Printf.fprintf oc "\tbl\t%s\n" x; *)
        emit_inst (Bsr (rlr, x));
	(* Printf.fprintf oc "\tsubi\t%s, %s, %d\n" reg_sp reg_sp ss; *)
        emit_inst (Subl (rsp, RIImm ss, rsp));
	(* Printf.fprintf oc "\tlwz\t%s, %d(%s)\n" reg_tmp (ss - 4) reg_sp; *)
        emit_inst (Ldl (rlr, ss - 4, rsp));
	(if List.mem a allregs && a <> regs.(0) then
	   (* Printf.fprintf oc "\tmr\t%s, %s\n" (reg a) (reg regs.(0)) *)
           emit_inst (Inst.mov (Reg 0) (reg_of_string a))
	 else if List.mem a allfregs && a <> fregs.(0) then
	   Printf.fprintf oc "\tfmr\t%s, %s\n" (reg a) (reg fregs.(0)))
and g'_tail_if oc e1 e2 b bcond = 
  let b_else = Id.genid (b ^ "_else") in
    (* Printf.fprintf oc "\t%s\tcr7, %s\n" bn b_else; *)
    emit_inst (BC (NE, rtmp, b_else));
    let stackset_back = !stackset in
      g oc (Tail, e1);
      (* Printf.fprintf oc "%s:\n" b_else; *)
      emit_inst (Label b_else);
      stackset := stackset_back;
      g oc (Tail, e2)
and g'_non_tail_if oc dest e1 e2 b bcond = 
  let b_else = Id.genid (b ^ "_else") in
  let b_cont = Id.genid (b ^ "_cont") in
    (* Printf.fprintf oc "\t%s\tcr7, %s\n" bn b_else; *)
    emit_inst (BC (NE, rtmp, b_else));
    let stackset_back = !stackset in
      g oc (dest, e1);
      let stackset1 = !stackset in
	(* Printf.fprintf oc "\tb\t%s\n" b_cont; *)
        emit_inst (Br (rtmp, b_cont));
	(* Printf.fprintf oc "%s:\n" b_else; *)
        emit_inst (Label b_else);
	stackset := stackset_back;
	g oc (dest, e2);
	(* Printf.fprintf oc "%s:\n" b_cont; *)
        emit_inst (Label b_cont);
	let stackset2 = !stackset in
	  stackset := S.inter stackset1 stackset2
and g'_args oc x_reg_cl ys zs = 
  let (i, yrs) = 
    List.fold_left
      (fun (i, yrs) y -> (i + 1, (y, regs.(i)) :: yrs))
      (0, x_reg_cl) ys in
    List.iter
      (fun (y, r) -> emit_inst (Inst.mov (reg_of_string y) (reg_of_string r)))
      (shuffle reg_sw yrs);
    let (d, zfrs) = 
      List.fold_left
	(fun (d, zfrs) z -> (d + 1, (z, fregs.(d)) :: zfrs))
	(0, []) zs in
      List.iter
        (fun (z, fr) -> Printf.fprintf oc "\tfmr\t%s, %s\n" (reg fr) (reg z))
	(shuffle reg_fsw zfrs)

let h oc { name = Id.L(x); args = _; fargs = _; body = e; ret = _ } =
  (* Printf.fprintf oc "%s:\n" x; *)
  emit_inst (Label x);
  stackset := S.empty;
  stackmap := [];
  g oc (Tail, e)

let f oc asmlib (Prog(data, fundefs, e)) =
  Format.eprintf "generating assembly...@.";
  emit_inst (li 0x4000 rsp);
  emit_inst (Inst.Comment "main program start");
  stackset := S.empty;
  stackmap := [];
  g oc (NonTail("_R_0"), e);
  emit_inst (Inst.Comment "main program end");
  emit_inst (Br (rtmp, "min_caml_main_end"));
  List.iter (fun fundef -> h oc fundef) fundefs;
  emit_inst (ExtFile asmlib);
  emit_inst (Label "min_caml_main_end");
  emit_inst (mov (Reg 0) (Reg 0));
  emit oc insts;

