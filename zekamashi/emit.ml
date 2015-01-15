open Asm
open Inst


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
let offset x = wordsize * List.hd (locate x)
let stacksize () = align ((List.length !stackmap + 1) * wordsize)

let insts = Queue.create ()

let emit_inst (inst : zek_inst) = Queue.add inst insts


let reg r = 
  if is_reg r
  then String.sub r 1 (String.length r - 1)
  else r 

let reg_of_string r = 
  if is_reg r
  then Reg (int_of_string (String.sub r 2 (String.length r - 2)))
  else failwith ("invalid regname" ^ r)

let freg_of_string r = 
  if is_reg r
  then FReg (int_of_string (String.sub r 2 (String.length r - 2)))
  else failwith ("invalid regname" ^ r)

let rsp = Reg 30
let rtmp = Reg 28
let rlr = Reg 29
let rhp = Reg 27
let frtmp = FReg 30
let rcl = Reg 26
let rtmp2 = Reg 25 (* TODO ad-hoc temporary register for JMP instruction, since operands must differ *)

let ri_of_ri r = match r with
  | V x ->
    if is_reg x
    then RIReg (int_of_string (String.sub x 2 (String.length x - 2)))
    else failwith "invalid regname"
  | C i -> RIImm i

let ri_of_reg (Reg x) = RIReg x


let load_label r label =
  emit_inst (Inst.Mov (reg_of_string r, label))

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

let load_imm imm reg =
  if Int32.compare imm (Int32.of_int (-32768)) >= 0 && Int32.compare imm (Int32.of_int 32768) < 0
    then
      emit_inst (Inst.li (Int32.to_int imm) reg)
    else
      let m = Int32.to_int (Int32.logand imm (Int32.of_int 0xffff)) in
      let m' = if m >= 32768 then m - 65536 else m in
      let n = Int32.to_int (Int32.shift_right (Int32.sub imm (Int32.of_int m')) 16) in
      let n' = if n >= 32768 then n - 65536 else n in
      if m' = 0 then
        emit_inst (Ldah (reg, n', Reg 31))
      else begin
        emit_inst (Lda (reg, m', Reg 31));
        emit_inst (Ldah (reg, n', reg))
      end

type dest = Tail | NonTail of Id.t (* 末尾かどうかを表すデータ型 *)
let rec g oc = function (* 命令列のアセンブリ生成 *)
  | (dest, Ans (exp)) -> g' oc (dest, exp)
  | (dest, Let((x, t), exp, e)) -> g' oc (NonTail (x), exp); g oc (dest, e)
and g' oc = function (* 各命令のアセンブリ生成 *)
    (* 末尾でなかったら計算結果を dest にセット *)
  | (NonTail(_), Nop) -> ()
  | (NonTail x, Li i) ->
      let r = reg_of_string x in
      load_imm (Int32.of_int i) r
  | (NonTail x, FLi fl) ->
     let bits = Int32.bits_of_float fl in
     load_imm bits rtmp;
     emit_inst (Itofs (rtmp, freg_of_string x));
     emit_inst (Inst.Comment (Printf.sprintf "%f : %s" fl (Int32.to_string bits)))
  | (NonTail(x), SetL(Id.L(y))) -> 
      load_label x y
  | (NonTail(x), Mr(y)) when x = y -> ()
  | (NonTail(x), Mr(y)) -> emit_inst (mov (reg_of_string y) (reg_of_string x))
  | (NonTail(x), Neg(y)) -> emit_inst (Subl (Reg 31, (match reg_of_string y with Reg i -> RIReg i), reg_of_string x))
  | (NonTail(x), Add (y, z)) -> 
      emit_inst (Addl (reg_of_string y, ri_of_ri z, reg_of_string x))
  | (NonTail(x), Sub (y, z)) -> 
      emit_inst (Subl (reg_of_string y, ri_of_ri z, reg_of_string x))
  | (NonTail(x), Arith (Syntax.AMul, y, C 2)) ->
      let Reg ry = reg_of_string y in
      emit_inst (Addl (Reg ry, RIReg ry, reg_of_string x))
  | (NonTail(x), Arith (Syntax.AMul, y, C 4)) ->
      let Reg ry = reg_of_string y in
      emit_inst (Sll (Reg ry, RIImm 2, reg_of_string x))
  | (NonTail(x), Arith (Syntax.ADiv, y, C 2)) ->
      let Reg ry = reg_of_string y in
      emit_inst (Srl (Reg ry, RIImm 1, reg_of_string x))
  | (NonTail(x), Arith (_, y, z)) -> 
      failwith "arith is not supported (emit.ml)"
  | (NonTail(x), Slw(y, z)) -> 
      emit_inst (Sll (reg_of_string y, ri_of_ri z, reg_of_string x)) 
      (* Printf.fprintf oc "\tslwi\t%s, %s, %d\n" (reg x) (reg y) z *)
  | (NonTail(x), Lwz(y, V(z))) ->
      emit_inst (Addl (reg_of_string y, ri_of_reg (reg_of_string z), rtmp));
      emit_inst (Ldl (reg_of_string x, 0, rtmp))
      (* Printf.fprintf oc "\tlwzx\t%s, %s, %s\n" (reg x) (reg y) (reg z) *)
  | (NonTail(x), Lwz(y, C(z))) -> 
      (* Printf.fprintf oc "\tlwz\t%s, %d(%s)\n" (reg x) z (reg y) *)
      emit_inst (Ldl (reg_of_string x, z, reg_of_string y));
  | (NonTail(_), Stw(x, y, V(z))) ->
      emit_inst (Addl (reg_of_string y, ri_of_reg (reg_of_string z), rtmp));
      emit_inst (Stl (reg_of_string x, 0, rtmp))
      (* Printf.fprintf oc "\tstwx\t%s, %s, %s\n" (reg x) (reg y) (reg z) *)
  | (NonTail(_), Stw(x, y, C(z))) -> 
      (* Printf.fprintf oc "\tstw\t%s, %d(%s)\n" (reg x) z (reg y) *)
      emit_inst (Stl (reg_of_string x, z, reg_of_string y));
  | (NonTail(x), FMr(y)) when x = y -> ()
  | (NonTail(x), FMr(y)) -> emit_inst (Inst.fmov (freg_of_string y) (freg_of_string x))
  | (NonTail(x), FNeg(y)) -> 
      emit_inst (FOp (FOpSub, FReg 31, freg_of_string y, freg_of_string x))
  | (NonTail(x), FAdd(y, z)) ->
      emit_inst (FOp (FOpAdd, freg_of_string y, freg_of_string z, freg_of_string x))
  | (NonTail(x), FSub(y, z)) -> 
      emit_inst (FOp (FOpSub, freg_of_string y, freg_of_string z, freg_of_string x))
  | (NonTail(x), FMul(y, z)) -> 
      emit_inst (FOp (FOpMul, freg_of_string y, freg_of_string z, freg_of_string x))
  | (NonTail(x), FDiv(y, z)) ->
        emit_inst (Invs (freg_of_string z, frtmp));
        emit_inst (FOp (FOpMul, freg_of_string y, frtmp, freg_of_string x))
  | (NonTail(x), Lfd(y, V(z))) ->
      emit_inst (Addl (reg_of_string y, ri_of_reg (reg_of_string z), rtmp));
      emit_inst (Lds (freg_of_string x, 0, rtmp))
  | (NonTail(x), Lfd(y, C(z))) -> 
      emit_inst (Lds (freg_of_string x, z, reg_of_string y))
  | (NonTail(_), Stfd(x, y, V(z))) ->
      emit_inst (Addl (reg_of_string y, ri_of_reg (reg_of_string z), rtmp));
      emit_inst (Sts (freg_of_string x, 0, rtmp))
  | (NonTail(_), Stfd(x, y, C(z))) ->
      emit_inst (Sts (freg_of_string x, z, reg_of_string y))
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
        emit_inst (Sts (freg_of_string x, offset y, rsp))
  | (NonTail(_), Save(x, y)) -> assert (S.mem y !stackset); ()
  (* 復帰の仮想命令の実装 *)
  | (NonTail(x), Restore(y)) when List.mem x allregs ->
      (* Printf.fprintf oc "\tlwz\t%s, %d(%s)\n" (reg x) (offset y) reg_sp *)
      emit_inst (Ldl (reg_of_string x, offset y, rsp))
  | (NonTail(x), Restore(y)) ->
      assert (List.mem x allfregs);
      emit_inst (Lds (freg_of_string x, offset y, rsp))
  (* 末尾だったら計算結果を第一レジスタにセット *)
  | (Tail, (Nop | Stw _ | Stfd _ | Asm.Comment _ | Save _ as exp)) ->
      g' oc (NonTail(Id.gentmp Type.Unit), exp);
      emit_inst (Ret (rtmp, rlr));
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
      emit_inst (Ret (rtmp, rlr));
  | (Tail, IfEq(x, y, e1, e2)) ->
      emit_inst (Subl (reg_of_string x, ri_of_ri y, rtmp));
      g'_tail_if oc e1 e2 "beq" NE
  | (Tail, IfLE(x, C y, e1, e2)) ->
      load_imm (Int32.of_int y) rtmp;
      emit_inst (Cmp (CLE, reg_of_string x, ri_of_reg rtmp, rtmp));
      g'_tail_if oc e1 e2 "ble" EQ
  | (Tail, IfLE(x, V y, e1, e2)) ->
      emit_inst (Cmp (CLE, reg_of_string x, ri_of_ri (V y), rtmp));
      g'_tail_if oc e1 e2 "ble" EQ
  | (Tail, IfGE(x, C y, e1, e2)) ->
      load_imm (Int32.of_int y) rtmp;
      emit_inst (Cmp (CLT, reg_of_string x, ri_of_reg rtmp, rtmp));
      g'_tail_if oc e1 e2 "bge" NE
  | (Tail, IfGE(x, V y, e1, e2)) ->
      emit_inst (Cmp (CLT, reg_of_string x, ri_of_ri (V y), rtmp));
      g'_tail_if oc e1 e2 "bge" NE
  | (Tail, IfFEq(x, y, e1, e2)) ->
      emit_inst (Cmps (CEQ, freg_of_string x, freg_of_string y, frtmp));
      (* Printf.fprintf oc "\tfcmpu\tcr7, %s, %s\n" (reg x) (reg y); *)
      g'_tail_if_float oc e1 e2 "beq" EQ
  | (Tail, IfFLE(x, y, e1, e2)) ->
      emit_inst (Cmps (CLE, freg_of_string x, freg_of_string y, frtmp));
      (* Printf.fprintf oc "\tfcmpu\tcr7, %s, %s\n" (reg x) (reg y); *)
      g'_tail_if_float oc e1 e2 "ble" EQ
  | (NonTail(z), IfEq(x, y, e1, e2)) ->
      emit_inst (Subl (reg_of_string x, ri_of_ri y, rtmp));
      g'_non_tail_if oc (NonTail(z)) e1 e2 "beq" NE
  | (NonTail(z), IfLE(x, C y, e1, e2)) ->
      load_imm (Int32.of_int y) rtmp;
      emit_inst (Cmp (CLE, reg_of_string x, ri_of_reg rtmp, rtmp));
      g'_non_tail_if oc (NonTail(z)) e1 e2 "ble" EQ
  | (NonTail(z), IfLE(x, V y, e1, e2)) ->
      emit_inst (Cmp (CLE, reg_of_string x, ri_of_ri (V y), rtmp));
      g'_non_tail_if oc (NonTail(z)) e1 e2 "ble" EQ
  | (NonTail(z), IfGE(x, C y, e1, e2)) ->
      load_imm (Int32.of_int y) rtmp;
      emit_inst (Cmp (CLT, reg_of_string x, ri_of_reg rtmp, rtmp));
      g'_non_tail_if oc (NonTail(z)) e1 e2 "ble" NE
  | (NonTail(z), IfGE(x, V y, e1, e2)) ->
      emit_inst (Cmp (CLT, reg_of_string x, ri_of_ri (V y), rtmp));
      g'_non_tail_if oc (NonTail(z)) e1 e2 "ble" NE
  | (NonTail(z), IfFEq(x, y, e1, e2)) ->
      emit_inst (Cmps (CEQ, freg_of_string x, freg_of_string y, frtmp));
      (* Printf.fprintf oc "\tfcmpu\tcr7, %s, %s\n" (reg x) (reg y); *)
      g'_non_tail_if_float oc (NonTail(z)) e1 e2 "beq" EQ
  | (NonTail(z), IfFLE(x, y, e1, e2)) ->
      emit_inst (Cmps (CLE, freg_of_string x, freg_of_string y, frtmp));
      (* Printf.fprintf oc "\tfcmpu\tcr7, %s, %s\n" (reg x) (reg y); *)
      g'_non_tail_if_float oc (NonTail(z)) e1 e2 "ble" EQ
  (* 関数呼び出しの仮想命令の実装 *)
  | (Tail, CallCls(x, ys, zs)) -> (* 末尾呼び出し *)
      g'_args oc [(x, reg_cl)] ys zs;
      (* Printf.fprintf oc "\tlwz\t%s, 0(%s)\n" (reg reg_sw) (reg reg_cl); *)
      emit_inst (Ldl (rtmp, 0, reg_of_string reg_cl));
      emit_inst (Jmp (rtmp2, rtmp))
      (* Printf.fprintf oc "\tmtctr\t%s\n\tbctr\n" (reg reg_sw); *)
  | (Tail, CallDir(Id.L(x), ys, zs)) -> (* 末尾呼び出し *)
      g'_args oc [] ys zs;
      (* Printf.fprintf oc "\tb\t%s\n" x *)
      emit_inst (Br (rtmp, x))
  | (NonTail(a), CallCls(x, ys, zs)) ->
      (* Printf.fprintf oc "\tmflr\t%s\n" reg_tmp; *)
      g'_args oc [(x, reg_cl)] ys zs;
      let ss = stacksize () in
	(* Printf.fprintf oc "\tstw\t%s, %d(%s)\n" reg_tmp (ss - 4) reg_sp; *)
        emit_inst (Stl (rlr, ss - wordsize, rsp));
	(* Printf.fprintf oc "\taddi\t%s, %s, %d\n" reg_sp reg_sp ss; *)
        emit_inst (Addl (rsp, RIImm ss, rsp));
	(* Printf.fprintf oc "\tlwz\t%s, 0(%s)\n" reg_tmp (reg reg_cl); *)
        emit_inst (Ldl (rtmp, 0 * wordsize, rcl));
	(* Printf.fprintf oc "\tmtctr\t%s\n" reg_tmp;
	Printf.fprintf oc "\tbctrl\n"; *)
        emit_inst (Jsr (rlr, rtmp));
	(* Printf.fprintf oc "\tsubi\t%s, %s, %d\n" reg_sp reg_sp ss;
	Printf.fprintf oc "\tlwz\t%s, %d(%s)\n" reg_tmp (ss - 4) reg_sp; *)
        emit_inst (Subl (rsp, RIImm ss, rsp));
        emit_inst (Ldl (rtmp, ss - wordsize, rsp));
	(if List.mem a allregs && a <> regs.(0) then 
	   (* Printf.fprintf oc "\tmr\t%s, %s\n" (reg a) (reg regs.(0)) *)
           emit_inst (Inst.mov (Reg 0) (reg_of_string a)) 
	 else if List.mem a allfregs && a <> fregs.(0) then 
           emit_inst (Inst.fmov (FReg 0) (freg_of_string a)));
	   (* Printf.fprintf oc "\tfmr\t%s, %s\n" (reg a) (reg fregs.(0))); *)
	(* Printf.fprintf oc "\tmtlr\t%s\n" reg_tmp *)
        emit_inst (Inst.mov rtmp rlr)
  | (NonTail(a), CallDir(Id.L(x), ys, zs)) -> 
      (* Printf.fprintf oc "\tmflr\t%s\n" reg_tmp; *)
      g'_args oc [] ys zs;
      let ss = stacksize () in
	(* Printf.fprintf oc "\tstw\t%s, %d(%s)\n" reg_tmp (ss - 4) reg_sp; *)
        emit_inst (Stl (rlr, ss - wordsize, rsp));
	(* Printf.fprintf oc "\taddi\t%s, %s, %d\n" reg_sp reg_sp ss; *)
        emit_inst (Addl (rsp, RIImm ss, rsp));
	(* Printf.fprintf oc "\tbl\t%s\n" x; *)
        emit_inst (Bsr (rlr, x));
	(* Printf.fprintf oc "\tsubi\t%s, %s, %d\n" reg_sp reg_sp ss; *)
        emit_inst (Subl (rsp, RIImm ss, rsp));
	(* Printf.fprintf oc "\tlwz\t%s, %d(%s)\n" reg_tmp (ss - 4) reg_sp; *)
        emit_inst (Ldl (rlr, ss - wordsize, rsp));
	(if List.mem a allregs && a <> regs.(0) then
	   (* Printf.fprintf oc "\tmr\t%s, %s\n" (reg a) (reg regs.(0)) *)
           emit_inst (Inst.mov (Reg 0) (reg_of_string a))
	 else if List.mem a allfregs && a <> fregs.(0) then
           emit_inst (Inst.fmov (FReg 0) (freg_of_string a)))
and g'_tail_if oc e1 e2 b bcond = 
  let b_else = Id.genid (b ^ "_else") in
    (* Printf.fprintf oc "\t%s\tcr7, %s\n" bn b_else; *)
    emit_inst (BC (bcond, rtmp, b_else));
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
    emit_inst (BC (bcond, rtmp, b_else));
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
and g'_tail_if_float oc e1 e2 b bcond = 
  let b_else = Id.genid (b ^ "_else") in
    (* Printf.fprintf oc "\t%s\tcr7, %s\n" bn b_else; *)
    emit_inst (FBC (bcond, frtmp, b_else));
    let stackset_back = !stackset in
      g oc (Tail, e1);
      (* Printf.fprintf oc "%s:\n" b_else; *)
      emit_inst (Label b_else);
      stackset := stackset_back;
      g oc (Tail, e2)
and g'_non_tail_if_float oc dest e1 e2 b bcond = 
  let b_else = Id.genid (b ^ "_else") in
  let b_cont = Id.genid (b ^ "_cont") in
    (* Printf.fprintf oc "\t%s\tcr7, %s\n" bn b_else; *)
    emit_inst (FBC (bcond, frtmp, b_else));
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
        (fun (z, fr) -> emit_inst (Inst.fmov (freg_of_string z) (freg_of_string fr)))
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
  emit_inst (li 0x6000 rhp);
  emit_inst (Inst.Comment "main program start");
  stackset := S.empty;
  stackmap := [];
  g oc (NonTail("%R0"), e);
  emit_inst (Inst.Comment "main program end");
  emit_inst (Br (rtmp, "min_caml_main_end"));
  List.iter (fun fundef -> h oc fundef) fundefs;
  emit_inst (ExtFile asmlib);
  emit_inst (Label "min_caml_main_end");
  emit_inst (mov (Reg 0) (Reg 0));
  emit oc insts;

