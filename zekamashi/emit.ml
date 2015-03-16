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
    stackmap := !stackmap @ [x]
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
let emit_insts (inst : zek_inst list) = List.map (fun x -> Queue.add x insts) inst

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


let rtmp2 = Reg 25 (* TODO ad-hoc temporary register for JMP instruction, since operands must differ *)
let rcl = Reg 26
let rhp = Reg 27
let rtmp = Reg 28
let rlr = Reg 29
let rsp = Reg 30
let frtmp = FReg 30

let stackplace = ref 0 (* Current place of stack *)

let set_sp v = let cur = !stackplace in
  if cur <> v then begin
    emit_inst (Lda (rsp, v - cur, rsp));
    stackplace := v
  end

let set_sp_quiet v = stackplace := v


let load_sp r v = let cur = !stackplace in
  emit_inst (Ldl (r, v - cur, rsp))
let store_sp r v = let cur = !stackplace in
  emit_inst (Stl (r, v - cur, rsp))
let loadf_sp r v = let cur = !stackplace in
  emit_inst (Lds (r, v - cur, rsp))
let storef_sp r v = let cur = !stackplace in
  emit_inst (Sts (r, v - cur, rsp))

(* emit return instructions *)
let return () =
  set_sp 0;
  emit_inst (Ret (rtmp, rlr))

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

let is_imm_range x = 0 <= x && x <= 255

let rec g oc = function (* 命令列のアセンブリ生成 *)
  | (dest, Ans (exp)) -> g' oc (dest, exp)
  | (dest, Let((x, t), exp, e)) -> g' oc (NonTail (x), exp); g oc (dest, e)
and g' oc = function (* 各命令のアセンブリ生成 *)
    (* 末尾でなかったら計算結果を dest にセット *)
  | (NonTail(_), Nop) -> ()
  | (NonTail x, Li i) ->
      let r = reg_of_string x in
      load_imm (Int32.of_int i) r
  | (NonTail x, FLi fl)  when fl = 0.0 ->
     emit_inst (FOp (FOpMul, FReg 31, FReg 31, freg_of_string x));
     emit_inst (Inst.Comment "0.0 = 0.0 * 0.0")
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
  | (NonTail(x), Lwz(y, V(z))) ->
      emit_inst (Addl (reg_of_string y, ri_of_reg (reg_of_string z), rtmp));
      emit_inst (Ldl (reg_of_string x, 0, rtmp))
  | (NonTail(x), Lwz(y, C(z))) -> 
      emit_inst (Ldl (reg_of_string x, z, reg_of_string y));
  | (NonTail(_), Stw(x, y, V(z))) ->
      emit_inst (Addl (reg_of_string y, ri_of_reg (reg_of_string z), rtmp));
      emit_inst (Stl (reg_of_string x, 0, rtmp))
  | (NonTail(_), Stw(x, y, C(z))) -> 
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
  | (NonTail x, Native ("sqrt", [y])) ->
        emit_inst (Sqrts (freg_of_string y, freg_of_string x))
  | (NonTail _, Native ("print_char", [y])) ->
        let mcpc = Id.genid "mcpc" in
        emit_inst (Ldah (rtmp, 16, Reg 31));
        emit_inst (Label mcpc);
        emit_inst (Ldl (rtmp2, 2, rtmp));
        emit_inst (And (rtmp2, RIImm 1, rtmp2));
        emit_inst (BC (Inst.EQ, rtmp2, mcpc));
        emit_inst (And (reg_of_string y, RIImm 255, rtmp2));
        emit_inst (Stl (rtmp2, 3, rtmp))
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
      store_sp (reg_of_string x) (offset y)
      (* emit_inst (Stl (reg_of_string x, offset y, rsp)) *)

  | (NonTail(_), Save(x, y)) 
      when List.mem x allfregs && not (S.mem y !stackset) ->
      savef y;
      storef_sp (freg_of_string x) (offset y)
      (* emit_inst (Sts (freg_of_string x, offset y, rsp)) *)
  | (NonTail(_), Save(x, y)) -> assert (S.mem y !stackset); ()
  (* 復帰の仮想命令の実装 *)
  | (NonTail(x), Restore(y)) when List.mem x allregs ->
      load_sp (reg_of_string x) (offset y)
      (* emit_inst (Ldl (reg_of_string x, offset y, rsp)) *)
  | (NonTail(x), Restore(y)) ->
      assert (List.mem x allfregs);
      loadf_sp (freg_of_string x) (offset y)
      (* emit_inst (Lds (freg_of_string x, offset y, rsp)) *)
  (* 末尾だったら計算結果を第一レジスタにセット *)
  | (Tail, (Nop | Stw _ | Stfd _ | Asm.Comment _ | Save _ | Native ("print_char", _) as exp)) ->
      g' oc (NonTail(Id.gentmp Type.Unit), exp);
      return ();
  | (Tail, (Li _ | SetL _ | Mr _ | Neg _ | Add _ | Sub _ | Arith _ | Slw _ |
            Lwz _ as exp)) -> 
      g' oc (NonTail(regs.(0)), exp);
      return ()
  | (Tail, (FLi _ | FMr _ | FNeg _ | FAdd _ | FSub _ | FMul _ | FDiv _ | Native ("sqrt", _) |
            Lfd _ as exp)) ->
      g' oc (NonTail(fregs.(0)), exp);
      return ()
  | (Tail, (Restore(x) as exp)) ->
      (match locate x with
	 | [i] -> g' oc (NonTail(regs.(0)), exp)
	 | [i; j] when (i + 1 = j) -> g' oc (NonTail(fregs.(0)), exp)
	 | _ -> assert false);
      return ();
  | (Tail, IfEq(x, y, e1, e2)) ->
      if y = C 0 then
        g'_tail_if oc e1 e2 "beq" (reg_of_string x) NE
      else begin
        emit_inst (Subl (reg_of_string x, ri_of_ri y, rtmp));
        g'_tail_if oc e1 e2 "beq" rtmp NE
      end
  | (Tail, IfLE(x, C y, e1, e2)) ->
      if is_imm_range y then
        emit_inst (Cmp (CLE, reg_of_string x, RIImm y, rtmp))
      else begin
        load_imm (Int32.of_int y) rtmp;
        emit_inst (Cmp (CLE, reg_of_string x, ri_of_reg rtmp, rtmp))
      end;
      g'_tail_if oc e1 e2 "ble" rtmp EQ
  | (Tail, IfLE(x, V y, e1, e2)) ->
      emit_inst (Cmp (CLE, reg_of_string x, ri_of_ri (V y), rtmp));
      g'_tail_if oc e1 e2 "ble" rtmp EQ
  | (Tail, IfGE(x, C y, e1, e2)) ->
      if is_imm_range y then
        emit_inst (Cmp (CLT, reg_of_string x, RIImm y, rtmp))
      else begin
        load_imm (Int32.of_int y) rtmp;
        emit_inst (Cmp (CLT, reg_of_string x, ri_of_reg rtmp, rtmp))
      end;
      g'_tail_if oc e1 e2 "bge" rtmp NE
  | (Tail, IfGE(x, V y, e1, e2)) ->
      emit_inst (Cmp (CLT, reg_of_string x, ri_of_ri (V y), rtmp));
      g'_tail_if oc e1 e2 "bge" rtmp NE
  | (Tail, IfFEq(x, y, e1, e2)) ->
      emit_inst (Cmps (CEQ, freg_of_string x, freg_of_string y, frtmp));
      g'_tail_if_float oc e1 e2 "beq" frtmp EQ
  | (Tail, IfFLE(x, y, e1, e2)) ->
      emit_inst (Cmps (CLE, freg_of_string x, freg_of_string y, frtmp));
      g'_tail_if_float oc e1 e2 "ble" frtmp EQ
  | (Tail, IfF0(x, e1, e2)) ->
      g'_tail_if_float oc e1 e2 "beq" (freg_of_string x) NE
  | (NonTail(z), IfEq(x, y, e1, e2)) ->
      if y = C 0 then
        g'_non_tail_if oc (NonTail z) e1 e2 "beq" (reg_of_string x) NE
      else begin
        emit_inst (Subl (reg_of_string x, ri_of_ri y, rtmp));
        g'_non_tail_if oc (NonTail(z)) e1 e2 "beq" rtmp NE
      end
  | (NonTail(z), IfLE(x, C y, e1, e2)) ->
      if is_imm_range y then
        emit_inst (Cmp (CLE, reg_of_string x, RIImm y, rtmp))
      else begin
        load_imm (Int32.of_int y) rtmp;
        emit_inst (Cmp (CLE, reg_of_string x, ri_of_reg rtmp, rtmp))
      end;
      g'_non_tail_if oc (NonTail(z)) e1 e2 "ble" rtmp EQ
  | (NonTail(z), IfLE(x, V y, e1, e2)) ->
      emit_inst (Cmp (CLE, reg_of_string x, ri_of_ri (V y), rtmp));
      g'_non_tail_if oc (NonTail(z)) e1 e2 "ble" rtmp EQ
  | (NonTail(z), IfGE(x, C y, e1, e2)) ->
      if is_imm_range y then
        emit_inst (Cmp (CLT, reg_of_string x, RIImm y, rtmp))
      else begin
        load_imm (Int32.of_int y) rtmp;
        emit_inst (Cmp (CLT, reg_of_string x, ri_of_reg rtmp, rtmp))
      end;
      g'_non_tail_if oc (NonTail(z)) e1 e2 "ble" rtmp NE
  | (NonTail(z), IfGE(x, V y, e1, e2)) ->
      emit_inst (Cmp (CLT, reg_of_string x, ri_of_ri (V y), rtmp));
      g'_non_tail_if oc (NonTail(z)) e1 e2 "ble" rtmp NE
  | (NonTail(z), IfFEq(x, y, e1, e2)) ->
      emit_inst (Cmps (CEQ, freg_of_string x, freg_of_string y, frtmp));
      g'_non_tail_if_float oc (NonTail(z)) e1 e2 "nt_fbeq" frtmp EQ
  | (NonTail(z), IfFLE(x, y, e1, e2)) ->
      emit_inst (Cmps (CLE, freg_of_string x, freg_of_string y, frtmp));
      g'_non_tail_if_float oc (NonTail(z)) e1 e2 "nt_fble" frtmp EQ
  | (NonTail(z), IfF0(x, e1, e2)) ->
      g'_non_tail_if_float oc (NonTail(z)) e1 e2 "nt_fbeq" (freg_of_string x) NE
  (* 関数呼び出しの仮想命令の実装 *)
  | (Tail, CallCls(x, ys, zs)) -> (* 末尾呼び出し *)
      g'_args oc [(x, reg_cl)] ys zs;
      emit_inst (Ldl (rtmp, 0, reg_of_string reg_cl));
      set_sp 0;
      emit_inst (Jmp (rtmp2, rtmp))
  | (Tail, CallDir(Id.L(x), ys, zs)) -> (* 末尾呼び出し *)
      g'_args oc [] ys zs;
      set_sp 0;
      emit_inst (Br (rtmp, x))
  | (NonTail(a), CallCls(x, ys, zs)) ->
      g'_args oc [(x, reg_cl)] ys zs;
      let ss = stacksize () in
        store_sp rlr (ss - wordsize);
        (* emit_inst (Stl (rlr, ss - wordsize, rsp)); *)
        set_sp ss;
        (*  emit_inst (Addl (rsp, RIImm ss, rsp)); *)
        emit_inst (Ldl (rtmp, 0 * wordsize, rcl));
        emit_inst (Jsr (rlr, rtmp));
        (* emit_inst (Subl (rsp, RIImm ss, rsp)); *)
        load_sp rlr (ss - wordsize);
        (* emit_inst (Ldl (rtmp, ss - wordsize, rsp)); *)
	(if List.mem a allregs && a <> regs.(0) then 
           emit_inst (Inst.mov (Reg 0) (reg_of_string a)) 
	 else if List.mem a allfregs && a <> fregs.(0) then 
           emit_inst (Inst.fmov (FReg 0) (freg_of_string a)));
        emit_inst (Inst.mov rtmp rlr)
  | (NonTail(a), CallDir(Id.L(x), ys, zs)) -> 
      g'_args oc [] ys zs;
      let ss = stacksize () in
        store_sp rlr (ss - wordsize);
        (* emit_inst (Stl (rlr, ss - wordsize, rsp)); *)
        set_sp ss;
        (* emit_inst (Addl (rsp, RIImm ss, rsp)); *)
        emit_inst (Bsr (rlr, x));
        (* emit_inst (Subl (rsp, RIImm ss, rsp)); *)
        load_sp rlr (ss - wordsize);
        (* emit_inst (Ldl (rlr, ss - wordsize, rsp)); *)
	(if List.mem a allregs && a <> regs.(0) then
           emit_inst (Inst.mov (Reg 0) (reg_of_string a))
	 else if List.mem a allfregs && a <> fregs.(0) then
           emit_inst (Inst.fmov (FReg 0) (freg_of_string a))
         else if not (List.mem a allregs || List.mem a allfregs) then
           failwith ("neither regs nor fregs: " ^ a))
and g'_tail_if oc e1 e2 b rcond bcond = 
  let b_else = Id.genid (b ^ "_else") in
    emit_inst (BC (bcond, rcond, b_else));
    let stackset_back = !stackset in
      let curst = !stackplace in
      g oc (Tail, e1);
      emit_inst (Label b_else);
      stackset := stackset_back;
      set_sp_quiet curst;
      g oc (Tail, e2)
and g'_non_tail_if oc dest e1 e2 b rcond bcond = 
  let b_else = Id.genid (b ^ "_else") in
  let b_cont = Id.genid (b ^ "_cont") in
    emit_inst (BC (bcond, rcond, b_else));
    let stackset_back = !stackset in
      let curst = !stackplace in
      g oc (dest, e1);
      set_sp 0;
      let stackset1 = !stackset in
        emit_inst (Br (rtmp, b_cont));
        emit_inst (Label b_else);
	stackset := stackset_back;
        set_sp_quiet curst;
	g oc (dest, e2);
        set_sp 0;
        emit_inst (Label b_cont);
	let stackset2 = !stackset in
	  stackset := S.inter stackset1 stackset2
and g'_tail_if_float oc e1 e2 b frcond bcond = 
  let b_else = Id.genid (b ^ "_else") in
    emit_inst (FBC (bcond, frcond, b_else));
    let stackset_back = !stackset in
      let curst = !stackplace in
      g oc (Tail, e1);
      emit_inst (Label b_else);
      stackset := stackset_back;
      set_sp_quiet curst;
      g oc (Tail, e2)
and g'_non_tail_if_float oc dest e1 e2 b frcond bcond = 
  let b_else = Id.genid (b ^ "_else") in
  let b_cont = Id.genid (b ^ "_cont") in
    emit_inst (FBC (bcond, frcond, b_else));
    let stackset_back = !stackset in
      let curst = !stackplace in
      g oc (dest, e1);
      set_sp 0;
      let stackset1 = !stackset in
        emit_inst (Br (rtmp, b_cont));
        emit_inst (Label b_else);
	stackset := stackset_back;
        set_sp_quiet curst;
	g oc (dest, e2);
        set_sp 0;
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
      (shuffle reg_tmp yrs);
    let (d, zfrs) = 
      List.fold_left
	(fun (d, zfrs) z -> (d + 1, (z, fregs.(d)) :: zfrs))
	(0, []) zs in
      List.iter
        (fun (z, fr) -> emit_inst (Inst.fmov (freg_of_string z) (freg_of_string fr)))
	(shuffle freg_tmp zfrs)

let h oc { name = Id.L(x); args = _; fargs = _; body = e; ret = _ } =
  (* Printf.fprintf oc "%s:\n" x; *)
  emit_inst (Label x);
  stackset := S.empty;
  stackmap := [];
  set_sp 0;
  g oc (Tail, e)

let g_vardef_body oc { vname = (Id.L x, ty); vbody = e } =
  let gl_name = "min_caml_" ^ x in
  emit_inst (Label (x ^ ".init"));
  stackset := S.empty;
  stackmap := [];
  g oc (NonTail "%R0", e);
  emit_inst (Inst.Mov (rtmp, gl_name));
  emit_inst (Stl (Reg 0, 0, rtmp));
  return ();
  emit_inst (Label gl_name);
  emit_inst (Lda (Reg 31, 0, Reg 31))

let f oc asmlib (Prog(vardefs, fundefs, e)) =
  Format.eprintf "generating assembly...@.";
  emit_insts (li32 !reg_sp_start rsp);
  emit_insts (li32 !reg_hp_start rhp);
  emit_inst (Inst.Comment "main program start");
  stackset := S.empty;
  stackmap := [];
  List.iter (fun { vname = (Id.L x, _); _ } -> emit_inst (Bsr (rlr, x ^ ".init")))
    vardefs;
  g oc (NonTail("%R0"), e);
  emit_inst (Inst.Comment "main program end");
  emit_inst (Br (rtmp, "min_caml_main_end"));
  List.iter (h oc) fundefs;
  List.iter (g_vardef_body oc) vardefs;
  emit_inst (ExtFile asmlib);
  emit_inst (Label "min_caml_main_end");
  emit_inst (Br (Reg 31, "min_caml_main_end"));
  emit oc insts;

