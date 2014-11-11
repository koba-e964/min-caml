open Asm;;
open Inst;;

(* NOTE: This code assumes that R14 is temporary register. *)

let stackset = ref S.empty (* すでにSaveされた変数の集合 (caml2html: emit_stackset) *)
let stackmap = ref [] (* Saveされた変数の、スタックにおける位置 (caml2html: emit_stackmap) *)
let save x =
  stackset := S.add x !stackset;
  if not (List.mem x !stackmap) then
    stackmap := !stackmap @ [x]
let savef x =
  stackset := S.add x !stackset;
  if not (List.mem x !stackmap) then
    stackmap := !stackmap @ [x] (* float is 4-byte *)
let locate x =
  let rec loc = function
    | [] -> []
    | y :: zs when x = y -> 0 :: List.map succ (loc zs)
    | y :: zs -> List.map succ (loc zs) in
  loc !stackmap
let offset x = let l = locate x in if l = [] then failwith ("offset of " ^ x ^ " is not defined: stackmap = " ^ List.fold_left (fun x y -> x ^ " " ^ y) "" !stackmap) else 4 * List.hd l (* TODO ad-hoc modification, should be fixed  FIXME *)
let stacksize () = List.length !stackmap * 4

let insts = Queue.create ()

let emit_inst (inst : zebius_inst) = Queue.add inst insts

(* 関数呼び出しのために引数を並べ替える(register shuffling) (caml2html: emit_shuffle) *)
let rec shuffle sw xys =
  (* remove identical moves *)
  let _, xys = List.partition (fun (x, y) -> x = y) xys in
  (* find acyclic moves *)
  match List.partition (fun (_, y) -> List.mem_assoc y xys) xys with
  | [], [] -> []
  | (x, y) :: xys, [] -> (* no acyclic moves; resolve a cyclic move *)
      (y, sw) :: (x, y) :: shuffle sw (List.map
					 (function
					   | (y', z) when y = y' -> (sw, z)
					   | yz -> yz)
					 xys)
  | xys, acyc -> acyc @ shuffle sw xys

let nop oc = emit_inst (And (Reg 0, Reg 0))

let mov_label oc (label : string) r = 
  let uniq= Id.genid ".imm_addr" in
  let endpoint = Id.genid ".imm_endp" in
  emit_inst (MovPc (uniq, reg_of_string r));
  emit_inst (Bra endpoint);
  emit_inst Align;
  emit_inst (Label uniq);
  emit_inst (DataL label);
  emit_inst (Label endpoint)

let mov_label_float oc (label : string) r = 
  let uniq= Id.genid ".imm_addr" in
  let endpoint = Id.genid ".imm_endp" in
  emit_inst (MovPc (uniq, Reg 14));
  emit_inst (LdsFpul (Reg 14));
  emit_inst (FstsFpul (freg_of_string r));
  emit_inst (Bra endpoint);
  emit_inst Align;
  emit_inst (Label uniq);
  emit_inst (DataL label);
  emit_inst (Label endpoint)

let add_imm oc imm dest =
  if -256 <= imm && imm <= 254 then begin
    let r = reg_of_string dest in
    if -128 <= imm && imm <= 127 then
      emit_inst (AddI (imm, r))
    else if imm >= 128 then begin
      emit_inst (AddI (127, r));
      emit_inst (AddI (imm - 127, r))
    end else begin
      emit_inst (AddI (-128, r));
      emit_inst (AddI (imm + 128, r))
    end
  end else begin
    mov_label oc (Printf.sprintf "#%d" imm) "R14";
    emit_inst (AddR (Reg 14, reg_of_string dest))
  end
let load_disp oc n src dest = 
  if n <> 0 then add_imm oc n src;
  emit_inst (Load (reg_of_string src, reg_of_string dest));
  if n <> 0 then add_imm oc (-n) src
let store_disp oc n src dest = 
  if n <> 0 then add_imm oc n dest;
  emit_inst (Store (reg_of_string src, reg_of_string dest));
  if n <> 0 then add_imm oc (-n) dest

let load_disp_float oc n src dest = 
  if n <> 0 then add_imm oc n src;
  emit_inst (FLoad (reg_of_string src, freg_of_string dest));
  if n <> 0 then add_imm oc (-n) src
let store_disp_float oc n src dest = 
  if n <> 0 then add_imm oc n dest;
  emit_inst (FStore (freg_of_string src, reg_of_string dest));
  if n <> 0 then add_imm oc (-n) dest

let call oc sr =
  let uniq_label = Id.genid ".call_addr" in
  let endpoint = Id.genid ".call_endp" in
  emit_inst (MovPc (uniq_label, Reg 14));
  emit_inst (Jsr (Reg 14));
  emit_inst (Bra endpoint);
  emit_inst Align;
  emit_inst (Label uniq_label);
  emit_inst (DataL sr);
  emit_inst (Label endpoint)
let jmp oc sr =
  let uniq_label = Id.genid ".call_addr" in
  emit_inst (MovPc (uniq_label, Reg 14));
  emit_inst (Jmp (Reg 14));
  emit_inst Align;
  emit_inst (Label uniq_label);
  emit_inst (DataL sr)
let rts oc = 
  emit_inst (AddI (-4, Reg 15));
  emit_inst (Load (Reg 15, Reg 14));
  emit_inst (Jmp (Reg 14))
let mov_imm oc imm r =
  if Int32.of_int (-256) <= imm && imm <= Int32.of_int 254 then begin
    let i_imm = Int32.to_int imm in
    if -128 <= i_imm && i_imm <= 127 then
      emit_inst (MovI (i_imm, reg_of_string r))
    else if i_imm >= 128 then begin
      emit_inst (MovI (127, reg_of_string r));
      emit_inst (AddI (i_imm - 127, reg_of_string r))
    end else begin
      emit_inst (MovI (-128, reg_of_string r));
      emit_inst (AddI (i_imm + 128, reg_of_string r))
    end
  end else
    mov_label oc ("#" ^ Int32.to_string imm) r

let cmp_eq oc src r = emit_inst (CmpEq (reg_of_string src, reg_of_string r))
let cmp_le oc src r = emit_inst (CmpGt (reg_of_string src, reg_of_string r))

let sub_id oc src r = emit_inst (Inst.Sub (reg_of_string src, reg_of_string r))
let add_id oc src dest = emit_inst (AddR (reg_of_string src, reg_of_string dest))
let add_id_or_imm oc ii dest = 
  match ii with
    | V reg -> add_id oc reg dest
    | C imm -> add_imm oc imm dest

let mov_labelref_or_reg oc src dest = emit_inst (mov src dest)

let mov_float oc f r = 
  if f = 0.0 then
    emit_inst (FLdI0 (freg_of_string r))
  else if f = 1.0 then
    emit_inst (FLdI1 (freg_of_string r))
  else if float_of_int (int_of_float f) = f && -256.0 <= f && f <= 254.0 then begin
    mov_imm oc (Int32.of_float f) "R14";
    emit_inst (LdsFpul (Reg 14));
    emit_inst (FloatFpul (freg_of_string r))
  end else begin
    mov_label_float oc (Printf.sprintf "#%s" (Int32.to_string (Int32.bits_of_float f))) r;
    emit_inst (Inst.Comment (Printf.sprintf "\t; :float = %f" f))
  end
type dest = Tail | NonTail of Id.t (* 末尾かどうかを表すデータ型 (caml2html: emit_dest) *)
let rec g oc = function (* 命令列のアセンブリ生成 (caml2html: emit_g) *)
  | dest, Ans(exp) -> g' oc (dest, exp)
  | dest, Let((x, t), exp, e) ->
      g' oc (NonTail(x), exp);
      g oc (dest, e)
and g' oc = function (* 各命令のアセンブリ生成 (caml2html: emit_gprime) *)
  (* 末尾でなかったら計算結果をdestにセット (caml2html: emit_nontail) *)
  | NonTail(_), Nop -> ()
  | NonTail(x), Set(i) -> mov_imm oc (Int32.of_int i) x
  | NonTail(x), SetF(f) -> mov_float oc f x
  | NonTail(x), SetL(Id.L(y)) -> mov_label oc y x
  | NonTail(x), Mov(y) ->
      if x <> y then mov_labelref_or_reg oc y x
  | NonTail(x), Asm.Neg(y) ->
      if x <> y then mov_labelref_or_reg oc y x;
      emit_inst (Inst.Not (reg_of_string x, reg_of_string x));
      emit_inst (AddI (1, reg_of_string x))
  | NonTail(x), Asm.Add(y, z') ->
      if V(x) = z' then
	add_id_or_imm oc (V y) x
      else
	(if x <> y then mov_labelref_or_reg oc y x;
	 	add_id_or_imm oc z' x)
  | NonTail(x), Asm.Sub(y, z') ->
      if x = z' then begin
        sub_id oc y x; (* x - y *)
        emit_inst (Inst.Not (reg_of_string x, reg_of_string x));
        emit_inst (AddI (1, reg_of_string x))
      end else
	(if x <> y then mov_labelref_or_reg oc y x;
	 sub_id oc z' x)
  | NonTail(x), Arith (Syntax.AMul, y, z) ->
     if z = C 2 then (mov_labelref_or_reg oc y x; add_id oc x x)
     else begin
       if z = C 4 then (mov_labelref_or_reg oc y x; add_id oc x x; add_id oc x x)
       else failwith ("invalid mul imm: " ^ show_ii z ^ " " ^ y ^ " *= " ^ show_ii z)
     end
  | NonTail(x), Arith (Syntax.ADiv, y, z) -> (* TODO very *ugly* code, it should be rewritten *)
     if z = C 2 then begin
       mov_labelref_or_reg oc y x;
       emit_inst (MovI (-1, Reg 14));
       emit_inst (Shld (Reg 14, reg_of_string x))
     end else
       failwith ("invalid div imm: " ^ show_ii z)
  | NonTail(x), Ld(y) -> emit_inst (Load (reg_of_string y, reg_of_string x))
  | NonTail(_), St(x, y) -> emit_inst (Store (reg_of_string x, reg_of_string y))
  | NonTail(x), FMovD(y) ->
      if x <> y then emit_inst (fmov y x);
  | NonTail(x), FNegD(y) ->
      if x <> y then emit_inst (fmov y x);
      emit_inst (FNeg (freg_of_string x))
  | NonTail(x), FAddD(y, z) ->
      if x = z then
        emit_inst (FOp (FAdd, freg_of_string y, freg_of_string x))
      else
	(if x <> y then emit_inst (fmov y x);
	 emit_inst (FOp (FAdd, freg_of_string z, freg_of_string x)))
  | NonTail(x), FSubD(y, z) ->
      if x = z then (* [XXX] ugly *) begin
	emit_inst (FOp (FSub, freg_of_string y, freg_of_string x));
        if y <> x then emit_inst (FNeg (freg_of_string x))
      end else
	(if x <> y then emit_inst (fmov y x);
	 emit_inst (FOp (FSub, freg_of_string z, freg_of_string x)))
  | NonTail(x), FMulD(y, z) ->
      if x = z then
        emit_inst (FOp (FMul, freg_of_string y, freg_of_string x))
      else
	(if x <> y then emit_inst (fmov y x);
	 emit_inst (FOp (FMul, freg_of_string z, freg_of_string x)))
  | NonTail(x), FDivD(y, z) ->
      if x = z then (* [XXX] ugly *) begin
        emit_inst (fmov z "FR15");
	if x <> y then emit_inst (fmov y x);
	emit_inst (FOp (FDiv, FReg 15, freg_of_string x))
      end else
	(if x <> y then emit_inst (fmov y x);
	 emit_inst (FOp (FDiv, freg_of_string z, freg_of_string x)))
  | NonTail(x), LdF(y) -> emit_inst (FLoad (reg_of_string y, freg_of_string x))
  | NonTail(_), StF(x, y) -> emit_inst (FStore (freg_of_string x, reg_of_string y))
  | NonTail(_), Asm.Comment(s) -> emit_inst (Inst.Comment s)
  (* 退避の仮想命令の実装 (caml2html: emit_save) *)
  | NonTail(_), Save(x, y) when List.mem x allregs && not (S.mem y !stackset) ->
      save y;
      store_disp oc (offset y) x reg_sp
  | NonTail(_), Save(x, y) when List.mem x allfregs && not (S.mem y !stackset) ->
      savef y;
      store_disp_float oc (offset y) x reg_sp
  | NonTail(_), Save(x, y) -> assert (S.mem y !stackset); ()
  (* 復帰の仮想命令の実装 (caml2html: emit_restore) *)
  | NonTail(x), Restore(y) when List.mem x allregs ->
      load_disp oc (offset y) reg_sp x
  | NonTail(x), Restore(y) ->
      assert (List.mem x allfregs);
      load_disp_float oc (offset y) reg_sp x
  (* 末尾だったら計算結果を第一レジスタにセットしてret (caml2html: emit_tailret) *)
  | Tail, (Nop | St _ | StF _ | Asm.Comment _ | Save _ as exp) ->
      g' oc (NonTail(Id.gentmp Type.Unit), exp);
      rts oc
  | Tail, (Asm.Set _ | Asm.SetL _ | Asm.Mov _ | Asm.Neg _ | Asm.Add _ | Asm.Sub _ | Asm.Arith _ | Asm.Ld _ as exp) ->
      g' oc (NonTail(regs.(0)), exp);
      rts oc
  | Tail, (SetF _ | FMovD _ | FNegD _ | FAddD _ | FSubD _ | FMulD _ | FDivD _ | LdF _  as exp) ->
      g' oc (NonTail(fregs.(0)), exp);
      rts oc
  | Tail, (Restore(x) as exp) ->
      (match locate x with
      | [i] -> g' oc (NonTail(regs.(0)), exp)
      | [i; j] when i + 1 = j -> g' oc (NonTail(fregs.(0)), exp)
      | _ -> assert false);
      rts oc
  | Tail, IfEq(x, y', e1, e2) ->
      cmp_eq oc y' x;
      g'_tail_if oc e1 e2 ".JE" (fun x -> Pseudo (ABC (false, x)))
  | Tail, IfLE(x, y', e1, e2) ->
      cmp_le oc y' x;
      g'_tail_if oc e1 e2 ".JLE" (fun x -> Pseudo (ABC (true, x)))
  | NonTail(z), IfEq(x, y', e1, e2) ->
      cmp_eq oc y' x;
      g'_non_tail_if oc (NonTail(z)) e1 e2 ".je" (fun x -> Pseudo (ABC (false, x)))
  | NonTail(z), IfLE(x, y', e1, e2) ->
      cmp_le oc y' x;
      g'_non_tail_if oc (NonTail(z)) e1 e2 ".jle" (fun x -> Pseudo (ABC (true, x)))
  | Tail, IfFEq(x, y, e1, e2) ->
      emit_inst (FCmpEq (freg_of_string x, freg_of_string y));
      g'_tail_if oc e1 e2 ".JEQ_f" (fun x -> Pseudo (ABC (false, x)))
  | Tail, IfFLE(x, y, e1, e2) ->
      emit_inst (FCmpGt (freg_of_string y, freg_of_string x));
      g'_tail_if oc e1 e2 ".JLE_f" (fun x -> Pseudo (ABC (true, x)))
  | NonTail z, IfFEq(x, y, e1, e2) ->
      emit_inst (FCmpEq (freg_of_string x, freg_of_string y));
      g'_non_tail_if oc (NonTail z) e1 e2 ".jeq_f" (fun x -> Pseudo (ABC (false, x)))
  | NonTail z, IfFLE(x, y, e1, e2) ->
      emit_inst (FCmpGt (freg_of_string y, freg_of_string x));
      g'_non_tail_if oc (NonTail z) e1 e2 ".jle_f" (fun x -> Pseudo (ABC (true, x)))
  (* 関数呼び出しの仮想命令の実装 (caml2html: emit_call) *)
  | Tail, CallCls(x, ys, zs) -> (* 末尾呼び出し (caml2html: emit_tailcall) *)
      g'_args oc [(x, reg_cl)] ys zs;
      let ss = stacksize () in
      if ss > 0 then add_imm oc ss reg_sp;
      emit_inst (Load (reg_of_string reg_cl, Reg 14));
      emit_inst (Jsr (Reg 14));
      if ss > 0 then add_imm oc (-ss) reg_sp;
      rts oc
  | Tail, CallDir(Id.L(x), ys, zs) -> (* 末尾呼び出し *)
      g'_args oc [] ys zs;
      let ss = stacksize () in
      if ss > 0 then add_imm oc ss reg_sp;
      call oc x;
      if ss > 0 then add_imm oc (-ss) reg_sp;
      rts oc
      (* jmp oc x;  *) (* Since tailcall optimization is buggy, we use ordinary call instead. *) 
  | NonTail(a), CallCls(x, ys, zs) ->
      g'_args oc [(x, reg_cl)] ys zs;
      let ss = stacksize () in
      if ss > 0 then add_imm oc ss reg_sp;
      emit_inst (Load (reg_of_string reg_cl, Reg 14));
      emit_inst (Jsr (Reg 14));
      if ss > 0 then add_imm oc (-ss) reg_sp;
      if List.mem a allregs && a <> regs.(0) then
        emit_inst (mov regs.(0) a)
      else if List.mem a allfregs && a <> fregs.(0) then
        emit_inst (fmov fregs.(0) a)
  | NonTail(a), CallDir(Id.L(x), ys, zs) ->
      g'_args oc [] ys zs;
      let ss = stacksize () in
      if ss > 0 then add_imm oc ss reg_sp;
      call oc x;
      if ss > 0 then add_imm oc (-ss) reg_sp;
      if List.mem a allregs && a <> regs.(0) then
        emit_inst (mov regs.(0) a)
      else if List.mem a allfregs && a <> fregs.(0) then
        emit_inst (fmov fregs.(0) a)
and g'_tail_if oc e1 e2 b bn =
  let b_else = Id.genid (b ^ "_else") in
  emit_inst (bn b_else);
  let stackset_back = !stackset in
  g oc (Tail, e1);
  emit_inst (Label b_else);
  stackset := stackset_back;
  g oc (Tail, e2)
and g'_non_tail_if oc dest e1 e2 b bn =
  let b_else = Id.genid (b ^ "_else") in
  let b_cont = Id.genid (b ^ "_cont") in
  emit_inst (bn b_else);
  let stackset_back = !stackset in
  g oc (dest, e1);
  let stackset1 = !stackset in
  emit_inst (Bra b_cont);
  emit_inst (Label b_else);
  stackset := stackset_back;
  g oc (dest, e2);
  emit_inst (Label b_cont);
  let stackset2 = !stackset in
  stackset := S.inter stackset1 stackset2
and g'_args oc x_reg_cl ys zs =
  assert (List.length ys <= Array.length regs - List.length x_reg_cl);
  assert (List.length zs <= Array.length fregs);
  let sw = "(dummy_register)" in
  let (i, yrs) =
    List.fold_left
      (fun (i, yrs) y -> (i + 1, (y, regs.(i)) :: yrs))
      (0, x_reg_cl)
      ys in
  List.iter
    (fun (y, r) -> if y = sw then
       emit_inst (MovR (Reg 14, reg_of_string r))
     else if r = sw then
       emit_inst (MovR (reg_of_string y, Reg 14))
     else
       emit_inst (MovR (reg_of_string y, reg_of_string r));
     emit_inst (Inst.Comment "shuffle-int"))
    (shuffle sw yrs);
  let (d, zfrs) =
    List.fold_left
      (fun (d, zfrs) z -> (d + 1, (z, fregs.(d)) :: zfrs))
      (0, [])
      zs in
  List.iter
    (fun (z, fr) -> if z = sw then
       emit_inst (FMov (FReg 15, freg_of_string fr))
     else if fr = sw then
       emit_inst (FMov (freg_of_string z, FReg 15))
     else
       emit_inst (FMov (freg_of_string z, freg_of_string fr));
     emit_inst (Inst.Comment "shuffle-float"))
    (shuffle sw zfrs)

let h oc { name = Id.L(x); args = _; fargs = _; body = e; ret = _ } =
  emit_inst (Label x);
  stackset := S.empty;
  stackmap := [];
  emit_inst (StsPr (Reg 14));
  emit_inst (Store (Reg 14, Reg 15));
  emit_inst (AddI (4, Reg 15)); (* room for return address *)
  g oc (Tail, e)

(* TODO type is ignored, and this doesn't work correctly unless ty = int, bool, float. *)
let emit_var oc { vname = Id.L x; vtype = ty; vbody = exp } =
  emit_inst (Label ("." ^ x ^ "_init"));
  stackset := S.empty;
  stackmap := [];
  emit_inst (StsPr (Reg 14));
  emit_inst (Store (Reg 14, Reg 15));
  emit_inst (AddI (4, Reg 15)); (* room for return address *)
  g oc (NonTail (regs.(0)), exp);
  mov_label oc ("min_caml_" ^ x) "R14";
  emit_inst (Store (Reg 0, Reg 14));
  rts oc;
  emit_inst Align;
  emit_inst (Label ("min_caml_" ^ x));
  emit_inst (DataI (Int32.of_string "314159265"))

(* vardefs are currently ignored *)
let f oc lib (Prog(data, vardefs, fundefs, e)) =
  Format.eprintf "generating assembly...@.";
  emit_inst (MovI (1, Reg 15));
  emit_inst (MovI (18, Reg 14));
  emit_inst (Shld (Reg 14, Reg 15));
  emit_inst (MovR (Reg 15, Reg 12));
  emit_inst (AddR (Reg 12, Reg 12));
  List.iter (fun { vname = Id.L x; vtype; vbody } ->
    call oc ("." ^ x ^ "_init")) vardefs;
  g oc (NonTail(regs.(0)), e);
  jmp oc ".end";
  List.iter (fun fundef -> h oc fundef) fundefs;
  List.iter (emit_var oc) vardefs;
  stackset := S.empty;
  stackmap := [];
  emit_inst (ExtFile lib);
  emit_inst (Label ".end");
  emit oc insts;
  Printf.fprintf oc "\tAND R0,R0\n"

