open Asm

(* NOTE: This code assumes that R14,R13,R12 are temporary registers. *)

external gethi : float -> int32 = "gethi"
external getlo : float -> int32 = "getlo"

let is_reg_g str = str.[0] = 'R'

let stackset = ref S.empty (* すでにSaveされた変数の集合 (caml2html: emit_stackset) *)
let stackmap = ref [] (* Saveされた変数の、スタックにおける位置 (caml2html: emit_stackmap) *)
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
let stacksize () = align (List.length !stackmap * 4)

let pp_id_or_imm = function
  | V(x) -> x
  | C(i) -> "#" ^ string_of_int i

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

let load_disp oc n src dest = 
  if n <> 0 then Printf.fprintf oc "\tADD\t#%d, %s\n" n src;
  Printf.fprintf oc "\tMOV.L\t@%s, %s\n" src dest;
  if n <> 0 then Printf.fprintf oc "\tADD\t#%d, %s\n" (-n) src
let store_disp oc n src dest = 
  if n <> 0 then Printf.fprintf oc "\tADD\t#%d, %s\n" n dest;
  Printf.fprintf oc "\tMOV.L\t%s, @%s\n" src dest;
  if n <> 0 then Printf.fprintf oc "\tADD\t#%d, %s\n" (-n) dest

let nop oc = 
  Printf.fprintf oc "\tAND\tR0, R0\n"

let call oc sr =
  let uniq_label = Id.genid ".call_addr" in
  let endpoint = Id.genid ".call_endp" in
  Printf.fprintf oc "\tMOV.L\t%s, R14\n" uniq_label;
  Printf.fprintf oc "\tJSR\t@R14\n";
  nop oc;
  Printf.fprintf oc "\tBRA\t%s\n" endpoint;
  nop oc;
  Printf.fprintf oc "\t.align\n";
  Printf.fprintf oc "%s\n" uniq_label;
  Printf.fprintf oc "\t.data.l\t%s\n" sr;
  Printf.fprintf oc "%s\n" endpoint
let jmp oc sr =
  let uniq_label = Id.genid ".call_addr" in
  Printf.fprintf oc "\tMOV.L\t%s, R14\n" uniq_label;
  Printf.fprintf oc "\tJMP\t@R14\n";
  nop oc;
  Printf.fprintf oc "\t.align\n";
  Printf.fprintf oc "%s\n" uniq_label;
  Printf.fprintf oc "\t.data.l\t%s\n" sr
let rts oc = 
  Printf.fprintf oc "\tADD\t#-4, R15\n";
  Printf.fprintf oc "\tMOV.L\t@R15, R14\n";
  Printf.fprintf oc "\tJMP\t@R14\n";
  nop oc
let mov_label oc (label : string) r = 
  let uniq= Id.genid ".imm_addr" in
  let endpoint = Id.genid ".imm_endp" in
  Printf.fprintf oc "\tMOV.L\t%s, %s\n" uniq r;
  Printf.fprintf oc "\tBRA\t%s\n" endpoint;
  nop oc;
  Printf.fprintf oc "\t.align\n";
  Printf.fprintf oc "%s\n" uniq;
  Printf.fprintf oc "\t.data.l\t%s\n" label;
  Printf.fprintf oc "%s\n" endpoint

let mov_imm oc imm r =
  if -128 <= imm && imm <= 127 then
    Printf.fprintf oc "\tMOV\t#%d, %s\n" imm r
  else
    mov_label oc (Printf.sprintf "#%d" imm) r
let cmp_imm oc asmstr imm r =
  mov_imm oc imm "R14";
  Printf.fprintf oc "\t%s\tR14, %s\n" asmstr r
let cmp_id_or_imm oc ii r = match ii with
  | V reg -> Printf.fprintf oc "\tCMP\t%s, %s\n" reg r
  | C imm -> cmp_imm oc "***" imm r

let cmp_eq oc src r = 
  Printf.fprintf oc "\tCMP/EQ\t%s, %s\n" src r
let cmp_le oc src r =
  Printf.fprintf oc "\tCMP/GT\t%s, %s\n" src r


let sub_id oc src r = 
  Printf.fprintf oc "\tSUB\t%s, %s\n" src r
let add_imm oc imm dest =
  if is_reg_g dest then
    Printf.fprintf oc "\tADD\t#%d, %s\n" imm dest
  else begin
    mov_label oc dest "R14";
    Printf.fprintf oc "\tMOV.L\t@R14, R13\n";
    Printf.fprintf oc "\tADD\t#%d, R13\n" imm;
    Printf.fprintf oc "\tMOV.L\tR13, @R14\n"
  end
let add_id oc src dest = 
  if is_reg_g dest then begin
    if is_reg_g src then
      Printf.fprintf oc "\tADD\t%s, %s\n" src dest
    else begin
      Printf.fprintf oc "\tMOV.L\t%s, R14" src;
      Printf.fprintf oc "\tADD\tR14, %s\n" dest
      end
    end
  else
    if is_reg_g src then begin
      mov_label oc dest "R14";
      Printf.fprintf oc "\tMOV.L\t@R14, R13\n";
      Printf.fprintf oc "\tADD\t%s, R13\n" src;
      Printf.fprintf oc "\tMOV.L\tR13, @R14\n"
      end
    else begin
      Printf.fprintf oc "\tMOV.L\t%s, R12" src;
      mov_label oc dest "R14";
      Printf.fprintf oc "\tMOV.L\t@R14, R13\n";
      Printf.fprintf oc "\tADD\tR12, R13\n";
      Printf.fprintf oc "\tMOV.L\tR13, @R14\n"
    end
let add_id_or_imm oc ii dest = 
  match ii with
    | V reg -> add_id oc reg dest
    | C imm -> add_imm oc imm dest

let mov_labelref_or_reg oc (lr : string) r =
  if is_reg_g lr then
    Printf.fprintf oc "\tMOV\t%s, %s\n" lr r
  else
    Printf.fprintf oc "\tMOV.L\t%s, %s\n" lr r
type dest = Tail | NonTail of Id.t (* 末尾かどうかを表すデータ型 (caml2html: emit_dest) *)
let rec g oc = function (* 命令列のアセンブリ生成 (caml2html: emit_g) *)
  | dest, Ans(exp) -> g' oc (dest, exp)
  | dest, Let((x, t), exp, e) ->
      g' oc (NonTail(x), exp);
      g oc (dest, e)
and g' oc = function (* 各命令のアセンブリ生成 (caml2html: emit_gprime) *)
  (* 末尾でなかったら計算結果をdestにセット (caml2html: emit_nontail) *)
  | NonTail(_), Nop -> ()
  | NonTail(x), Set(i) -> mov_imm oc i x
  | NonTail(x), SetL(Id.L(y)) -> mov_label oc y x
  | NonTail(x), Mov(y) ->
      if x <> y then mov_labelref_or_reg oc y x
  | NonTail(x), Neg(y) ->
      if x <> y then mov_labelref_or_reg oc y x;
      Printf.fprintf oc "\tnegl\t%s\n" x
  | NonTail(x), Add(y, z') ->
      if V(x) = z' then
	add_id_or_imm oc (V y) x
      else
	(if x <> y then mov_labelref_or_reg oc y x;
	 	add_id_or_imm oc z' x)
  | NonTail(x), Sub(y, z') ->
	(if x <> y then mov_labelref_or_reg oc y x;
	 sub_id oc z' x)
  | NonTail(x), Ld(y, V(z), i) -> Printf.fprintf oc "\tMOV\t(%s,%s,%d), %s\n" y z i x
  | NonTail(x), Ld(y, C(j), i) -> load_disp oc (j * i) y x
  | NonTail(_), St(x, y, V(z), i) -> Printf.fprintf oc "\tMOV\t%s, (%s,%s,%d)\n" x y z i
  | NonTail(_), St(x, y, C(j), i) -> store_disp oc (j * i) x y
  | NonTail(x), FMovD(y) ->
      if x <> y then Printf.fprintf oc "\tFMOV\t%s, %s\n" y x
  | NonTail(x), FNegD(y) ->
      if x <> y then Printf.fprintf oc "\tFMOV\t%s, %s\n" y x;
      Printf.fprintf oc "\txorpd\tmin_caml_fnegd, %s\n" x
  | NonTail(x), FAddD(y, z) ->
      if x = z then
        Printf.fprintf oc "\taddsd\t%s, %s\n" y x
      else
        (if x <> y then Printf.fprintf oc "\tFMOV\t%s, %s\n" y x;
	 Printf.fprintf oc "\taddsd\t%s, %s\n" z x)
  | NonTail(x), FSubD(y, z) ->
      if x = z then (* [XXX] ugly *)
	let ss = stacksize () in
	Printf.fprintf oc "\tFMOV\t%s, %d(%s)\n" z ss reg_sp;
	if x <> y then Printf.fprintf oc "\tFMOV\t%s, %s\n" y x;
	Printf.fprintf oc "\tsubsd\t%d(%s), %s\n" ss reg_sp x
      else
	(if x <> y then Printf.fprintf oc "\tFMOV\t%s, %s\n" y x;
	 Printf.fprintf oc "\tsubsd\t%s, %s\n" z x)
  | NonTail(x), FMulD(y, z) ->
      if x = z then
        Printf.fprintf oc "\tmulsd\t%s, %s\n" y x
      else
        (if x <> y then Printf.fprintf oc "\tFMOV\t%s, %s\n" y x;
	 Printf.fprintf oc "\tmulsd\t%s, %s\n" z x)
  | NonTail(x), FDivD(y, z) ->
      if x = z then (* [XXX] ugly *)
	let ss = stacksize () in
	Printf.fprintf oc "\tFMOV\t%s, %d(%s)\n" z ss reg_sp;
	if x <> y then Printf.fprintf oc "\tFMOV\t%s, %s\n" y x;
	Printf.fprintf oc "\tdivsd\t%d(%s), %s\n" ss reg_sp x
      else
	(if x <> y then Printf.fprintf oc "\tFMOV\t%s, %s\n" y x;
	 Printf.fprintf oc "\tdivsd\t%s, %s\n" z x)
  | NonTail(x), LdDF(y, V(z), i) -> Printf.fprintf oc "\tFMOV\t(%s,%s,%d), %s\n" y z i x
  | NonTail(x), LdDF(y, C(j), i) -> Printf.fprintf oc "\tFMOV\t%d(%s), %s\n" (j * i) y x
  | NonTail(_), StDF(x, y, V(z), i) -> Printf.fprintf oc "\tFMOV\t%s, (%s,%s,%d)\n" x y z i
  | NonTail(_), StDF(x, y, C(j), i) -> Printf.fprintf oc "\tFMOV\t%s, %d(%s)\n" x (j * i) y
  | NonTail(_), Comment(s) -> Printf.fprintf oc "\t# %s\n" s
  (* 退避の仮想命令の実装 (caml2html: emit_save) *)
  | NonTail(_), Save(x, y) when List.mem x allregs && not (S.mem y !stackset) ->
      save y;
      store_disp oc (offset y) x reg_sp
  | NonTail(_), Save(x, y) when List.mem x allfregs && not (S.mem y !stackset) ->
      savef y;
      Printf.fprintf oc "\tFMOV\t%s, %d(%s)\n" x (offset y) reg_sp
  | NonTail(_), Save(x, y) -> assert (S.mem y !stackset); ()
  (* 復帰の仮想命令の実装 (caml2html: emit_restore) *)
  | NonTail(x), Restore(y) when List.mem x allregs ->
      load_disp oc (offset y) reg_sp x
  | NonTail(x), Restore(y) ->
      assert (List.mem x allfregs);
      Printf.fprintf oc "\tFMOV\t%d(%s), %s\n" (offset y) reg_sp x
  (* 末尾だったら計算結果を第一レジスタにセットしてret (caml2html: emit_tailret) *)
  | Tail, (Nop | St _ | StDF _ | Comment _ | Save _ as exp) ->
      g' oc (NonTail(Id.gentmp Type.Unit), exp);
      rts oc
  | Tail, (Set _ | SetL _ | Mov _ | Neg _ | Add _ | Sub _ | Ld _ as exp) ->
      g' oc (NonTail(regs.(0)), exp);
      rts oc
  | Tail, (FMovD _ | FNegD _ | FAddD _ | FSubD _ | FMulD _ | FDivD _ | LdDF _  as exp) ->
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
      g'_tail_if oc e1 e2 ".JE" "BF"
  | Tail, IfLE(x, y', e1, e2) ->
      cmp_le oc y' x;
      g'_tail_if oc e1 e2 ".JLE" "BT"
  | Tail, IfFEq(x, y, e1, e2) ->
      Printf.fprintf oc "\tcomisd\t%s, %s\n" y x;
      g'_tail_if oc e1 e2 "je" "jne"
  | Tail, IfFLE(x, y, e1, e2) ->
      Printf.fprintf oc "\tcomisd\t%s, %s\n" y x;
      g'_tail_if oc e1 e2 "jbe" "ja"
  | NonTail(z), IfEq(x, y', e1, e2) ->
      cmp_eq oc y' x;
      g'_non_tail_if oc (NonTail(z)) e1 e2 ".je" "BF"
  | NonTail(z), IfLE(x, y', e1, e2) ->
      cmp_le oc y' x;
      g'_non_tail_if oc (NonTail(z)) e1 e2 ".jle" "BT"
  | NonTail(z), IfFEq(x, y, e1, e2) ->
      Printf.fprintf oc "\tcomisd\t%s, %s\n" y x;
      g'_non_tail_if oc (NonTail(z)) e1 e2 "je" "jne"
  | NonTail(z), IfFLE(x, y, e1, e2) ->
      Printf.fprintf oc "\tcomisd\t%s, %s\n" y x;
      g'_non_tail_if oc (NonTail(z)) e1 e2 "jbe" "ja"
  (* 関数呼び出しの仮想命令の実装 (caml2html: emit_call) *)
  | Tail, CallCls(x, ys, zs) -> (* 末尾呼び出し (caml2html: emit_tailcall) *)
      g'_args oc [(x, reg_cl)] ys zs;
      Printf.fprintf oc "\tjmp\t*(%s)\n" reg_cl;
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
      Printf.fprintf oc "\tMOV.L\t@%s, R14\n" reg_cl;
      Printf.fprintf oc "\tJSR\t@R14\n";
      nop oc;
      if ss > 0 then add_imm oc (-ss) reg_sp;
      if List.mem a allregs && a <> regs.(0) then
        Printf.fprintf oc "\tMOV\t%s, %s\n" regs.(0) a
      else if List.mem a allfregs && a <> fregs.(0) then
        Printf.fprintf oc "\tFMOV\t%s, %s\n" fregs.(0) a
  | NonTail(a), CallDir(Id.L(x), ys, zs) ->
      g'_args oc [] ys zs;
      let ss = stacksize () in
      if ss > 0 then add_imm oc ss reg_sp;
      call oc x;
      if ss > 0 then add_imm oc (-ss) reg_sp;
      if List.mem a allregs && a <> regs.(0) then
        Printf.fprintf oc "\tMOV\t%s, %s\n" regs.(0) a
      else if List.mem a allfregs && a <> fregs.(0) then
        Printf.fprintf oc "\tFMOV\t%s, %s\n" fregs.(0) a
and g'_tail_if oc e1 e2 b bn =
  let b_else = Id.genid (b ^ "_else") in
  Printf.fprintf oc "\t%s\t%s\n" bn b_else;
  let stackset_back = !stackset in
  g oc (Tail, e1);
  Printf.fprintf oc "%s\n" b_else;
  stackset := stackset_back;
  g oc (Tail, e2)
and g'_non_tail_if oc dest e1 e2 b bn =
  let b_else = Id.genid (b ^ "_else") in
  let b_cont = Id.genid (b ^ "_cont") in
  Printf.fprintf oc "\t%s\t%s\n" bn b_else;
  let stackset_back = !stackset in
  g oc (dest, e1);
  let stackset1 = !stackset in
  Printf.fprintf oc "\tjmp\t%s\n" b_cont;
  Printf.fprintf oc "%s\n" b_else;
  stackset := stackset_back;
  g oc (dest, e2);
  Printf.fprintf oc "%s\n" b_cont;
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
       load_disp oc (stacksize ()) reg_sp r
     else if r = sw then
       store_disp oc (stacksize ()) y reg_sp
     else
       Printf.fprintf oc "\tMOV\t%s, %s\n" y r)
    (shuffle sw yrs);
  let (d, zfrs) =
    List.fold_left
      (fun (d, zfrs) z -> (d + 1, (z, fregs.(d)) :: zfrs))
      (0, [])
      zs in
  List.iter
    (fun (z, fr) -> Printf.fprintf oc "\tFMOV\t%s, %s\n" z fr)
    (shuffle sw zfrs)

let h oc { name = Id.L(x); args = _; fargs = _; body = e; ret = _ } =
  Printf.fprintf oc "%s\n" x;
  stackset := S.empty;
  stackmap := [];
  Printf.fprintf oc "\tSTS\tPR, R14\n"; 
  Printf.fprintf oc "\tMOV.L\tR14, @R15\n"; 
  Printf.fprintf oc "\tADD\t#4, R15\n"; (* room for return address *)
  g oc (Tail, e)

let f oc (Prog(data, fundefs, e)) =
  Format.eprintf "generating assembly...@.";
  Printf.fprintf oc "\tMOV #1, R15\n";
  Printf.fprintf oc "\tMOV #15, R14\n";
  Printf.fprintf oc "\tSHLD R14, R15\n";
  g oc (NonTail(regs.(0)), e);
  Printf.fprintf oc "\tBRA\t.end\n";
  List.iter (fun fundef -> h oc fundef) fundefs;
  stackset := S.empty;
  stackmap := [];
  Printf.fprintf oc "min_caml_print_int\n"; (* dummy print routine. it does nothing. *)
  Printf.fprintf oc "\tRTS\n"; (* return *)
  nop oc;
  Printf.fprintf oc "min_caml_hp\n";
  Printf.fprintf oc "\t.data.l\t#65536\n";
  Printf.fprintf oc ".end\n";
  Printf.fprintf oc "\tAND R0, R0\n"

