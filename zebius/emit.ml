open Asm

(* NOTE: This code assumes that R14,R13,R12 are temporary registers. *)

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
let offset x = let l = locate x in if l = [] then failwith ("offset of " ^ x ^ " is not defined: stackmap = " ^ List.fold_left (fun x y -> x ^ " " ^ y) "" !stackmap) else 4 * List.hd l (* TODO ad-hoc modification, should be fixed  FIXME *)
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

let load_disp_float oc n src dest = 
  if n <> 0 then Printf.fprintf oc "\tADD\t#%d, %s\n" n src;
  Printf.fprintf oc "\tFMOV.S\t@%s, %s\n" src dest;
  if n <> 0 then Printf.fprintf oc "\tADD\t#%d, %s\n" (-n) src
let store_disp_float oc n src dest = 
  if n <> 0 then Printf.fprintf oc "\tADD\t#%d, %s\n" n dest;
  Printf.fprintf oc "\tFMOV.S\t%s, @%s\n" src dest;
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

let mov_label_float oc (label : string) r = 
  let uniq= Id.genid ".imm_addr" in
  let endpoint = Id.genid ".imm_endp" in
  Printf.fprintf oc "\tMOV.L\t%s, R14\n" uniq;
  Printf.fprintf oc "\tLDS\tR14, FPUL\n";
  Printf.fprintf oc "\tFSTS\tFPUL, %s\n" r;
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

let mov_float oc f r = 
    mov_label_float oc (Printf.sprintf "#%s" (Int32.to_string (Int32.bits_of_float f))) r;
    Printf.fprintf oc "\t; :float = %f\n" f
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
  | NonTail(x), SetF(f) -> mov_float oc f x
  | NonTail(x), SetL(Id.L(y)) -> mov_label oc y x
  | NonTail(x), Mov(y) ->
      if x <> y then mov_labelref_or_reg oc y x
  | NonTail(x), Neg(y) ->
      if x <> y then mov_labelref_or_reg oc y x;
      Printf.fprintf oc "\tNEG\t%s\n" x
  | NonTail(x), Add(y, z') ->
      if V(x) = z' then
	add_id_or_imm oc (V y) x
      else
	(if x <> y then mov_labelref_or_reg oc y x;
	 	add_id_or_imm oc z' x)
  | NonTail(x), Sub(y, z') ->
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
       Printf.fprintf oc "\tMOV\t#-1, R14\n";
       Printf.fprintf oc "\tSHLD\tR14, %s" x
     end else
       failwith ("invalid div imm: " ^ show_ii z)
  | NonTail(x), Ld(y) -> Printf.fprintf oc "\tMOV.L\t@%s, %s\n" y x
  | NonTail(_), St(x, y) -> Printf.fprintf oc "\tMOV.L\t%s, @%s\n" x y
  | NonTail(x), FMovD(y) ->
      if x <> y then Printf.fprintf oc "\tFMOV\t%s, %s\n" y x
  | NonTail(x), FNegD(y) ->
      if x <> y then Printf.fprintf oc "\tFMOV\t%s, %s\n" y x;
      Printf.fprintf oc "\tFNEG\t%s\n" x
  | NonTail(x), FAddD(y, z) ->
      if x = z then
        Printf.fprintf oc "\tFADD\t%s, %s\n" y x
      else
        (if x <> y then Printf.fprintf oc "\tFMOV\t%s, %s\n" y x;
	 Printf.fprintf oc "\tFADD\t%s, %s\n" z x)
  | NonTail(x), FSubD(y, z) ->
      if x = z then (* [XXX] ugly *)
	let ss = stacksize () in
	Printf.fprintf oc "\tFMOV\t%s, FR14\n" z;
	if x <> y then Printf.fprintf oc "\tFMOV\t%s, %s\n" y x;
	Printf.fprintf oc "\tFSUB\tFR14, %s\n"  x
      else
	(if x <> y then Printf.fprintf oc "\tFMOV\t%s, %s\n" y x;
	 Printf.fprintf oc "\tFSUB\t%s, %s\n" z x)
  | NonTail(x), FMulD(y, z) ->
      if x = z then
        Printf.fprintf oc "\tFMUL\t%s, %s\n" y x
      else
        (if x <> y then Printf.fprintf oc "\tFMOV\t%s, %s\n" y x;
	 Printf.fprintf oc "\tFMUL\t%s, %s\n" z x)
  | NonTail(x), FDivD(y, z) ->
      if x = z then (* [XXX] ugly *)
	let ss = stacksize () in
	Printf.fprintf oc "\tFMOV\t%s, FR14\n" y;
	if x <> y then Printf.fprintf oc "\tFMOV\t%s, %s\n" y x;
	Printf.fprintf oc "\tFDIV\tR14, %s\n" x
      else
	(if x <> y then Printf.fprintf oc "\tFMOV\t%s, %s\n" y x;
	 Printf.fprintf oc "\tdivsd\t%s, %s\n" z x)
  | NonTail(x), LdF(y) -> Printf.fprintf oc "\tFMOV.S\t@%s, %s\n" y x
  | NonTail(_), StF(x, y) -> Printf.fprintf oc "\tFMOV.S\t%s, @%s\n" x y
  | NonTail(_), Comment(s) -> Printf.fprintf oc "\t; %s\n" s
  (* 退避の仮想命令の実装 (caml2html: emit_save) *)
  | NonTail(_), Save(x, y) when List.mem x allregs && not (S.mem y !stackset) ->
      save y;
      store_disp oc (offset y) x reg_sp
  | NonTail(_), Save(x, y) when List.mem x allfregs && not (S.mem y !stackset) ->
      savef y;
      store_disp_float oc (offset y) x reg_sp
      (* Printf.fprintf oc "\tFMOV\t%s, %d(%s)\n" x (offset y) reg_sp *)
  | NonTail(_), Save(x, y) -> assert (S.mem y !stackset); ()
  (* 復帰の仮想命令の実装 (caml2html: emit_restore) *)
  | NonTail(x), Restore(y) when List.mem x allregs ->
      load_disp oc (offset y) reg_sp x
  | NonTail(x), Restore(y) ->
      assert (List.mem x allfregs);
      load_disp_float oc (offset y) reg_sp x
  (* 末尾だったら計算結果を第一レジスタにセットしてret (caml2html: emit_tailret) *)
  | Tail, (Nop | St _ | StF _ | Comment _ | Save _ as exp) ->
      g' oc (NonTail(Id.gentmp Type.Unit), exp);
      rts oc
  | Tail, (Set _ | SetL _ | SetF _ | Mov _ | Neg _ | Add _ | Sub _ | Arith _ | Ld _ as exp) ->
      g' oc (NonTail(regs.(0)), exp);
      rts oc
  | Tail, (FMovD _ | FNegD _ | FAddD _ | FSubD _ | FMulD _ | FDivD _ | LdF _  as exp) ->
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

(* TODO type is ignored, and this doesn't work correctly unless ty = int, bool, float. *)
let emit_var oc { vname = Id.L x; vtype = ty; vbody = exp } =
  Printf.fprintf oc ".%s_init\n" x;
  stackset := S.empty;
  stackmap := [];
  Printf.fprintf oc "\tSTS\tPR, R14\n"; 
  Printf.fprintf oc "\tMOV.L\tR14, @R15\n"; 
  Printf.fprintf oc "\tADD\t#4, R15\n"; (* room for return address *)
  g oc (NonTail (regs.(0)), exp);
  mov_label oc ("min_caml_" ^ x) "R14";
  Printf.fprintf oc "\tMOV.L\tR0, @R14\n";
  rts oc;
  Printf.fprintf oc "\t.align\n";
  Printf.fprintf oc "min_caml_%s\n" x;
  Printf.fprintf oc "\t.data.l\t#314159265\n"

(* vardefs are currently ignored *)
let f oc lib (Prog(data, vardefs, fundefs, e)) =
  Format.eprintf "generating assembly...@.";
  Printf.fprintf oc "\tMOV\t#1, R15\n";
  Printf.fprintf oc "\tMOV\t#15, R14\n";
  Printf.fprintf oc "\tSHLD\tR14, R15\n";
  List.iter (fun { vname = Id.L x; vtype; vbody } ->
    call oc ("." ^ x ^ "_init")) vardefs;
  g oc (NonTail(regs.(0)), e);
  Printf.fprintf oc "\tBRA\t.end\n";
  List.iter (fun fundef -> h oc fundef) fundefs;
  List.iter (emit_var oc) vardefs;
  stackset := S.empty;
  stackmap := [];
  let ic = open_in lib in
  begin try
    while true do
      let line = input_line ic in
      Printf.fprintf oc "%s\n" line;
    done
  with  | End_of_file ->  close_in ic
        | e ->
    close_in_noerr ic;
    raise e
  end;
  Printf.fprintf oc ".end\n";
  Printf.fprintf oc "\tAND R0, R0\n"

