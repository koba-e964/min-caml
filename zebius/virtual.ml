(* translation into assembly with infinite number of virtual registers *)

open Asm

let data = ref [] (* 浮動小数点数の定数テーブル (caml2html: virtual_data) *)
let fsqrt = ref false

let classify xts ini addf addi =
  List.fold_left
    (fun acc (x, t) ->
      match t with
      | Type.Unit -> acc
      | Type.Float -> addf acc x
      | Type.Int -> addi acc x t
      | _ -> addi acc x t) (* closures *)
    ini
    xts

let separate xts =
  classify
    xts
    ([], [])
    (fun (int, float) x -> (int, float @ [x]))
    (fun (int, float) x _ -> (int @ [x], float))

let expand xts ini addf addi =
  classify
    xts
    ini
    (fun (offset, acc) x ->
      let offset = align offset in
      (offset + 8, addf x offset acc))
    (fun (offset, acc) x t ->
      (offset + 4, addi x t offset acc))

let st (x, y, z, mul) succ =
  match z with
  | C offset -> 
  let aa = Id.genid "lidx" in
    Let ((aa, Type.Int), Add (y, C (offset * mul)), seq (St (x, aa), succ))
  | V z' ->
  let aa = Id.genid "lidx" in
    let bb = Id.genid "lary" in
      Let ((aa, Type.Int), Arith (Syntax.AMul, z', C mul), Let ((bb, Type.Int), Add (y, V aa), seq (St (x, bb), succ)))
   
let stDF (x, y, z, mul) succ =
  match z with
  | C offset -> 
  let aa = Id.genid "lidx" in
    Let ((aa, Type.Int), Add (y, C(offset * mul)), seq (StF (x, aa), succ))
  | V z' ->
  let aa = Id.genid "lidx" in
    let bb = Id.genid "lary" in
      Let ((aa, Type.Int), Arith (Syntax.AMul, z', C mul), Let ((bb, Type.Int), Add (y, V aa), seq (StF (x, bb), succ)))
   

let rec g env = function (* 式の仮想マシンコード生成 (caml2html: virtual_g) *)
  | Closure.Unit -> Ans(Nop)
  | Closure.Int(i) -> Ans(Set(i))
  | Closure.Float(d) ->
    (*
      let l =
	try
	  (* すでに定数テーブルにあったら再利用 *)
	  let (l, _) = List.find (fun (_, d') -> d = d') !data in
	  l
	with Not_found ->
	  let l = Id.L(Id.genid "l") in
	  data := (l, d) :: !data;
	  l in
      let x = Id.genid "l" in
      Let((x, Type.Int), SetL(l), Ans(LdDF(x, C(0), 1)))
   *)
    Ans (SetF d)
  | Closure.Neg(x) -> Ans(Neg(x))
  | Closure.Add(x, y) -> Ans(Add(x, V(y)))
  | Closure.Sub(x, y) -> Ans(Sub(x, y))
  | Closure.Arith (op, x, y) -> Ans (Arith (op, x, V(y)))
  | Closure.FNeg(x) -> Ans(FNegD(x))
  | Closure.FAdd(x, y) -> Ans(FAddD(x, y))
  | Closure.FSub(x, y) -> Ans(FSubD(x, y))
  | Closure.FMul(x, y) -> Ans(FMulD(x, y))
  | Closure.FDiv(x, y) -> Ans(FDivD(x, y))
  | Closure.IfEq(x, y, e1, e2) ->
      (match M.find x env with
      | Type.Bool | Type.Int -> Ans(IfEq(x, y, g env e1, g env e2))
      | Type.Float -> Ans(IfFEq(x, y, g env e1, g env e2))
      | _ -> failwith "equality supported only for bool, int, and float")
  | Closure.IfLE(x, y, e1, e2) ->
      (match M.find x env with
      | Type.Bool | Type.Int -> Ans(IfLE(x, y, g env e1, g env e2))
      | Type.Float -> Ans(IfFLE(x, y, g env e1, g env e2))
      | _ -> failwith "inequality supported only for bool, int, and float")
  | Closure.Let((x, t1), e1, e2) ->
      let e1' = g env e1 in
      let e2' = g (M.add x t1 env) e2 in
      concat e1' (x, t1) e2'
  | Closure.Var(x) ->
      (match M.find x env with
      | Type.Unit -> Ans(Nop)
      | Type.Float -> Ans(FMovD(x))
      | _ -> Ans(Mov(x)))
  | Closure.MakeCls((x, t), { Closure.entry = l; Closure.actual_fv = ys }, e2) -> (* クロージャの生成 (caml2html: virtual_makecls) *)
      (* Closureのアドレスをセットしてから、自由変数の値をストア *)
      let e2' = g (M.add x t env) e2 in
      let offset, store_fv =
	expand
	  (List.map (fun y -> (y, M.find y env)) ys)
	  (4, e2')
	  (fun y offset store_fv -> stDF (y, x, C(offset), 1) store_fv)
	  (fun y _ offset store_fv -> st (y, x, C(offset), 1) store_fv) in
      Let((x, t), Mov(reg_hp),
	  Let((reg_hp, Type.Int), Add(reg_hp, C(align offset)),
	      let z = Id.genid "l" in
	      Let((z, Type.Int), SetL(l),
		  st (z, x, C(0), 1) store_fv)))
  | Closure.AppCls(x, ys) ->
      let (int, float) = separate (List.map (fun y -> (y, M.find y env)) ys) in
      Ans(CallCls(x, int, float))
  | Closure.AppDir(Id.L(x), (y :: _ as ys)) when x = "min_caml_print_char" && List.length ys = 1 ->
     Ans (ExtOp (PrintChar y))
  | Closure.AppDir(Id.L(x), (y :: _ as ys)) when x = "min_caml_int_of_float" && List.length ys = 1 ->
     Ans (ExtOp (FToI y))
  | Closure.AppDir(Id.L(x), (y :: _ as ys)) when x = "min_caml_float_of_int" && List.length ys = 1 ->
     Ans (ExtOp (IToF y))
  | Closure.AppDir(Id.L(x), (y :: _ as ys)) when x = "min_caml_sqrt" && List.length ys = 1 ->
     if !fsqrt then
       Ans (CallDir (Id.L "min_caml_fsqrt_software", [], [y]))
     else
       Ans (ExtOp (FSqrt y))
  | Closure.AppDir(Id.L(x), ys) ->
      let (int, float) = separate (List.map (fun y -> (y, M.find y env)) ys) in
      Ans(CallDir(Id.L(x), int, float))
  | Closure.Tuple(xs) -> (* 組の生成 (caml2html: virtual_tuple) *)
      let y = Id.genid "t" in
      let (offset, store) =
	expand
	  (List.map (fun x -> (x, M.find x env)) xs)
	  (0, Ans(Mov(y)))
	  (fun x offset store -> stDF(x, y, C(offset), 1) store)
	  (fun x _ offset store -> st(x, y, C(offset), 1) store) in
      Let((y, Type.Tuple(List.map (fun x -> M.find x env) xs)), Mov(reg_hp),
	  Let((reg_hp, Type.Int), Add(reg_hp, C(align offset)),
	      store))
  | Closure.LetTuple(xts, y, e2) ->
      let s = Closure.fv e2 in
      let (offset, load) =
        expand
          xts
          (0, g (M.add_list xts env) e2)
          (fun x offset load ->
            if not (S.mem x s) then load else (* [XX] a little ad hoc optimization *)
            let aa = Id.genid "ltfidx" in
            Let ((aa, Type.Int), Add (y, C offset), fletd(x, LdF aa, load)))
          (fun x t offset load ->
            if not (S.mem x s) then load else (* [XX] a little ad hoc optimization *)
            let aa = Id.genid "ltidx" in
            Let ((aa, Type.Int), Add (y, C offset),
              Let((x, t), Ld aa, load))) in
      load
  | Closure.Get(x, y) -> (* 配列の読み出し (caml2html: virtual_get) *)
      (match M.find x env with
      | Type.Array(Type.Unit) -> Ans(Nop)
      | Type.Array(Type.Float) -> 
        let aa = Id.genid "lfidx" in
        let bb = Id.genid "lfary" in
        Let ((aa, Type.Int), Arith (Syntax.AMul, y, C 4), Let ((bb, Type.Int), Add (x, V aa), Ans (LdF bb)))
      | Type.Array(_) -> 
        let aa = Id.genid "lidx" in
        let bb = Id.genid "lary" in
        Let ((aa, Type.Int), Arith (Syntax.AMul, y, C 4), Let ((bb, Type.Int), Add (x, V aa), Ans (Ld bb)))
      | _ -> assert false)
  | Closure.Put(x, y, z) ->
      (match M.find x env with
      | Type.Array(Type.Unit) -> Ans(Nop)
      | Type.Array(Type.Float) -> stDF(z, x, V(y), 4) (Ans Nop)
      | Type.Array(_) -> st(z, x, V(y), 4) (Ans Nop)
      | _ -> assert false)
  | Closure.ExtArray(Id.L(x)) -> g env (Closure.ExtVar (Id.L x, Type.Array Type.Unit (*stub*)))
  | Closure.ExtVar(Id.L(x), ty) ->
    let uniq = Id.genid "ext_var" in
    Let ((uniq, ty), (SetL (Id.L ("min_caml_" ^ x))), Ans (Ld uniq)) (* TODO this only works if type = int, bool, float *)

(* 関数の仮想マシンコード生成 (caml2html: virtual_h) *)
let h { Closure.name = (Id.L(x), t); Closure.args = yts; Closure.formal_fv = zts; Closure.body = e } =
  let (int, float) = separate yts in
  let (offset, load) =
    expand
      zts
      (4, g (M.add x t (M.add_list yts (M.add_list zts M.empty))) e)
      (fun z offset load -> 
            let aa = Id.genid "clsidx" in
              Let ((aa, Type.Int), Add (reg_cl, C offset), fletd(z, LdF aa, load)))
      (fun z t offset load ->
            let aa = Id.genid "clsidx" in
              Let ((aa, Type.Int), Add (reg_cl, C offset), Let ((z, t), Ld aa, load))) in
  match t with
  | Type.Fun(_, t2) ->
      { name = Id.L(x); args = int; fargs = float; body = load; ret = t2 }
  | _ -> assert false

let generate_var { Closure.vname = (x, ty); Closure.vbody = expr } =
  { vname = x; vtype = ty; vbody = g M.empty expr }
 

(* プログラム全体の仮想マシンコード生成 (caml2html: virtual_f) *)
let f (Closure.Prog(vardefs, fundefs, e)) =
  data := [];
  let vardefs = List.map generate_var vardefs in
  let fundefs = List.map h fundefs in
  let e = g M.empty e in
  Prog(!data, vardefs, fundefs, e)
