type closure = { entry : Id.l; actual_fv : Id.t list }
type t = (* ���������Ѵ���μ� (caml2html: closure_t) *)
  | Unit
  | Int of int
  | Float of float
  | Neg of Id.t
  | Add of Id.t * Id.t
  | Sub of Id.t * Id.t
  | Arith of Syntax.a_op * Id.t * Id.t
  | FNeg of Id.t
  | FAdd of Id.t * Id.t
  | FSub of Id.t * Id.t
  | FMul of Id.t * Id.t
  | FDiv of Id.t * Id.t
  | IfEq of Id.t * Id.t * t * t
  | IfLE of Id.t * Id.t * t * t
  | Let of (Id.t * Type.t) * t * t
  | Var of Id.t
  | MakeCls of (Id.t * Type.t) * closure * t
  | AppCls of Id.t * Id.t list
  | AppDir of Id.l * Id.t list
  | Tuple of Id.t list
  | LetTuple of (Id.t * Type.t) list * Id.t * t
  | Get of Id.t * Id.t
  | Put of Id.t * Id.t * Id.t
  | ExtArray of Id.l
type fundef = { name : Id.l * Type.t;
		args : (Id.t * Type.t) list;
		formal_fv : (Id.t * Type.t) list;
		body : t }
type vardef = { vname : Id.l * Type.t; vbody : t }
type prog = Prog of vardef list * fundef list * t

let rec fv = function
  | Unit | Int(_) | Float(_) | ExtArray(_) -> S.empty
  | Neg(x) | FNeg(x) -> S.singleton x
  | Add(x, y) | Sub(x, y) | Arith (_, x, y) | FAdd(x, y) | FSub(x, y) | FMul(x, y) | FDiv(x, y) | Get(x, y) -> S.of_list [x; y]
  | IfEq(x, y, e1, e2)| IfLE(x, y, e1, e2) -> S.add x (S.add y (S.union (fv e1) (fv e2)))
  | Let((x, t), e1, e2) -> S.union (fv e1) (S.remove x (fv e2))
  | Var(x) -> S.singleton x
  | MakeCls((x, t), { entry = l; actual_fv = ys }, e) -> S.remove x (S.union (S.of_list ys) (fv e))
  | AppCls(x, ys) -> S.of_list (x :: ys)
  | AppDir(_, xs) | Tuple(xs) -> S.of_list xs
  | LetTuple(xts, y, e) -> S.add y (S.diff (fv e) (S.of_list (List.map fst xts)))
  | Put(x, y, z) -> S.of_list [x; y; z]

let toplevel : fundef list ref = ref []

let rec g env known = function (* ���������Ѵ��롼�������� (caml2html: closure_g) *)
  | KNormal.Unit -> Unit
  | KNormal.Int(i) -> Int(i)
  | KNormal.Float(d) -> Float(d)
  | KNormal.Neg(x) -> Neg(x)
  | KNormal.Add(x, y) -> Add(x, y)
  | KNormal.Sub(x, y) -> Sub(x, y)
  | KNormal.Arith(op, x, y) -> Arith(op, x, y)
  | KNormal.FNeg(x) -> FNeg(x)
  | KNormal.FAdd(x, y) -> FAdd(x, y)
  | KNormal.FSub(x, y) -> FSub(x, y)
  | KNormal.FMul(x, y) -> FMul(x, y)
  | KNormal.FDiv(x, y) -> FDiv(x, y)
  | KNormal.IfEq(x, y, e1, e2) -> IfEq(x, y, g env known e1, g env known e2)
  | KNormal.IfLE(x, y, e1, e2) -> IfLE(x, y, g env known e1, g env known e2)
  | KNormal.Let((x, t), e1, e2) -> Let((x, t), g env known e1, g (M.add x t env) known e2)
  | KNormal.Var(x) -> Var(x)
  | KNormal.LetRec({ KNormal.name = (x, t); KNormal.args = yts; KNormal.body = e1 }, e2) -> (* �ؿ�����ξ�� (caml2html: closure_letrec) *)
      (* �ؿ����let rec x y1 ... yn = e1 in e2�ξ��ϡ�
	 x�˼�ͳ�ѿ����ʤ�(closure��𤵤�direct�˸ƤӽФ���)
	 �Ȳ��ꤷ��known���ɲä���e1�򥯥������Ѵ����Ƥߤ� *)
      let toplevel_backup = !toplevel in
      let env' = M.add x t env in
      let known' = S.add x known in
      let e1' = g (M.add_list yts env') known' e1 in
      (* �����˼�ͳ�ѿ����ʤ��ä������Ѵ����e1'���ǧ���� *)
      (* ���: e1'��x���Ȥ��ѿ��Ȥ��ƽи��������closure��ɬ��!
         (thanks to nuevo-namasute and azounoman; test/cls-bug2.ml����) *)
      let zs = S.diff (fv e1') (S.of_list (List.map fst yts)) in
      let known', e1' =
	if S.is_empty zs then known', e1' else
	(* ���ܤ��ä������(toplevel����)���ᤷ�ơ����������Ѵ�����ľ�� *)
	(Format.eprintf "free variable(s) %s found in function %s@." (Id.pp_list (S.elements zs)) x;
	 Format.eprintf "function %s cannot be directly applied in fact@." x;
	 toplevel := toplevel_backup;
	 let e1' = g (M.add_list yts env') known e1 in
	 known, e1') in
      let zs = S.elements (S.diff (fv e1') (S.add x (S.of_list (List.map fst yts)))) in (* ��ͳ�ѿ��Υꥹ�� *)
      let zts = List.map (fun z -> (z, M.find z env')) zs in (* �����Ǽ�ͳ�ѿ�z�η����������˰���env��ɬ�� *)
      toplevel := { name = (Id.L(x), t); args = yts; formal_fv = zts; body = e1' } :: !toplevel; (* �ȥåץ�٥�ؿ����ɲ� *)
      let e2' = g env' known' e2 in
      if S.mem x (fv e2') then (* x���ѿ��Ȥ���e2'�˽и����뤫 *)
	MakeCls((x, t), { entry = Id.L(x); actual_fv = zs }, e2') (* �и����Ƥ����������ʤ� *)
      else
	(Format.eprintf "eliminating closure(s) %s@." x;
	 e2') (* �и����ʤ����MakeCls���� *)
  | KNormal.App(x, ys) when S.mem x known -> (* �ؿ�Ŭ�Ѥξ�� (caml2html: closure_app) *)
      Format.eprintf "directly applying %s@." x;
      AppDir(Id.L(x), ys)
  | KNormal.App(f, xs) -> AppCls(f, xs)
  | KNormal.Tuple(xs) -> Tuple(xs)
  | KNormal.LetTuple(xts, y, e) -> LetTuple(xts, y, g (M.add_list xts env) known e)
  | KNormal.Get(x, y) -> Get(x, y)
  | KNormal.Put(x, y, z) -> Put(x, y, z)
  | KNormal.ExtArray(x) -> ExtArray(Id.L(x))
  | KNormal.ExtFunApp(x, ys) -> AppDir(Id.L("min_caml_" ^ x), ys)

let f e =
  toplevel := [];
  let e' = g M.empty S.empty e in
  (List.rev !toplevel, e')

let rec show_closure_t (syn : t) : string = 
  match syn with
    | Unit -> "()"
    | Int x  -> string_of_int x
    | Float x -> string_of_float x
    | Neg x -> "neg(" ^ x ^ ")"
    | Add (x, y) -> "+(" ^ x ^ ", " ^ y ^ ")"
    | Sub (x, y) -> "-(" ^ x ^ ", " ^ y ^ ")"
    | Arith (_, x, y) -> "arith(" ^ x ^ ", " ^ y ^ ")"
    | FNeg x -> "fneg(" ^ x ^ ")"
    | FAdd (x, y) -> "+.(" ^ x ^ ", " ^ y ^ ")"
    | FSub (x, y) -> "-.(" ^ x ^ ", " ^ y ^ ")"
    | FMul (x, y) -> "*.(" ^ x ^ ", " ^ y ^ ")"
    | FDiv (x, y) -> "/.(" ^ x ^ ", " ^ y ^ ")"
    | IfEq (a, b, x, y) -> "if=(" ^ a ^ "," ^ b ^ "," ^ show_closure_t x ^ ", " ^ show_closure_t y ^ ")"
    | IfLE (a, b, x, y) -> "if<=(" ^ a ^ "," ^ b ^ "," ^ show_closure_t x ^ ", " ^ show_closure_t y ^ ")"
    | Let ((name, ty), y, z) -> "let(" ^ name ^ " := " ^ show_closure_t y ^ " in " ^ show_closure_t z ^ ")"
    | Var x -> "var(" ^ x ^ ")"
    | MakeCls ((id, ty), clos, t) -> "make_cls(" ^ id ^ ":" ^ Type.show_type_t ty ^ ", " ^ show_closure clos ^ ", " ^ show_closure_t t ^ ")"
    | AppCls (x, ls) -> "app_cls(" ^ x ^ List.fold_left (fun x y -> x ^ "," ^ y) "" ls ^ ")"
    | AppDir (Id.L x, ls) -> "app_dir(" ^ x ^ List.fold_left (fun x y -> x ^ "," ^ y) "" ls ^ ")"
    | Tuple ls -> "tuple(" ^ List.fold_left (fun x y -> x ^ y ^ ", ") "" ls ^ ")"
    | LetTuple (ls, a, b) -> "let_tuple(...)"
    | Get (x, y) -> "get(" ^ x ^ ", " ^ y ^ ")"
    | Put (x, y, z) -> "put(" ^ x ^ ", " ^ y ^ "," ^ z ^ ")"
    | ExtArray (Id.L x) -> "ext_array(" ^ x ^ ")"
and show_fundef f = match f with
  | { name = (Id.L id, ty); args = ls; body = body } -> "fundef(" ^ id ^ "," ^ Type.show_type_t ty ^ "" ^ "," ^ show_closure_t body ^ ")"
and show_closure clos : string = match clos with
  | { entry = Id.L id; actual_fv = ls } -> "clos(entry = " ^ id ^ List.fold_left (fun x y -> x ^ ", " ^ y) "" ls ^ ")"


let show_prog prog : string = match prog with
  | Prog (vardefs, fundefs, exp) -> List.fold_left (fun x y -> x ^ show_fundef y ^ "\n") "" fundefs ^ show_closure_t exp

