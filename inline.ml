open KNormal

(* インライン展開する関数の最大サイズ (caml2html: inline_threshold) *)
let threshold = ref 0 (* Mainで-inlineオプションによりセットされる *)

let rec size = function
  | IfEq(_, _, e1, e2) | IfLE(_, _, e1, e2)
  | Let(_, e1, e2) | LetRec({ body = e1 }, e2) -> 1 + size e1 + size e2
  | LetTuple(_, _, e) -> 1 + size e
  | _ -> 1

let rec g env knmap = function (* インライン展開ルーチン本体 (caml2html: inline_g) *)
  | IfEq(x, y, e1, e2) -> IfEq(x, y, g env knmap e1, g env knmap e2)
  | IfLE(x, y, e1, e2) -> IfLE(x, y, g env knmap e1, g env knmap e2)
  | Let(xt, IfEq(x, y, tr, fl), e) when size tr <= !threshold && size fl <= !threshold && size e <= !threshold -> 
      IfEq(x, y, Let(xt, tr, g env knmap e), Let(xt, fl, g env knmap e))
  | Let(xt, IfLE(x, y, tr, fl), e) when size tr <= !threshold && size fl <= !threshold && size e <= !threshold -> 
      IfLE(x, y, Let(xt, tr, g env knmap e), Let(xt, fl, g env knmap e))
  | Let(xt, e1, e2) -> Let(xt, g env knmap e1, g env knmap e2)
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) -> (* 関数定義の場合 (caml2html: inline_letrec) *)
      let env = if size e1 > !threshold then env else M.add x (yts, e1) env in
      LetRec({ name = (x, t); args = yts; body = g env knmap  e1}, g env knmap  e2)
  | App(x, ys) when M.mem x env -> (* 関数適用の場合 (caml2html: inline_app) *)
      let (zs, e) = M.find x env in
      Format.eprintf "inlining %s@." x;
      let env' =
	List.fold_left2
	  (fun env' (z, t) y -> M.add z y env')
	  M.empty
	  zs
	  ys in
      Alpha.g env' e
  | ExtFunApp (x, ys) as expr when M.mem x !knmap ->
     let  {name =(n,_); args=zs; body = e} = M.find x !knmap in
     if size e <= !threshold then begin
      Format.eprintf "inlining %s@." x;
      let env' =
	List.fold_left2
	  (fun env' (z, t) y -> M.add z y env')
	  M.empty
	  zs
	  ys in
      Alpha.g env' e
     end else expr
  | LetTuple(xts, y, e) -> LetTuple(xts, y, g env knmap e)
  | e -> e

let f knmap e = g M.empty knmap e
