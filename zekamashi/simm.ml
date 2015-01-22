open Asm

let rec g env fenv = function (* 命令列の即値最適化 *)
  | Ans(exp) -> Ans(g' env fenv exp)
  | Let((x, t), Li(i), e) ->
      let e' = g (M.add x i env) fenv e in
      if List.mem x (fv e') then Let((x, t), Li(i), e') else e'
  | Let((x, t), FLi f, e) ->
      let e' = g env (M.add x f fenv) e in
      if List.mem x (fv e') then Let((x, t), FLi f, e') else e'
  | Let(xt, Slw(y, C(i)), e) when M.mem y env -> (* for array access *)
      g env fenv (Let(xt, Li((M.find y env) lsl i), e))
  | Let(xt, exp, e) -> Let(xt, g' env fenv exp, g env fenv e)
and g' env fenv = function (* 各命令の即値最適化 *)
  | Add(x, V(y)) when M.mem y env -> Add(x, C(M.find y env))
  | Add(x, V(y)) when M.mem x env -> Add(y, C(M.find x env))
  | Sub(x, V(y)) when M.mem y env -> Sub(x, C(M.find y env))
  | Arith (op, x, V(y)) when M.mem y env -> Arith (op, x, C(M.find y env))
  | Slw(x, V(y)) when M.mem y env -> Slw(x, C(M.find y env))
  | Lwz(x, V(y)) when M.mem y env -> Lwz(x, C(M.find y env))
  | Stw(x, y, V(z)) when M.mem z env -> Stw(x, y, C(M.find z env))
  | Lfd(x, V(y)) when M.mem y env -> Lfd(x, C(M.find y env))
  | Stfd(x, y, V(z)) when M.mem z env -> Stfd(x, y, C(M.find z env))
  | IfEq(x, V(y), e1, e2) when M.mem y env -> 
      IfEq(x, C(M.find y env), g env fenv e1, g env fenv e2)
  | IfLE(x, V(y), e1, e2) when M.mem y env ->
      IfLE(x, C(M.find y env), g env fenv e1, g env fenv e2)
  | IfGE(x, V(y), e1, e2) when M.mem y env -> 
      IfGE(x, C(M.find y env), g env fenv e1, g env fenv e2)
  | IfEq(x, V(y), e1, e2) when M.mem x env -> 
      IfEq(y, C(M.find x env), g env fenv e1, g env fenv e2)
  | IfLE(x, V(y), e1, e2) when M.mem x env -> 
      IfGE(y, C(M.find x env), g env fenv e1, g env fenv e2)
  | IfGE(x, V(y), e1, e2) when M.mem x env -> 
      IfLE(y, C(M.find x env), g env fenv e1, g env fenv e2)
  | IfEq(x, y', e1, e2) -> IfEq(x, y', g env fenv e1, g env fenv e2)
  | IfLE(x, y', e1, e2) -> IfLE(x, y', g env fenv e1, g env fenv e2)
  | IfGE(x, y', e1, e2) -> IfGE(x, y', g env fenv e1, g env fenv e2)
  | IfFEq(x, y, e1, e2) when M.mem y fenv && M.find y fenv = 0.0 -> IfF0(x, g env fenv e1, g env fenv e2)
  | IfFEq(x, y, e1, e2) when M.mem x fenv && M.find x fenv = 0.0 -> IfF0(y, g env fenv e1, g env fenv e2)
  | IfFEq(x, y, e1, e2) -> IfFEq(x, y, g env fenv e1, g env fenv e2)
  | IfFLE(x, y, e1, e2) -> IfFLE(x, y, g env fenv e1, g env fenv e2)
  | IfF0(x, e1, e2) -> IfF0(x, g env fenv e1, g env fenv e2)
  | e -> e

(* トップレベル関数の 16 bit 即値最適化 *)
let h { name = l; args = xs; fargs = ys; body = e; ret = t } = 
  { name = l; args = xs; fargs = ys; body = g M.empty M.empty e; ret = t }

(* プログラム全体の 16 bit 即値最適化 *)
let f (Prog(data, fundefs, e)) = 
  Prog(data, List.map h fundefs, g M.empty M.empty e)
