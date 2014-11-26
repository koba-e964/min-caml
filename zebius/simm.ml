open Asm

let rec g env = function (* 命令列の即値最適化 (caml2html: simm13_g) *)
  | Ans(exp) -> Ans(g' env exp)
  | Let((x, t), Set(i), e) ->
      (* Format.eprintf "found simm13 %s = %d@." x i; *)
      let e' = g (M.add x i env) e in
      if List.mem x (fv e') then Let((x, t), Set(i), e') else
      ((* Format.eprintf "erased redundant Set to %s@." x; *)
       e')
  | Let(xt, exp, e) -> Let(xt, g' env exp, g env e)
and g' env = function (* 各命令の即値最適化 (caml2html: simm13_gprime) *)
  | Add(x, V(y)) when M.mem y env -> Add(x, C(M.find y env))
  | Add(x, V(y)) when M.mem x env -> Add(y, C(M.find x env))
  | Sub(x, y) when M.mem y env -> Add(x, C(- M.find y env))
  | Arith (Syntax.AMul, x, V(y)) when M.mem x env && M.mem y env -> Set (M.find x env * M.find y env)
  | Arith (Syntax.ADiv, x, V(y)) when M.mem x env && M.mem y env -> Set (M.find x env / M.find y env)
  | Arith (op, x, V(y)) when M.mem y env -> Arith (op, x, C (M.find y env))
  | Arith (op, x, V(y)) when M.mem x env -> Arith (op, y, C (M.find x env))
  | Arith (Syntax.AMul, x, C y) when M.mem x env -> Set (M.find x env * y) (* ad-hoc optimization for array indexing *)
  | Arith (Syntax.ADiv, x, C y) when M.mem x env -> Set (M.find x env / y) (* ad-hoc optimization *)
  | IfEq(x, y', e1, e2) -> IfEq(x, y', g env e1, g env e2)
  | IfLE(x, y', e1, e2) -> IfLE(x, y', g env e1, g env e2)
  | IfFEq(x, y, e1, e2) -> IfFEq(x, y, g env e1, g env e2)
  | IfFLE(x, y, e1, e2) -> IfFLE(x, y, g env e1, g env e2)
  | e -> e

let h { name = l; args = xs; fargs = ys; body = e; ret = t } = (* トップレベル関数の即値最適化 *)
  { name = l; args = xs; fargs = ys; body = g M.empty e; ret = t }

let optimize_var { vname = x; vtype = ty; vbody = expr } =
  { vname = x; vtype = ty; vbody = g M.empty expr }

let f_once (Prog(data, vardefs, fundefs, e)) = (* プログラム全体の即値最適化 *)
  Prog (data, List.map optimize_var vardefs, List.map h fundefs, g M.empty e)

let rec f prog = 
  let prog_s = f_once prog in
  if prog_s = prog then prog
  else f prog_s

