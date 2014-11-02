type t = (* MinCamlの型を表現するデータ型 (caml2html: type_t) *)
  | Unit
  | Bool
  | Int
  | Float
  | Fun of t list * t (* arguments are uncurried *)
  | Tuple of t list
  | Array of t
  | Var of t option ref

let gentyp () = Var(ref None) (* 新しい型変数を作る *)

let rec show_type_t (ty : t) = match ty with
  | Unit -> "unit"
  | Bool -> "bool"
  | Int  -> "int"
  | Float -> "float"
  | Fun (ls, ty) -> "(" ^ List.fold_left (fun x y -> x ^ show_type_t y ^ "*") "" ls ^ "->" ^ show_type_t ty ^ ")"
  | Tuple ls -> "(" ^ List.fold_left (fun x y -> x ^ show_type_t y ^ ",") "" ls ^ ")"
  | Array ty -> "array(" ^ show_type_t ty ^ ")"
  | Var t  -> "type_var"

