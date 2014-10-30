type a_op =
  | AMul | ADiv

type t = (* MinCamlの構文を表現するデータ型 (caml2html: syntax_t) *)
  | Unit
  | Bool of bool
  | Int of int
  | Float of float
  | Not of t
  | Neg of t
  | Add of t * t
  | Sub of t * t
  | Arith of a_op * t * t
  | FNeg of t
  | FAdd of t * t
  | FSub of t * t
  | FMul of t * t
  | FDiv of t * t
  | Eq of t * t
  | LE of t * t
  | If of t * t * t
  | Let of (Id.t * Type.t) * t * t
  | Var of Id.t
  | LetRec of fundef * t
  | App of t * t list
  | Tuple of t list
  | LetTuple of (Id.t * Type.t) list * t * t
  | Array of t * t
  | Get of t * t
  | Put of t * t * t
and fundef = { name : Id.t * Type.t; args : (Id.t * Type.t) list; body : t }
and declare = 
  | VarDec of Id.t * t
  | FunDec of fundef
let rec show_syntax_t (syn : t) : string =
  match syn with
    | Unit -> "()"
    | Bool x -> string_of_bool x
    | Int x  -> string_of_int x
    | Float x -> string_of_float x
    | Not x -> "not(" ^ show_syntax_t x ^ ")"
    | Neg x -> "neg(" ^ show_syntax_t x ^ ")"
    | Add (x, y) -> "+(" ^ show_syntax_t x ^ ", " ^ show_syntax_t y ^ ")"
    | Sub (x, y) -> "-(" ^ show_syntax_t x ^ ", " ^ show_syntax_t y ^ ")"
    | Arith (_, x, y) -> "arith(" ^ show_syntax_t x ^ ", " ^ show_syntax_t y ^ ")"
    | FNeg x -> "fneg(" ^ show_syntax_t x ^ ")"
    | FAdd (x, y) -> "+.(" ^ show_syntax_t x ^ ", " ^ show_syntax_t y ^ ")"
    | FSub (x, y) -> "-.(" ^ show_syntax_t x ^ ", " ^ show_syntax_t y ^ ")"
    | FMul (x, y) -> "*.(" ^ show_syntax_t x ^ ", " ^ show_syntax_t y ^ ")"
    | FDiv (x, y) -> "/.(" ^ show_syntax_t x ^ ", " ^ show_syntax_t y ^ ")"
    | Eq (x, y) -> "=(" ^ show_syntax_t x ^ ", " ^ show_syntax_t y ^ ")"
    | LE (x, y) -> "<=(" ^ show_syntax_t x ^ ", " ^ show_syntax_t y ^ ")"
    | If (x, y, z) -> "if(" ^ show_syntax_t x ^ ", " ^ show_syntax_t y ^ "," ^ show_syntax_t z ^ ")"
    | Let ((name, ty), y, z) -> "let(" ^ name ^ " := ...)"
    | Var x -> "var(" ^ x ^ ")"
    | LetRec (x,y) -> "letrec(" ^ show_fundef x ^ ", " ^ show_syntax_t y ^ ")"
    | App (x, ls) -> "app(" ^ show_syntax_t x ^ ", " ^ List.fold_left (fun x y -> x ^ "," ^ show_syntax_t y) "" ls ^ ")"
    | Tuple ls -> "tuple(" ^ List.fold_left (fun x y -> x ^ show_syntax_t y ^ ", ") "" ls ^ ")"
    | LetTuple (ls, a, b) -> "let_tuple(...)"
    | Array (x, y) -> "array(" ^ show_syntax_t x ^ ", " ^ show_syntax_t y ^ ")"
    | Get (x, y) -> "get(" ^ show_syntax_t x ^ ", " ^ show_syntax_t y ^ ")"
    | Put (x, y, z) -> "put(" ^ show_syntax_t x ^ ", " ^ show_syntax_t y ^ "," ^ show_syntax_t z ^ ")"

and show_fundef f = match f with
  | { name = (id, ty); args = ls; body = body } -> "fundef(" ^ id ^ "," ^ Type.show_type_t ty ^ "" ^ "," ^ show_syntax_t body ^ ")"

let show_library lib = List.fold_left (fun x y -> x ^ "\n" ^ match y with
   | VarDec (id, exp) -> id ^ " := " ^ show_syntax_t exp
   | FunDec f         -> show_fundef f
  ) "library:" lib

exception ErrPos of int * int

