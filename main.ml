let limit = ref 1000
let lib   = ref "libmincaml.txt"

let rec iter n e = (* 最適化処理をくりかえす (caml2html: main_iter) *)
  Format.eprintf "iteration %d@." n;
  if n = 0 then e else
  let e' = Elim.f (ConstFold.f (Inline.f (Assoc.f (Beta.f e)))) in
  if e = e' then e else
  iter (n - 1) e'

let read_fully ic : string =
  let lines = ref "" in
  try
    while true do
      lines := !lines ^ (input_line ic) ^ "\n"
    done
    ;""
  with End_of_file -> !lines
 

let lexbuf outchan inchan = (* バッファをコンパイルしてチャンネルへ出力する (caml2html: main_lexbuf) *)
  let str = read_fully inchan in
  Id.counter := 0;
  Typing.extenv := M.add_list
   [("print_int", Type.Fun ([Type.Int], Type.Unit))
   ;("float_of_int", Type.Fun ([Type.Int], Type.Float))
   ;("int_of_float", Type.Fun ([Type.Float], Type.Int))
   ;("abs_float", Type.Fun ([Type.Float], Type.Float))
   ;("sin", Type.Fun ([Type.Float], Type.Float))
   ;("cos", Type.Fun ([Type.Float], Type.Float))
   ;("atan", Type.Fun ([Type.Float], Type.Float))
   ;("sqrt", Type.Fun ([Type.Float], Type.Float))
   ]
  M.empty;
  let exp = try
    Parser.exp Lexer.token (Lexing.from_string str)
  with 
    | Syntax.ErrPos (x, y) as e -> Printf.fprintf stderr "parse error at %d-%d, near %s" x y (String.sub str (x-20) (y-x+40)); raise e
    | e -> print_endline "error:"; raise e
  in
  print_endline "**** expr ****";
  print_endline (Syntax.show_syntax_t exp);
  let normalized = KNormal.f (Typing.f exp) in
  print_endline "**** normalized ****";
  print_endline (KNormal.show_knormal_t normalized);
  let rr = (Closure.f (iter !limit (Alpha.f normalized))) in
  print_endline "**** closure-trans ****";
  print_endline (Closure.show_prog rr);
  let virtual_code = Virtual.f rr in
  print_endline "**** virtual ****";
  print_endline (Asm.show_prog virtual_code);
  let simm = Simm.f virtual_code in
  let reg = RegAlloc.f simm in
  Emit.f outchan !lib reg

let file f = (* ファイルをコンパイルしてファイルに出力する (caml2html: main_file) *)
  let inchan = open_in (f ^ ".ml") in
  let outchan = open_out (f ^ ".s") in
  try
    lexbuf outchan inchan;
    close_in inchan;
    close_out outchan;
  with e -> (close_in inchan; close_out outchan; raise e)

let () = (* ここからコンパイラの実行が開始される (caml2html: main_entry) *)
  let files = ref [] in
  Arg.parse
    [("-inline", Arg.Int(fun i -> Inline.threshold := i), "maximum size of functions inlined")
    ;("-iter", Arg.Int(fun i -> limit := i), "maximum number of optimizations iterated")
    ;("-lib", Arg.String(fun i -> lib := i), "path to libmincaml.txt")
    ]
    (fun s -> files := !files @ [s])
    ("Mitou Min-Caml Compiler (C) Eijiro Sumii\n" ^
     Printf.sprintf "usage: %s [-inline m] [-iter n] ...filenames without \".ml\"..." Sys.argv.(0));
  List.iter
    (fun f -> ignore (file f))
    !files
