let limit = ref 1000
let asmlib   = ref "libmincaml.txt"
let glib  = ref ""
let verbose = ref false

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
 

(* currently, vardecs are just ignored. *)
let emit_code outchan vardecs fundecs (clexp : Closure.t) : unit =
  let virtual_code = Virtual.f (Closure.Prog (vardecs, fundecs, clexp)) in
  if !verbose then begin
    print_endline "**** virtual ****";
    print_endline (Asm.show_prog virtual_code);
  end;
  let simm = Simm.f virtual_code in
  if !verbose then begin
    print_endline "**** simm ****";
    print_endline (Asm.show_prog simm);
  end;
  let reg = RegAlloc.f simm in
  if !verbose then begin
    print_endline "**** reg-alloc ****";
    print_endline (Asm.show_prog reg);
  end;
  Emit.f outchan !asmlib reg


(* Processes a function declaration and adds it to fundecs.
   This is a very *ugly* code, so it should be rewritten. *)
let process_fundec vardecs fundecs ({ Syntax.name = (id, _) ; Syntax.args; Syntax.body } as fd) : unit =
  let wrap_exp = Syntax.LetRec (fd, Syntax.Var id) in
  let (exp, ty) = Typing.f_withtype wrap_exp false in
  Typing.extenv := M.add id ty !Typing.extenv;
  let dummy = "__dummy_unused_identifier_for_process_fundec" in
  let wrap_exp2 = Syntax.LetRec ({ fd with Syntax.name = (dummy, Type.gentyp ())}, Syntax.Var dummy) in
  let exp = Typing.f wrap_exp2 false in
  let normalized = KNormal.f exp in
  if !verbose then begin
    print_endline "**** normalized ****";
    print_endline (KNormal.show_knormal_t normalized);
  end;
  let rr = (Closure.f (iter !limit (Alpha.f normalized))) in
  let (fundefs, Closure.MakeCls ((uniq_name, _), _, _)) = rr in
  (* Add "min_caml_" to the head of function name. That is in order to call them as external functions. *)
  let newfundefs = List.map (fun ({ Closure.name = (Id.L n, ty) } as f) -> if n = uniq_name then { f with 
     Closure.name = (Id.L ("min_caml_" ^ id), ty)} else f) fundefs in
  fundecs := !fundecs @ newfundefs


let process_exp vardec fundec exp =
  let (exp, ty) = Typing.f_withtype exp false in
  let normalized = KNormal.f exp in
  if !verbose then begin
    print_endline "**** normalized ****";
    print_endline (KNormal.show_knormal_t normalized);
  end;
  let (fundefs, clexp) = (Closure.f (iter !limit (Alpha.f normalized))) in
  if !verbose then begin
    print_endline "**** closure-trans ****";
    print_endline (List.fold_left (fun x y -> x ^ Closure.show_fundef y ^ "\n") "" fundefs ^ Closure.show_closure_t clexp);
  end;
  fundec := !fundec @ fundefs;
  (clexp, ty)

(* processes one declaration *)
let process_declare (vardec : Closure.vardef list ref) (fundec : Closure.fundef list ref) (dec : Syntax.declare) : unit =
  match dec with
  | Syntax.VarDec (id, exp) ->
    let (cl, ty) = process_exp vardec fundec exp in
    Typing.extenv := M.add id ty !Typing.extenv;
    vardec := { Closure.vname = (Id.L id, ty); Closure.vbody = cl } :: !vardec;
  | Syntax.FunDec ({ Syntax.name = (id, _) ; Syntax.args; Syntax.body = exp } as fd) -> 
    process_fundec vardec fundec fd

let lexbuf_main inchan vardecs fundecs : Closure.t =
  let str = read_fully inchan in
  let exp = try
    Parser.exp Lexer.token (Lexing.from_string str)
  with 
    | Syntax.ErrPos (x, y) as e -> Printf.fprintf stderr "parse error at %d-%d, near %s" x y (String.sub str (x-20) (y-x+40)); raise e
    | e -> print_endline "error:"; raise e
  in
  fst (process_exp vardecs fundecs exp)

let lexbuf_lib inchan (vardec : Closure.vardef list ref) (fundec : Closure.fundef list ref) : unit = (* parse as library *)
  let str = read_fully inchan in
  let lib = try
    Parser.library Lexer.token (Lexing.from_string str)
  with 
    | Syntax.ErrPos (x, y) as e -> Printf.fprintf stderr "parse error at %d-%d, near %s" x y (String.sub str (x-20) (y-x+40)); raise e
    | e -> print_endline "error:"; raise e
  in
  print_endline (Syntax.show_library lib);
  List.iter (process_declare vardec fundec) lib

let file f vardec fundec = (* ファイルをコンパイルしてファイルに出力する (caml2html: main_file) *)
  let inchan = open_in (f ^ ".ml") in
  let outchan = open_out (f ^ ".s") in
  try
    let clexp = lexbuf_main inchan vardec fundec in
    emit_code outchan !vardec !fundec clexp;
    close_in inchan;
    close_out outchan;
  with e -> (close_in inchan; close_out outchan; raise e)

(* process library file (.ml) *)
let glib_process f vardecs fundecs =
  let inchan = open_in (f ^ ".ml") in
  try
    lexbuf_lib inchan vardecs fundecs;
    close_in inchan;
  with e -> (close_in inchan; raise e)



let () = (* ここからコンパイラの実行が開始される (caml2html: main_entry) *)
  let files = ref [] in
  Arg.parse
    [("-inline", Arg.Int(fun i -> Inline.threshold := i), "maximum size of functions inlined")
    ;("-iter", Arg.Int(fun i -> limit := i), "maximum number of optimizations iterated")
    ;("-lib", Arg.String(fun i -> asmlib := i), "path to libmincaml.txt")
    ;("-glib", Arg.String(fun i -> glib := i), "path to globals.ml")
    ;("-v", Arg.Unit(fun () -> verbose := true), "verbose information")
    ]
    (fun s -> files := !files @ [s])
    ("Mitou Min-Caml Compiler (C) Eijiro Sumii\n" ^
     Printf.sprintf "usage: %s [-inline m] [-iter n] ...filenames without \".ml\"..." Sys.argv.(0));
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
  let vardec = ref [] in
  let fundec = ref [] in
  if !glib <> "" then
    glib_process !glib vardec fundec;
  List.iter
    (fun f -> ignore (file f vardec fundec))
    !files
