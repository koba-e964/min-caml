let limit = ref 1000
let asmlib   = ref ""
let glib  = ref []
let inter = ref false
let verbose = ref false
let outfile = ref ""

let rec iter n knmap e = (* ��Ŭ�������򤯤꤫���� (caml2html: main_iter) *)
  Format.eprintf "iteration %d@." n;
  if n = 0 then e else
  let e' = Elim.f (ConstFold.f (Inline.f knmap (Assoc.f (Beta.f e)))) in
  if e = e' then e else
  iter (n - 1) knmap e'

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
  if !inter then begin 
    let ir = Closure.Prog (vardecs, fundecs, clexp) in
    let outchan = open_out (!outfile ^ "-inter.s") in
    Printf.fprintf outchan "%s\n" (Closure.show_prog ir);
    Printf.fprintf outchan "%s\n" (Asm.show_prog simm);
    close_out outchan
  end;
  let reg = RegAlloc.f simm in
  if !verbose then begin
    print_endline "**** reg-alloc ****";
    print_endline (Asm.show_prog reg);
  end;
  Emit.f outchan !asmlib reg


(* Processes a function declaration and adds it to fundecs.
   This is a very *ugly* code, so it should be rewritten. *)
let process_fundec vardecs fundecs knmap ({ Syntax.name = (id, _) ; Syntax.args; Syntax.body } as fd) : KNormal.fundef * string =
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
  let opt = iter !limit knmap (Alpha.f normalized) in
  let rr = Closure.f opt in
  let (fundefs, Closure.MakeCls ((uniq_name, _), _, _)) = rr in
  (* Add "min_caml_" to the head of function name. That is in order to call them as external functions. *)
  let newfundefs = List.map (fun ({ Closure.name = (Id.L n, ty) } as f) -> if n = uniq_name then { f with 
     Closure.name = (Id.L ("min_caml_" ^ id), ty)} else f) fundefs in
  fundecs := !fundecs @ newfundefs;
  let KNormal.LetRec (wrap_exp_fundef, _) = opt in
  (wrap_exp_fundef, id)

let process_exp vardec fundec knmap exp =
  let (exp, ty) = Typing.f_withtype exp false in
  let normalized = KNormal.f exp in
  if !verbose then begin
    print_endline "**** normalized ****";
    print_endline (KNormal.show_knormal_t normalized);
  end;
  let (fundefs, clexp) = (Closure.f (iter !limit knmap (Alpha.f normalized))) in
  if !verbose then begin
    print_endline "**** closure-trans ****";
    print_endline (List.fold_left (fun x y -> x ^ Closure.show_fundef y ^ "\n") "" fundefs ^ Closure.show_closure_t clexp);
  end;
  fundec := !fundec @ fundefs;
  (clexp, ty)

(* processes one declaration *)
let process_declare (vardec : Closure.vardef list ref) (fundec : Closure.fundef list ref) (knmap : (KNormal.fundef M.t) ref) (dec : Syntax.declare) : unit =
  match dec with
  | Syntax.VarDec (id, exp) ->
    let (cl, ty) = process_exp vardec fundec knmap exp in
    Typing.extenv := M.add id ty !Typing.extenv;
    vardec := !vardec @ [{ Closure.vname = (Id.L id, ty); Closure.vbody = cl }];
  | Syntax.FunDec ({ Syntax.name = (id, _) ; Syntax.args; Syntax.body = exp } as fd) -> 
    let (fdef, id) =process_fundec vardec fundec knmap fd in
    knmap := M.add id fdef !knmap

let lexbuf_main inchan vardecs fundecs knmap : Closure.t =
  let str = read_fully inchan in
  let exp = try
    Parser.exp Lexer.token (Lexing.from_string str)
  with 
    | Syntax.ErrPos (x, y) as e -> Printf.fprintf stderr "parse error at %d-%d, near %s" x y (String.sub str (x-20) (y-x+40)); raise e
    | e -> print_endline "error:"; raise e
  in
  fst (process_exp vardecs fundecs knmap exp)

let lexbuf_lib inchan (vardec : Closure.vardef list ref) (fundec : Closure.fundef list ref) (knmap : (KNormal.fundef M.t) ref) : unit = (* parse as library *)
  let str = read_fully inchan in
  let lib = try
    Parser.library Lexer.token (Lexing.from_string str)
  with 
    | Syntax.ErrPos (x, y) as e -> Printf.fprintf stderr "parse error at %d-%d, near %s" x y (String.sub str (x-20) (y-x+40)); raise e
    | e -> print_endline "error:"; raise e
  in
  print_endline (Syntax.show_library lib);
  List.iter (process_declare vardec fundec knmap) lib

let file f vardec fundec knmap = (* �ե�����򥳥�ѥ��뤷�ƥե�����˽��Ϥ��� (caml2html: main_file) *)
  let inchan = open_in (f ^ ".ml") in
  let outchan = open_out (f ^ ".s") in
  outfile := f;
  try
    let clexp = lexbuf_main inchan vardec fundec knmap in
    emit_code outchan !vardec !fundec clexp;
    close_in inchan;
    close_out outchan;
  with e -> (close_in inchan; close_out outchan; raise e)

(* process library file (.ml) *)
let glib_process f vardecs fundecs knmap =
  let inchan = open_in (f ^ ".ml") in
  try
    lexbuf_lib inchan vardecs fundecs knmap;
    close_in inchan;
  with e -> (close_in inchan; raise e)



let () = (* �������饳��ѥ���μ¹Ԥ����Ϥ���� (caml2html: main_entry) *)
  let files = ref [] in
  Arg.parse
    [("-inline", Arg.Int(fun i -> Inline.threshold := i), "maximum size of functions inlined")
    ;("-iter", Arg.Int(fun i -> limit := i), "maximum number of optimizations iterated")
    ;("-lib", Arg.String(fun i -> asmlib := i), "path to libmincaml.txt")
    ;("-glib", Arg.String(fun i -> glib := !glib @ [i]), "path to libary form (*.ml)")
    ;("-i", Arg.Unit(fun () -> inter := true), "emit IR (to *-inter.s)")
    ;("-v", Arg.Unit(fun () -> verbose := true), "verbose information")
    ;("-finv", Arg.Unit(fun () -> KNormal.finv := true), "use software implementation of finv")
    ;("-fsqrt", Arg.Unit(fun () -> Virtual.fsqrt := true), "use software implementation of fsqrt")
    ]
    (fun s -> files := !files @ [s])
    ("Mitou Min-Caml Compiler (C) Eijiro Sumii\n" ^
     Printf.sprintf "usage: %s [-inline m] [-iter n] ...filenames without \".ml\"..." Sys.argv.(0));
  Id.counter := 0;
  Typing.extenv := M.add_list
   [("print_int", Type.Fun ([Type.Int], Type.Unit))
   ;("print_char", Type.Fun ([Type.Int], Type.Unit))
   ;("float_of_int", Type.Fun ([Type.Int], Type.Float))
   ;("int_of_float", Type.Fun ([Type.Float], Type.Int))
   ;("read_float", Type.Fun ([Type.Unit], Type.Float))
   ;("read_int", Type.Fun ([Type.Unit], Type.Int))
   ;("sin", Type.Fun ([Type.Float], Type.Float))
   ;("cos", Type.Fun ([Type.Float], Type.Float))
   ;("atan", Type.Fun ([Type.Float], Type.Float))
   ;("sqrt", Type.Fun ([Type.Float], Type.Float))
   ;("floor", Type.Fun ([Type.Float], Type.Float))
   ;("finv", Type.Fun ([Type.Float], Type.Float))
   ]
  M.empty;
  let vardec = ref [] in
  let fundec = ref [] in
  let knmap = ref M.empty in
  List.iter (fun g ->
    glib_process g vardec fundec knmap) !glib;
  List.iter
    (fun f -> ignore (file f vardec fundec knmap))
    !files
