open Int32

type reg =
  | Reg of int
type freg =
  | FReg of int

type label = string

type fop = FAdd | FSub | FMul | FDiv

type pseudo = ABC of bool * label

type zebius_inst =
  | Write of reg
  | Read of reg
  | MovI of int * reg
  | MovPc of label * reg
  | MovR of reg * reg
  | Store of reg * reg (* MOV.L 1, @2 *)
  | Load of reg * reg (* MOV.L @1, 2 *)
  | StsPr of reg
  | AddR of reg * reg
  | AddI of int * reg
  | CmpEq of reg * reg
  | CmpGt of reg * reg
  | Sub of reg * reg
  | And of reg * reg
  | Not of reg * reg
  | Or of reg * reg
  | Xor of reg * reg
  | Shld of reg * reg
  | BC of bool * label
  | Bra of label
  | Jmp of reg
  | Jsr of reg
  | Rts
  | FLdI0 of freg
  | FLdI1 of freg
  | FMov of freg * freg
  | FStore of freg * reg (* MOV.L 1, @2 *)
  | FLoad of reg * freg (* MOV.L @1, 2 *)
  | FOp of fop * freg * freg
  | FCmpEq of freg * freg
  | FCmpGt of freg * freg
  | FNeg of freg
  | FSqrt of freg
  | LdsFpul of reg
  | StsFpul of reg
  | FldsFpul of freg
  | FstsFpul of freg
  | FtrcFpul of freg
  | FloatFpul of freg
  | Pseudo of pseudo
  | Label of label
  | DataI of int32
  | DataL of label
  | Align
  | ExtFile of string
  | Comment of string

let reg_of_string str = 
  let rec sub n =
    if n >= 16 then
      failwith ("not a valid GPR: " ^ str);
    if str = "R" ^ string_of_int n then
      Reg n
    else sub (n+1)
  in sub 0

let freg_of_string str = 
  let rec sub n =
    if n >= 16 then
      failwith ("not a valid Float Register: " ^ str);
    if str = "FR" ^ string_of_int n then
      FReg n
    else sub (n+1)
  in sub 0

(* size of instruction in words(2 bytes) *)
let size = function
  | Pseudo (ABC _) -> 5
  | Label _ -> 0
  | Align   -> 0
  | DataI _ -> 2
  | DataL _ -> 2
  | Bra _ | Jmp _ | Jsr _ | Rts -> 2
  | ExtFile _ -> 1000000 (* infinite *)
  | Comment _ -> 0
  | _ -> 1

let mov r1 r2 = MovR (reg_of_string r1, reg_of_string r2)
let fmov r1 r2 = FMov (freg_of_string r1, freg_of_string r2)

let filter_queue p queue =
  let newq = Queue.create () in
  Queue.iter (fun x -> if p x then Queue.add x newq) queue;
  newq

let list_of_queue q = List.rev (Queue.fold (fun x y -> y :: x) [] q)
let rec times n f x = if n <= 0 then x else times (n-1) f (f x)


(* This function look for @lbl@ and returns the address of the label wrapped with Some. If not found, this returns None. *)
let rec search_label lbl (ls : zebius_inst list) : int option = match ls with
  | [] -> None
  | Label x :: _ when x = lbl -> Some 0
  | x :: y -> match search_label lbl y with
    | None -> None
    | Some d -> Some (size x + d)


let replace_abc b lbl rest : zebius_inst list =
  let Some dist = search_label lbl rest in (* look for following instructions *)
  if dist <= 60 then
     [ BC (b, lbl) ]
  else begin
    let tmp1 = Id.genid "._iftmp1" in
    let tmp2 = Id.genid "._iftmp2" in
    [ BC (b, tmp1)
    ; Bra tmp2
    ; Label tmp1
    ; Bra lbl
    ; Label tmp2
    ]
  end
let pseudo_one newq ls = match ls with
  | Pseudo (ABC (b, lbl)) :: rest ->
    List.iter (fun x -> Queue.add x newq) (replace_abc b lbl rest); rest
  | x :: y -> Queue.add x newq; y
  | [] -> failwith "error:pseudo_one"



let process_pseudo q = 
  let l = list_of_queue q in
  let newq = Queue.create () in
  let rec proc ls = match ls with
    | [] -> ()
    | _ :: _ -> proc (pseudo_one newq ls)
  in proc l; newq

let is_nop = function
  | AddI (i, _) -> i = 0
  | MovR (Reg a, Reg b) -> a = b
  | FMov (FReg a, FReg b) -> a = b
  | And (Reg a, Reg b) -> a = b
  | Or (Reg a, Reg b) -> a = b
  | _ -> false

let eliminate_nop = filter_queue (fun x -> not (is_nop x))

let peep_one newq ls = match ls with
  | AddI (i1, r1) :: AddI (i2, r2) :: rest when r1 = r2 && i1 + i2 <= 127 && i1 + i2 >= -128 ->
    Queue.add (AddI (i1 + i2, r1)) newq; rest
  | x :: y -> Queue.add x newq; y
  | [] -> failwith "error:peep_one"

let peephole_opt q = 
  let l = list_of_queue q in
  let newq = Queue.create () in
  let rec proc ls = match ls with
    | [] -> ()
    | _ :: _ -> proc (peep_one newq ls)
  in proc l; newq

let show_reg (Reg x) = "R" ^ string_of_int x
let show_freg (FReg x) = "FR" ^ string_of_int x
let show_fop = function
  | FAdd -> "FADD"
  | FMul -> "FMUL"
  | FSub -> "FSUB"
  | FDiv -> "FDIV"

let show_inst = function
  | Write r -> "\tWRITE " ^ show_reg r
  | Read r  -> "\tREAD " ^ show_reg r
  | MovI (i, r) -> Printf.sprintf "\tMOV\t#%d, %s" i (show_reg r)
  | MovPc (l, r) -> Printf.sprintf "\tMOV.L\t%s, %s" l (show_reg r)
  | MovR (r1, r2) -> Printf.sprintf "\tMOV\t%s, %s" (show_reg r1) (show_reg r2)
  | Store (r1, r2) -> Printf.sprintf "\tMOV.L\t%s, @%s" (show_reg r1) (show_reg r2)
  | Load (r1, r2) -> Printf.sprintf "\tMOV.L\t@%s, %s" (show_reg r1) (show_reg r2)
  | StsPr r -> Printf.sprintf "\tSTS\tPR, %s" (show_reg r)
  | AddR (r1, r2) -> Printf.sprintf "\tADD\t%s, %s" (show_reg r1) (show_reg r2)
  | AddI (i, r) -> Printf.sprintf "\tADD\t#%d, %s" i (show_reg r)
  | CmpEq (r1, r2) -> Printf.sprintf "\tCMP/EQ\t%s, %s" (show_reg r1) (show_reg r2)
  | CmpGt (r1, r2) -> Printf.sprintf "\tCMP/GT\t%s, %s" (show_reg r1) (show_reg r2)
  | Sub (r1, r2) -> Printf.sprintf "\tSUB\t%s, %s" (show_reg r1) (show_reg r2)
  | And (r1, r2) -> Printf.sprintf "\tAND\t%s, %s" (show_reg r1) (show_reg r2)
  | Not (r1, r2) -> Printf.sprintf "\tNOT\t%s, %s" (show_reg r1) (show_reg r2)
  | Or (r1, r2) -> Printf.sprintf "\tOR\t%s, %s" (show_reg r1) (show_reg r2)
  | Xor (r1, r2) -> Printf.sprintf "\tXOR\t%s, %s" (show_reg r1) (show_reg r2)
  | Shld (r1, r2) -> Printf.sprintf "\tSHLD\t%s, %s" (show_reg r1) (show_reg r2)
  | BC (b, l) -> "\t" ^ (if b then "BT" else "BF") ^ "\t" ^ l
  | Bra l -> Printf.sprintf "\tBRA\t%s\n\tAND\tR0, R0" l
  | Jmp r -> Printf.sprintf "\tJMP\t@%s\n\tAND\tR0, R0" (show_reg r)
  | Jsr r -> Printf.sprintf "\tJSR\t@%s\n\tAND\tR0, R0" (show_reg r)
  | Rts -> "\tRTS\n\tAND\tR0, R0"
  | FLdI0 fr -> Printf.sprintf "\tFLDI0\t%s" (show_freg fr)
  | FLdI1 fr -> Printf.sprintf "\tFLDI1\t%s" (show_freg fr)
  | FMov (fr1, fr2) -> Printf.sprintf "\tFMOV\t%s, %s" (show_freg fr1) (show_freg fr2)
  | FStore (fr1, r2) -> Printf.sprintf "\tFMOV.S\t%s, @%s" (show_freg fr1) (show_reg r2)
  | FLoad (r1, fr2) -> Printf.sprintf "\tFMOV.S\t@%s, %s" (show_reg r1) (show_freg fr2)
  | FOp (op, fr1, fr2) -> Printf.sprintf "\t%s\t%s, %s" (show_fop op) (show_freg fr1) (show_freg fr2)
  | FCmpEq (fr1, fr2) -> Printf.sprintf "\tFCMP/EQ\t%s, %s" (show_freg fr1) (show_freg fr2)
  | FCmpGt (fr1, fr2) -> Printf.sprintf "\tFCMP/GT\t%s, %s" (show_freg fr1) (show_freg fr2)
  | FNeg fr -> Printf.sprintf "\tFNEG\t%s" (show_freg fr)
  | FSqrt fr -> Printf.sprintf "\tFSQRT\t%s" (show_freg fr)
  | LdsFpul r -> Printf.sprintf "\tLDS\t%s, FPUL" (show_reg r)
  | StsFpul r -> Printf.sprintf "\tSTS\tFPUL, %s" (show_reg r)
  | FldsFpul fr -> Printf.sprintf "\tFLDS\t%s, FPUL" (show_freg fr)
  | FstsFpul fr -> Printf.sprintf "\tFSTS\tFPUL, %s" (show_freg fr)
  | FtrcFpul fr -> Printf.sprintf "\tFTRC\t%s, FPUL" (show_freg fr)
  | FloatFpul fr -> Printf.sprintf "\tFLOAT\tFPUL, %s" (show_freg fr)
  | Pseudo ps -> failwith "pseudo-code"
  | Label l -> l
  | DataI i -> "\t.data.l\t#" ^ Int32.to_string i
  | DataL l -> "\t.data.l\t" ^ l
  | Align -> "\t.align"
  | Comment s -> "\t;; " ^ s
  | ExtFile lib -> failwith "undefined"
let emit_inst oc = function
  | ExtFile lib ->
    if lib <> "" then begin
      let ic = open_in lib in
      begin try
        while true do
          let line = input_line ic in
          Printf.fprintf oc "%s\n" line;
        done
      with  | End_of_file ->  close_in ic
            | e ->
        close_in_noerr ic;
        raise e
      end
    end
  | inst -> Printf.fprintf oc "%s\n" (show_inst inst)
let emit oc code = 
  let code = process_pseudo code in
  Printf.eprintf "eliminating NOPs...\n";
  Printf.eprintf "peephole optimization...\n";
  let el =  code in
  let po = times 7 (fun x -> eliminate_nop (peephole_opt x)) el in
  Queue.iter (emit_inst oc) po


