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


let mov r1 r2 = MovR (reg_of_string r1, reg_of_string r2)
let fmov r1 r2 = FMov (freg_of_string r1, freg_of_string r2)

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
  | MovR (r1, r2) -> if r1 <> r2 then Printf.sprintf "\tMOV\t%s, %s" (show_reg r1) (show_reg r2) else ";;;nop"
  | Store (r1, r2) -> Printf.sprintf "\tMOV.L\t%s, @%s" (show_reg r1) (show_reg r2)
  | Load (r1, r2) -> Printf.sprintf "\tMOV.L\t@%s, %s" (show_reg r1) (show_reg r2)
  | StsPr r -> Printf.sprintf "\tSTS\tPR, %s" (show_reg r)
  | AddR (r1, r2) -> Printf.sprintf "\tADD\t%s, %s" (show_reg r1) (show_reg r2)
  | AddI (i, r) -> if i <> 0 then Printf.sprintf "\tADD\t#%d, %s" i (show_reg r) else ";;;nop"
  | CmpEq (r1, r2) -> Printf.sprintf "\tCMP/EQ\t%s, %s" (show_reg r1) (show_reg r2)
  | CmpGt (r1, r2) -> Printf.sprintf "\tCMP/GT\t%s, %s" (show_reg r1) (show_reg r2)
  | Sub (r1, r2) -> Printf.sprintf "\tSUB\t%s, %s" (show_reg r1) (show_reg r2)
  | And (r1, r2) -> Printf.sprintf "\tAND\t%s, %s" (show_reg r1) (show_reg r2)
  | Not (r1, r2) -> Printf.sprintf "\tNOT\t%s, %s" (show_reg r1) (show_reg r2)
  | Or (r1, r2) -> Printf.sprintf "\tOR\t%s, %s" (show_reg r1) (show_reg r2)
  | Xor (r1, r2) -> Printf.sprintf "\tXOR\t%s, %s" (show_reg r1) (show_reg r2)
  | Shld (r1, r2) -> Printf.sprintf "\tSHLD\t%s, %s" (show_reg r1) (show_reg r2)
  | BC (b, l) -> "\t" ^ (if b then "BT" else "BF") ^ "\t" ^ l
  | Bra l -> Printf.sprintf "\tBRA\t%s" l
  | Jmp r -> Printf.sprintf "\tJMP\t@%s\n\tAND\tR0, R0" (show_reg r)
  | Jsr r -> Printf.sprintf "\tJSR\t@%s\n\tAND\tR0, R0" (show_reg r)
  | Rts -> "\tRTS\n\tAND\tR0, R0"
  | FLdI0 fr -> Printf.sprintf "\tFLDI0\t%s" (show_freg fr)
  | FLdI1 fr -> Printf.sprintf "\tFLDI1\t%s" (show_freg fr)
  | FMov (fr1, fr2) -> if fr1 <> fr2 then Printf.sprintf "\tFMOV\t%s, %s" (show_freg fr1) (show_freg fr2) else ";;;nop"
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
  | FloatFpul fr -> Printf.sprintf "\tFLOAt\tFPUL, %s" (show_freg fr)
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
  Queue.iter (emit_inst oc) code


