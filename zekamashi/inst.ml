type reg =
  | Reg of int (* 0..31 *)
type freg =
  | FReg of int (* 0..31 *)

type reg_or_imm =
  | RIReg of int
  | RIImm of int

let show_reg (Reg i) = "$" ^ string_of_int i
let show_ri = function
  | RIReg i -> "R" ^ string_of_int i
  | RIImm i -> string_of_int i

type fop = FOpAdd | FOpSub | FOpMul | FOpDiv
type disp16 = int
type disp21 = int
type label = string
type cond = EQ | NE | GE | LE

type cmp = CEQ | CLE | CLT

let show_cond = function
  | EQ -> "BEQ"
  | NE -> "BNE"
  | GE -> "BGE"
  | LE -> "BLE"

let show_cmp = function
  | CEQ -> "EQ"
  | CLE -> "LE"
  | CLT -> "LT"

type zek_inst = 
  | Lda of reg * disp16 * reg
  | Ldah of reg * disp16 * reg
  | Ldl of reg * disp16 * reg
  | Stl of reg * disp16 * reg
  | BC of cond * reg * label
  | Br of reg * label
  | Bsr of reg * label
  | Jmp of reg * reg
  | Jsr of reg * reg
  | Ret of reg * reg
  | Addl of reg * reg_or_imm * reg
  | Subl of reg * reg_or_imm * reg
  | Cmp of cmp * reg * reg_or_imm * reg
  | Label of label
  | Comment of string
  | ExtFile of string

let show_zek_inst = function
  | Lda (a, d, b) -> "\tLDA\t" ^ show_reg a ^ ", " ^ string_of_int d ^ "(" ^ show_reg b ^ ")"
  | Ldah (a, d, b) -> "\tLDAH\t" ^ show_reg a ^ ", " ^ string_of_int d ^ "(" ^ show_reg b ^ ")"
  | Ldl (a, d, b) -> "\tLDL\t" ^ show_reg a ^ ", " ^ string_of_int d ^ "(" ^ show_reg b ^ ")"
  | Stl (a, d, b) -> "\tSTL\t" ^ show_reg a ^ ", " ^ string_of_int d ^ "(" ^ show_reg b ^ ")"
  | BC (c, a, d) -> "\t" ^ show_cond c ^ "\t" ^ show_reg a ^ ", " ^ d
  | Br (a, d) -> "\tBR\t" ^ show_reg a ^ ", " ^ d
  | Bsr (a, d) -> "\tBSR\t" ^ show_reg a ^ ", " ^ d
  | Jmp (a, b) -> "\tJMP\t" ^ show_reg a ^ ", (" ^ show_reg b ^ ")"
  | Jsr (a, b) -> "\tJSR\t" ^ show_reg a ^ ", (" ^ show_reg b ^ ")"
  | Ret (a, b) -> "\tRET\t" ^ show_reg a ^ ", (" ^ show_reg b ^ ")"
  | Addl (a, b, c) -> "\tADDL\t" ^ show_reg a ^ ", " ^ show_ri b ^ ", " ^ show_reg c
  | Subl (a, b, c) -> "\tSUBL\t" ^ show_reg a ^ ", " ^ show_ri b ^ ", " ^ show_reg c
  | Cmp (op, a, b, c) -> "\tCMP" ^ show_cmp op ^ "\t" ^ show_reg a ^ ", " ^ show_ri b ^ ", " ^ show_reg c
  | Label l -> l ^ ":"
  | Comment s -> "    # " ^ s ^ "\n"
  | ExtFile _ -> failwith "show_zek_inst for ExtFile"
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
  | inst -> Printf.fprintf oc "%s\n" (show_zek_inst inst)
let emit oc code = 
  Queue.iter (emit_inst oc) code

let mov src dest = Lda (dest, 0, src)

