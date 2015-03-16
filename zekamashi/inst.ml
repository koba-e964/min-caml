type reg =
  | Reg of int (* 0..31 *)
type freg =
  | FReg of int (* 0..31 *)

type reg_or_imm =
  | RIReg of int
  | RIImm of int

let show_reg (Reg i) = "$" ^ string_of_int i
let show_freg (FReg i) = "$f" ^ string_of_int i
let show_ri = function
  | RIReg i -> "$" ^ string_of_int i
  | RIImm i -> string_of_int i

type fop = FOpAdd | FOpSub | FOpMul
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
  | FBC of cond * freg * label
  | Cmp of cmp * reg * reg_or_imm * reg
  | And of reg * reg_or_imm * reg
  | Sll of reg * reg_or_imm * reg
  | Srl of reg * reg_or_imm * reg
  | Lds of freg * disp16 * reg
  | Sts of freg * disp16 * reg
  | Cmps of cmp * freg * freg * freg
  | FOp of fop * freg * freg * freg
  | Invs of freg * freg
  | Sqrts of freg * freg
  | Itofs of reg * freg
  | Label of label
  | Mov of reg * label (* macro, expanded to 2 instructions *)
  | Comment of string
  | ExtFile of string

let filter_queue p queue =
  let newq = Queue.create () in
  Queue.iter (fun x -> if p x then Queue.add x newq) queue;
  newq
let list_of_queue q = List.rev (Queue.fold (fun x y -> y :: x) [] q)

let abst_add rsrc imm rdest = 
  if Int32.compare imm (Int32.of_int (-32768)) >= 0 && Int32.compare imm (Int32.of_int 32768) < 0
    then
      [Lda (rdest, Int32.to_int imm, rsrc)]
    else
      let m = Int32.to_int (Int32.logand imm (Int32.of_int 0xffff)) in
      let m' = if m >= 32768 then m - 65536 else m in
      let n = Int32.to_int (Int32.shift_right (Int32.sub imm (Int32.of_int m')) 16) in
      let n' = if n >= 32768 then n - 65536 else n in
      if m' = 0 then
        [Ldah (rdest, n', rsrc)]
      else begin
        [Lda (rdest, m', rsrc)
        ;Ldah (rdest, n', rdest)]
      end


let replace_addl_subl newq inst = match inst with
  | Addl (rsrc, RIImm v, rdest) -> List.iter (fun x -> Queue.add x newq) (abst_add rsrc (Int32.of_int v) rdest) 
  | Subl (rsrc, RIImm v, rdest) -> List.iter (fun x -> Queue.add x newq) (abst_add rsrc (Int32.of_int (-v)) rdest) 
  | i -> Queue.add i newq
let process_addl_subl q = 
  let l = list_of_queue q in
  let newq = Queue.create () in
  let rec proc ls = match ls with
    | [] -> ()
    | x :: y -> replace_addl_subl newq x; proc y
  in proc l; newq


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
  | FBC (c, a, d) -> "\tF" ^ show_cond c ^ "\t" ^ show_freg a ^ ", " ^ d
  | Cmp (op, a, b, c) -> "\tCMP" ^ show_cmp op ^ "\t" ^ show_reg a ^ ", " ^ show_ri b ^ ", " ^ show_reg c
  | And (a, b, c) -> "\tAND\t" ^ show_reg a ^ ", " ^ show_ri b ^ ", " ^ show_reg c
  | Sll (a, b, c) -> "\tSLL\t" ^ show_reg a ^ ", " ^ show_ri b ^ ", " ^ show_reg c
  | Srl (a, b, c) -> "\tSRL\t" ^ show_reg a ^ ", " ^ show_ri b ^ ", " ^ show_reg c
  | Lds (a, d, b) -> "\tLDS\t" ^ show_freg a ^ ", " ^ string_of_int d ^ "(" ^ show_reg b ^ ")"
  | Sts (a, d, b) -> "\tSTS\t" ^ show_freg a ^ ", " ^ string_of_int d ^ "(" ^ show_reg b ^ ")"
  | Cmps (op, a, b, c) -> "\tCMPS" ^ show_cmp op ^ "\t" ^ show_freg a ^ ", " ^ show_freg b ^ ", " ^ show_freg c
  | FOp (FOpAdd, a, b, c) -> "\tADDS\t" ^ show_freg a ^ ", " ^ show_freg b ^ ", " ^ show_freg c
  | FOp (FOpSub, a, b, c) -> "\tSUBS\t" ^ show_freg a ^ ", " ^ show_freg b ^ ", " ^ show_freg c
  | FOp (FOpMul, a, b, c) -> "\tMULS\t" ^ show_freg a ^ ", " ^ show_freg b ^ ", " ^ show_freg c
  | Invs (a, b) -> "\tINVS\t" ^ show_freg a ^ ", " ^ show_freg b
  | Sqrts (a, b) -> "\tSQRTS\t" ^ show_freg a ^ ", " ^ show_freg b
  | Itofs (ra, fb) -> "\tITOFS\t" ^ show_reg ra ^ ", " ^ show_freg fb
  | Label l -> l ^ ":"
  | Mov (a, b) -> "\tMOV\t" ^ show_reg a ^ ", " ^ b
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
  let code1 = process_addl_subl code in
  Queue.iter (emit_inst oc) code1

let mov src dest = Lda (dest, 0, src)
let fmov src dest = FOp (FOpAdd, src, FReg 31, dest)
let li imm dest = Lda (dest, imm, Reg 31)
let li32 imm dest = abst_add (Reg 31) imm dest

