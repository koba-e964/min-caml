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

val emit : out_channel -> zebius_inst Queue.t -> unit 

