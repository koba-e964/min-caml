let f oc _infile module_ =
  Printf.fprintf oc "%s" (Llvm.string_of_llmodule module_)
  (*  assert (Llvm_bitwriter.output_bitcode oc module_) *)
