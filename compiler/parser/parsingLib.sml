structure parsingLib = struct

open ParseTree l1 ast_l1Theory

fun snd (a, b, c, d) = b

val s1 = syntax_fns "ast_l1" 1 HolKernel.dest_monop HolKernel.mk_monop
val s2 = syntax_fns "ast_l1" 2 HolKernel.dest_binop HolKernel.mk_binop
val s3 = syntax_fns "ast_l1" 3 HolKernel.dest_triop HolKernel.mk_triop

fun tmm s t = snd (s t)


fun make_value_term (Int n) = tmm s1 "L1_Int" (intSyntax.term_of_int (Arbintcore.fromInt n))
  | make_value_term (Bool true) = tmm s1 "L1_Bool" ``T``
  | make_value_term (Bool false) = tmm s1 "L1_Bool" ``F``
  | make_value_term Skip = ``L1_Skip`` 

fun ab f (a, b) = (f a, f b)

fun get_loc l = 0

fun int_to_num n = (numSyntax.mk_numeral (Arbnumcore.fromInt n))


fun all_locs (Value v) = []
  | all_locs (Plus (e1, e2)) = all_locs e1 @ all_locs e2
  | all_locs (Geq (e1, e2)) = all_locs e1 @ all_locs e2
  | all_locs (If (e1, e2, e3)) = all_locs e1 @ all_locs e2 @ all_locs e3
  | all_locs (Assign (l, e)) = l::all_locs e
  | all_locs (Deref l) = [l]
  | all_locs (Seq (e1, e2)) = all_locs e1 @ all_locs e2
  | all_locs (While (e1, e2)) = all_locs e1 @ all_locs e2 

fun index_set e = Lib.mk_set (all_locs e)

fun index_of x [] = raise Empty
  | index_of x (y::ys) = if x = y then 0 else 1 + index_of x ys

fun make_term e = let val ind_set = Lib.mk_set (all_locs e)
                      fun get_loc l = index_of l ind_set
                      fun mk_term (Value v) = tmm s1 "L1_Value" (make_value_term v)
                        | mk_term (Plus es) = tmm s2 "L1_Plus" (ab mk_term es)
                        | mk_term (Geq es) = tmm s2 "L1_Geq" (ab mk_term es)
                        | mk_term (If (e1, e2, e3)) = tmm s3 "L1_If" (mk_term e1, mk_term e2, mk_term e3)
                        | mk_term (Assign (l, e)) = tmm s2 "L1_Assign" (int_to_num (get_loc l), mk_term e)
                        | mk_term (Deref l) = tmm s1 "L1_Deref" (int_to_num (get_loc l))
                        | mk_term (Seq es) = tmm s2 "L1_Seq" (ab mk_term es)
                        | mk_term (While es) = tmm s2 "L1_While" (ab mk_term es)
                      in mk_term e end

fun parse s = make_term (l1.parse s)

end
