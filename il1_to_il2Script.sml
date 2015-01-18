open HolKernel boolLib bossLib listTheory Parse IndDefLib finite_mapTheory relationTheory arithmeticTheory l1Theory pred_setTheory pairTheory lcsymtacs il1Theory integerTheory il2Theory;

val _ = new_theory "il1_to_il2";

val true_value_def = Define `true_value = 1`;

val false_value_def = Define `false_value = 0`;

val skip_value_def = Define `skip_value = 0`;

val il1e_to_il2_def = Define `
(il1e_to_il2 (IL1_Value (IL1_Integer n)) = [IL2_Push n]) /\
(il1e_to_il2 (IL1_Value IL1_ESkip) = [IL2_Push skip_value]) /\
(il1e_to_il2 (IL1_Value (IL1_Boolean T)) = [IL2_Push true_value]) /\
(il1e_to_il2 (IL1_Value (IL1_Boolean F)) = [IL2_Push false_value]) /\

(il1e_to_il2 (IL1_Plus e1 e2) = (il1e_to_il2 e1 ++ il1e_to_il2 e2 ++ [IL2_Plus])) /\

(il1e_to_il2 (IL1_Deref l) = [IL2_Load l]) /\
(il1e_to_il2 (IL1_Geq e1 e2) = (il1e_to_il2 e1) ++ (il1e_to_il2 e2)) /\

(il1e_to_il2 (IL1_EIf e1 e2 e3) =
                                    (il1e_to_il2 e1) ++ [IL2_Jgeq (&LENGTH (il1e_to_il2 e2))] ++ (il1e_to_il2 e2) ++ [IL2_Jump (&LENGTH  (il1e_to_il2 e3))] ++  (il1e_to_il2 e3))
`;




val _ = export_theory ();
