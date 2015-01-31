open HolKernel boolLib bossLib ast_l1Theory ast_il1Theory ast_il2Theory listTheory smallstep_il2Theory;

val _ = new_theory "il1_to_il2_compiler";

val il1e_to_il2_def = Define `
(il1e_to_il2 (IL1_Value (IL1_Integer n)) = [IL2_Push n]) /\
(il1e_to_il2 (IL1_Value IL1_ESkip) = [IL2_Push skip_value]) /\
(il1e_to_il2 (IL1_Value (IL1_Boolean T)) = [IL2_Push true_value]) /\
(il1e_to_il2 (IL1_Value (IL1_Boolean F)) = [IL2_Push false_value]) /\

(il1e_to_il2 (IL1_Plus e1 e2) = (il1e_to_il2 e2 ++ il1e_to_il2 e1 ++ [IL2_Plus])) /\

(il1e_to_il2 (IL1_Deref l) = [IL2_Load l]) /\

(il1e_to_il2 (IL1_EIf e1 e2 e3) =
                                    (il1e_to_il2 e1) ++ [IL2_Jz (&LENGTH (il1e_to_il2 e2) + 1)] ++ (il1e_to_il2 e2) ++ [IL2_Jump (&LENGTH  (il1e_to_il2 e3))] ++  (il1e_to_il2 e3)) /\
(il1e_to_il2 (IL1_Geq e1 e2) = (il1e_to_il2 e2) ++ (il1e_to_il2 e1) ++ [IL2_Geq])
`;

val il1_to_il2_def = Define `
(il1_to_il2 (IL1_Expr e) = il1e_to_il2 e) /\
(il1_to_il2 (IL1_Assign l e) = (il1e_to_il2 e) ++ [IL2_Store l; IL2_Push skip_value]) /\
(il1_to_il2 (IL1_Seq e1 e2) = (il1_to_il2 e1) ++ [IL2_Pop] ++ (il1_to_il2 e2)) /\
(il1_to_il2 (IL1_SIf e1 e2 e3) = (il1e_to_il2 e1) ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 1)] ++ (il1_to_il2 e2) ++ [IL2_Jump (&LENGTH (il1_to_il2 e3))] ++ (il1_to_il2 e3)) /\

(il1_to_il2 (IL1_While e1 e2) = (il1e_to_il2 e1) ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 2)] ++ (il1_to_il2 e2) ++ [IL2_Pop; IL2_Jump (-&(LENGTH ((il1e_to_il2 e1) ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 2)] ++ (il1_to_il2 e2)) + 2))] ++ [IL2_Push skip_value])`;


val _ = export_theory ();
