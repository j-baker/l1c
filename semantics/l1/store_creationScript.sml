open HolKernel bossLib boolLib ast_l1Theory finite_mapTheory bigstep_l1Theory lcsymtacs;

val _ = new_theory "store_creation";

val create_store_def = Define `(create_store (L1_Value v) = FEMPTY) /\
(create_store (L1_Plus e1 e2) = (create_store e1) ⊌ (create_store e2)) /\
(create_store (L1_Geq e1 e2) = (create_store e1) ⊌ (create_store e2)) /\
(create_store (L1_If e1 e2 e3) = (create_store e1) ⊌ (create_store e2) ⊌ (create_store e3)) /\
(create_store (L1_Assign l e) = (FEMPTY |+ (l, 0)) ⊌ (create_store e)) /\
(create_store (L1_Deref l) = FEMPTY |+ (l, 0)) /\
(create_store (L1_Seq e1 e2) = (create_store e1) ⊌ (create_store e2)) /\
(create_store (L1_While e1 e2) = (create_store e1) ⊌ (create_store e2))`;

val contains_l1_def = Define `(contains_l1 l (L1_Value v) = F) /\
(contains_l1 l (L1_Plus e1 e2) = contains_l1 l e1 \/ contains_l1 l e2) /\
(contains_l1 l (L1_Geq e1 e2) = contains_l1 l e1 \/ contains_l1 l e2) /\
(contains_l1 l (L1_If e1 e2 e3) = contains_l1 l e1 \/ contains_l1 l e2 \/ contains_l1 l e3) /\
(contains_l1 l1 (L1_Assign l2 e) = (l1 = l2) \/ contains_l1 l1 e) /\
(contains_l1 l1 (L1_Deref l2) = (l1 = l2)) /\
(contains_l1 l (L1_Seq e1 e2) = contains_l1 l e1 \/ contains_l1 l e2) /\
(contains_l1 l (L1_While e1 e2) = contains_l1 l e1 \/ contains_l1 l e2)`;

val _ = store_thm("CONTAINS_IMP_IN_STORE",
``!l e.contains_l1 l e ==> l ∈ FDOM (create_store e)``,
Induct_on `e` THEN rw [contains_l1_def, create_store_def] THEN fs []);

val _ = export_theory ();
