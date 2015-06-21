open HolKernel boolLib bossLib lcsymtacs ast_il1Theory bigstep_il1Theory il1_typeTheory pred_setTheory

val _ = new_theory "il1_type_properties"

val BS_IL1_EXPR_TYPE_TOTAL = store_thm("BS_IL1_EXPR_TYPE_TOTAL",
``!e d t.il1_expr_type e d t ==> !s.(d = FDOM s) ==> ((t = intL1) /\ ?n.bs_il1_expr (e, s) (IL1_Integer n)) \/ ((t = boolL1) /\ ?b.bs_il1_expr (e, s) (IL1_Boolean b)) \/ ((t = unitL1) /\ bs_il1_expr (e, s) IL1_ESkip)``,
ho_match_mp_tac il1_expr_type_strongind THEN rw [] THEN rw [Once bs_il1_expr_cases]
THEN (TRY (metis_tac [])) THEN Cases_on `t` THEN rw [] THENL [all_tac, rw [Once bs_il1_expr_cases], rw [Once bs_il1_expr_cases]] THEN `?b.bs_il1_expr (e, s) (IL1_Boolean b)` by metis_tac [] THEN Cases_on `b` THEN metis_tac [])

val IL1_EXPR_TYPE_SUBSET_THM = store_thm("IL1_EXPR_TYPE_SUBSET_THM",
``!e g t.il1_expr_type e g t ==> !h. g ⊆ h ==> il1_expr_type e h t``,
ho_match_mp_tac il1_expr_type_strongind THEN rw [] THEN rw [Once il1_expr_type_cases] THEN metis_tac [SUBSET_DEF])

val IL1_TYPE_SUBSETS_THM = store_thm("IL1_TYPE_SUBSETS_THM",
``!e g t g'.il1_type e g t g' ==> g ⊆ g'``,
ho_match_mp_tac il1_type_strongind THEN rw [] THEN rw [Once il1_type_cases] THEN metis_tac [SUBSET_INSERT_RIGHT, SUBSET_TRANS, SUBSET_REFL, SUBSET_UNION])

val IL1_TYPE_SUBSET_THM = store_thm("IL1_TYPE_SUBSET_THM",
``!e g t g'.il1_type e g t g' ==> !h. g ⊆ h ==> il1_type e h t (g' ∪ h)``,
ho_match_mp_tac il1_type_strongind THEN rw [] THEN rw [Once il1_type_cases]

THEN1 metis_tac [IL1_EXPR_TYPE_SUBSET_THM, SUBSET_UNION_ABSORPTION]
THEN1 metis_tac [IL1_EXPR_TYPE_SUBSET_THM, SUBSET_UNION_ABSORPTION]

THEN1 metis_tac [INSERT_UNION_EQ, SUBSET_UNION_ABSORPTION, IL1_EXPR_TYPE_SUBSET_THM]
THEN1 metis_tac [INSERT_UNION_EQ, SUBSET_UNION_ABSORPTION, IL1_EXPR_TYPE_SUBSET_THM]


THEN1 metis_tac [IL1_TYPE_SUBSETS_THM, SUBSET_UNION, SUBSET_UNION_ABSORPTION, UNION_COMM, UNION_ASSOC]

THEN `g' ∪ g'' ∪ h = (g' ∪ h) ∪ (g'' ∪ h)` by metis_tac [UNION_COMM, UNION_ASSOC, UNION_IDEMPOT] THEN metis_tac [IL1_EXPR_TYPE_SUBSET_THM, IL1_TYPE_SUBSETS_THM, SUBSET_UNION, SUBSET_UNION_ABSORPTION])

val IL1_TYPE_SUBSET_2_THM = store_thm("IL1_TYPE_SUBSET_2_THM",
``!e g t g'.il1_type e g t g' ==> !h. g ⊆ h ==> ?h'.il1_type e h t h'``,
metis_tac [IL1_TYPE_SUBSET_THM])

val _ = export_theory ()
