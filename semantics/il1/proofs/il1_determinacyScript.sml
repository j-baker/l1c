open HolKernel boolLib bossLib listTheory Parse IndDefLib finite_mapTheory relationTheory arithmeticTheory ast_l1Theory bigstep_l1Theory pred_setTheory pairTheory lcsymtacs integerTheory ast_il1Theory bigstep_il1Theory il1_backTheory;

val _ = new_theory "il1_determinacy";

val BS_IL1_EXPR_DETERMINACY = store_thm("BS_IL1_EXPR_DETERMINACY",
``!p v1.bs_il1_expr p v1 ==> !v2.bs_il1_expr p v2 ==> (v1 = v2)``,
ho_match_mp_tac bs_il1_expr_strongind THEN rw []
THEN1 (Cases_on `v1` THEN Cases_on `v2` THEN fs [Once bs_il1_expr_cases])
THEN1 (imp_res_tac BS_IL1_EXPR_PLUS_BACK_THM THEN res_tac THEN rw [])
THEN1 (imp_res_tac BS_IL1_EXPR_GEQ_BACK_THM THEN res_tac THEN rw [])
THEN1 (imp_res_tac BS_IL1_EXPR_DEREF_BACK_THM THEN rw [])
THEN1 (imp_res_tac BS_IL1_EXPR_EIF_BACK_THM THEN res_tac THEN rw [])
THEN1 (imp_res_tac BS_IL1_EXPR_EIF_BACK_THM THEN res_tac THEN rw []));

val IL1_DETERMINACY_THM = store_thm("IL1_DETERMINACY_THM",
``!p v1 s1.bs_il1 p v1 s1 ==> !v2 s2.bs_il1 p v2 s2 ==> (v1 = v2) /\ (s1 = s2)``,
ho_match_mp_tac bs_il1_strongind THEN rw []

THEN1 (fs [Once bs_il1_cases] THEN metis_tac [BS_IL1_EXPR_DETERMINACY])
THEN1 (fs [Once bs_il1_cases] THEN metis_tac [BS_IL1_EXPR_DETERMINACY])
THEN1 (fs [Once bs_il1_cases] THEN metis_tac [BS_IL1_EXPR_DETERMINACY])

THEN1 (imp_res_tac IL1_ASSIGN_BACK_THM THEN rw [] THEN `IL1_Integer n = IL1_Integer n'` by metis_tac [BS_IL1_EXPR_DETERMINACY] THEN rw [] THEN metis_tac [])
THEN1 (imp_res_tac IL1_ASSIGN_BACK_THM THEN rw [] THEN `IL1_Integer n = IL1_Integer n'` by metis_tac [BS_IL1_EXPR_DETERMINACY] THEN rw [] THEN metis_tac [])
THEN1 (imp_res_tac IL1_ASSIGN_BACK_THM THEN rw [] THEN `IL1_Integer n = IL1_Integer n'` by metis_tac [BS_IL1_EXPR_DETERMINACY] THEN rw [] THEN metis_tac [])

THEN1 (imp_res_tac IL1_SEQ_BACK_THM THEN rw [] THEN metis_tac [])
THEN1 (imp_res_tac IL1_SEQ_BACK_THM THEN rw [] THEN metis_tac [])

THEN1 (imp_res_tac IL1_SIF_BACK_THM THEN rw [] THEN imp_res_tac BS_IL1_EXPR_DETERMINACY THEN rw [] THEN metis_tac [])
THEN1 (imp_res_tac IL1_SIF_BACK_THM THEN rw [] THEN imp_res_tac BS_IL1_EXPR_DETERMINACY THEN rw [] THEN metis_tac [])
THEN1 (imp_res_tac IL1_SIF_BACK_THM THEN rw [] THEN imp_res_tac BS_IL1_EXPR_DETERMINACY THEN rw [] THEN metis_tac [])
THEN1 (imp_res_tac IL1_SIF_BACK_THM THEN rw [] THEN imp_res_tac BS_IL1_EXPR_DETERMINACY THEN rw [] THEN metis_tac [])


THEN1 (imp_res_tac IL1_WHILE_BACK_THM THEN rw [] THEN imp_res_tac BS_IL1_EXPR_DETERMINACY THEN rw [] THEN metis_tac [])
THEN1 (imp_res_tac IL1_WHILE_BACK_THM THEN rw [] THEN imp_res_tac BS_IL1_EXPR_DETERMINACY THEN rw [] THEN metis_tac [])
THEN1 (imp_res_tac IL1_WHILE_BACK_THM THEN rw [] THEN imp_res_tac BS_IL1_EXPR_DETERMINACY THEN rw [] THEN metis_tac [])
THEN1 (imp_res_tac IL1_WHILE_BACK_THM THEN rw [] THEN imp_res_tac BS_IL1_EXPR_DETERMINACY THEN rw [] THEN metis_tac []));

val _ = export_theory ();
