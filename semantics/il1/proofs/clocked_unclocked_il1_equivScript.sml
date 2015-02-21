open ast_il1Theory bigstep_il1Theory bigstep_il1_clockedTheory HolKernel Parse boolLib bossLib integerTheory finite_mapTheory lcsymtacs pairTheory;

val _ = new_theory "clocked_unclocked_il1_equiv";

val bs_il1_expr_imp_clocked =  prove(
``!p v.bs_il1_expr p v ==> !cl'. ?cl. bs_il1_c_expr (SUC cl) p (SOME (v, cl'))``,
ho_match_mp_tac bs_il1_expr_strongind THEN rw [] THEN rw [Once bs_il1_c_expr_cases] THEN metis_tac []);

val clocked_imp_bs_il1_expr = prove(
``!cl p p'.bs_il1_c_expr cl p p' ==> !v cl'.(p' = SOME (v, cl')) ==> bs_il1_expr p v``,
ho_match_mp_tac bs_il1_c_expr_strongind THEN rw [FST, SND] THEN rw [Once bs_il1_expr_cases] THEN metis_tac []);



val CLOCKED_IMP_UNCLOCKED_IL1 = store_thm("CLOCKED_IMP_UNCLOCKED_IL1", ``!c p r.bs_il1_c c p r ==> !v s' c'.(r = SOME (v, s', c')) ==> bs_il1 p v s'``,
ho_match_mp_tac bs_il1_c_strongind THEN rw [] THEN rw [Once bs_il1_cases] THEN metis_tac [clocked_imp_bs_il1_expr]);

val UNCLOCKED_IMP_CLOCKED_IL1 = store_thm("UNCLOCKED_IMP_CLOCKED_IL1",
``!p v s'.bs_il1 p v s' ==> !cl'. ?cl. bs_il1_c (SUC cl) p (SOME (v, s', cl'))``,
ho_match_mp_tac bs_il1_strongind THEN rw []
THEN rw [Once bs_il1_c_cases] THEN metis_tac [bs_il1_expr_imp_clocked]);

val _ = export_theory ();
