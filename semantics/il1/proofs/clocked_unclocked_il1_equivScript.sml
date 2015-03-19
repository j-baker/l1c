open ast_il1Theory bigstep_il1Theory bigstep_il1_clockedTheory HolKernel Parse boolLib bossLib integerTheory finite_mapTheory lcsymtacs pairTheory;

val _ = new_theory "clocked_unclocked_il1_equiv";

val CLOCKED_IMP_UNCLOCKED_IL1 = store_thm("CLOCKED_IMP_UNCLOCKED_IL1", ``!c p r.bs_il1_c c p r ==> !v s' c'.(r = SOME (v, s', c')) ==> bs_il1 p v s'``,
ho_match_mp_tac bs_il1_c_strongind THEN rw [] THEN rw [Once bs_il1_cases] THEN metis_tac []);

val UNCLOCKED_IMP_CLOCKED_IL1 = store_thm("UNCLOCKED_IMP_CLOCKED_IL1",
``!p v s'.bs_il1 p v s' ==> !cl'. ?cl. bs_il1_c (SUC cl) p (SOME (v, s', (SUC cl')))``,
ho_match_mp_tac bs_il1_strongind THEN rw []
THEN rw [Once bs_il1_c_cases] THEN metis_tac []);

val _ = export_theory ();
