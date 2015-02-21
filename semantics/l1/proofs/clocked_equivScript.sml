open ast_l1Theory bigstep_l1Theory bigstep_l1_clockedTheory HolKernel Parse boolLib bossLib integerTheory finite_mapTheory lcsymtacs;

val _ = new_theory "clocked_equiv";

val CLOCKED_IMP_UNCLOCKED = store_thm("CLOCKED_IMP_UNCLOCKED", ``!c p r.bs_l1_c c p r ==> !v s' c'.(r = SOME (v, s', c')) ==> bs_l1 p v s'``,
ho_match_mp_tac bs_l1_c_strongind THEN rw [] THEN rw [Once bs_l1_cases] THEN metis_tac []);

val UNCLOCKED_IMP_CLOCKED = store_thm("UNCLOCKED_IMP_CLOCKED",
``!p v s'.bs_l1 p v s' ==> !cl'. ?cl. bs_l1_c (SUC cl) p (SOME (v, s', cl'))``,
ho_match_mp_tac bs_l1_strongind THEN rw []
THEN rw [Once bs_l1_c_cases] THEN metis_tac []);

val _ = export_theory ();
