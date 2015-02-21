open ast_il1Theory bigstep_il1Theory bigstep_il1_clockedTheory HolKernel Parse boolLib bossLib integerTheory finite_mapTheory lcsymtacs pairTheory l1_to_il1_compilerTheory l1_il1_correctnessTheory bigstep_il1Theory bigstep_l1_clockedTheory bigstep_l1Theory clocked_unclocked_il1_equivTheory clocked_equivTheory;

val _ = new_theory "l1_il1_clock";

val CLOCKED_L1_IMP_IL1 = store_thm("CLOCKED_L1_IMP_IL1",
``!c e s v s' c'.bs_l1_c c (e, s) (SOME (v, s', c')) ==>
    ?s'' tc tc'.
      bs_il1_c tc (l1_to_il1 e 0, con_store s) (SOME (l1_il1_val v, s'', tc')) /\ equiv (con_store s') s''``,
metis_tac [UNCLOCKED_IMP_CLOCKED_IL1, L1_TO_IL1_EXISTS_CORRECTNESS_THM, CLOCKED_IMP_UNCLOCKED]);

val _ = export_theory ();
