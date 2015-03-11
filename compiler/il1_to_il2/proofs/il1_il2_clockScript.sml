open ast_il1Theory bigstep_il1Theory bigstep_il1_clockedTheory HolKernel Parse boolLib bossLib integerTheory finite_mapTheory lcsymtacs pairTheory il1_to_il2_compilerTheory il1_il2_correctnessTheory smallstep_il2Theory smallstep_il2_clockedTheory clocked_unclocked_il1_equivTheory clocked_il2_equivTheory ast_il2Theory;

val _ = new_theory "il1_il2_clock";

val CLOCKED_IL1_IMP_IL2 = store_thm("CLOCKED_IL1_IMP_IL2",
``!c e s v s' c'.bs_il1_c c (e, s) (SOME (v, s', c')) ==> !stk.?tc tc'.exec_clocked (il1_to_il2 e) (SOME (0, tc, stk, s)) (SOME (&LENGTH (il1_to_il2 e), tc', (il1_il2_val v)::stk, s'))``,
metis_tac [CLOCKED_IMP_UNCLOCKED_IL1, CORRECTNESS_THM, CLOCKED_IL1_EQUIV_BIMP]);

val dud_diverge_thm = prove(``!e s.(!c.bs_il1_c c (e, s) NONE) ==> !tc stk. exec_clocked (il1_to_il2 e) (SOME (0, tc, stk, s)) NONE``, cheat);

val bs_il1_c_det_thm = prove(``!c p r r'.exec_clocked p a b /\ exec_clocked p a c

bs_il1_c c p r /\ bs_il1_c c p r' ==> (r = r')``, cheat);

val no_step_def = Define `
no_step p s = ~?r.exec_clocked_one p (SOME s) r
`;

val lem1 = prove(``!e s.(?c r.bs_il1_c c (e, s) (SOME r)) <=> ~(!c.bs_il1_c c (e, s) NONE)``, cheat);

val lem2 = prove(``!p stk s.(?c c' stk' s' r.exec_clocked p (SOME (0, c, stk, s)) (SOME (&LENGTH p, c', stk', s') )) <=> ~(!c.exec_clocked p (SOME (0, c, stk, s)) NONE)``, cheat);

val lem3 = prove(``!e s.(!v s'.~bs_il1 (e, s) v s') <=> ~(?c r.bs_il1_c c (e, s) (SOME r))``, cheat);

val lem4 = prove(``!e s.(!c.bs_il1_c c (e, s) NONE) ==> (!v s'.¬bs_il1 (e, s) v s')``, cheat);

val cor_oneway = prove(``
!e s.(~?v s'.bs_il1 (e, s) v s') ==> (!stk.~?stk' s'.exec (il1_to_il2 e) (0, stk, s) (&LENGTH (il1_to_il2 e), stk', s'))``,

rw []
THEN `!c.bs_il1_c c (e, s) NONE` by metis_tac [lem1, lem3]

THEN imp_res_tac dud_diverge_thm

THEN CCONTR_TAC THEN fs []

THEN imp_res_tac (GSYM CLOCKED_IL1_EQUIV_BIMP)

THEN metis_tac [lem2]);

val divergence_thm = prove(``!e s.(~?v s'. bs_il1 (e, s) v s') <=> (!stk.~?stk' s'.exec (il1_to_il2 e) (0, stk, s) (&LENGTH (il1_to_il2 e), stk', s'))``,
metis_tac [EQ_IMP_THM, cor_oneway, CORRECTNESS_THM]);

val _ = export_theory ();
