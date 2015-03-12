open ast_il1Theory bigstep_il1Theory bigstep_il1_clockedTheory HolKernel Parse boolLib bossLib integerTheory finite_mapTheory lcsymtacs pairTheory il1_to_il2_compilerTheory il1_il2_correctnessTheory smallstep_il2Theory smallstep_il2_clockedTheory clocked_unclocked_il1_equivTheory clocked_il2_equivTheory ast_il2Theory il1_typeTheory arithmeticTheory optionTheory pred_setTheory il1_type_propertiesTheory;

val _ = new_theory "il1_il2_clock";

val CLOCKED_IL1_IMP_IL2 = store_thm("CLOCKED_IL1_IMP_IL2",
``!c e s v s' c'.bs_il1_c c (e, s) (SOME (v, s', c')) ==> !stk.?tc tc'.exec_clocked (il1_to_il2 e) (SOME (0, tc, stk, s)) (SOME (&LENGTH (il1_to_il2 e), tc', (il1_il2_val v)::stk, s'))``,
metis_tac [CLOCKED_IMP_UNCLOCKED_IL1, CORRECTNESS_THM, CLOCKED_IL1_EQUIV_BIMP]);

val dud_diverge_thm = prove(``!e s.(!c.bs_il1_c c (e, s) NONE) ==> !tc stk. exec_clocked (il1_to_il2 e) (SOME (0, tc, stk, s)) NONE``, cheat);

val expr_doesnt_tick = prove(``!c p p'.bs_il1_c_expr c p p' ==> (p' <> NONE) ==> (SND (THE p') = c)``,
ho_match_mp_tac bs_il1_c_expr_strongind THEN rw []);

val lem1 = prove(``!e s.(?c r.bs_il1_c c (e, s) (SOME r)) <=> ~(!c.bs_il1_c c (e, s) NONE)``, cheat);
val expr_never_none = prove(``!c p p'.bs_il1_c_expr c p p' ==> (c <> 0) ==> (p' <> NONE)``,
ho_match_mp_tac bs_il1_c_expr_strongind THEN rw [] THEN CCONTR_TAC THEN fs [] THEN rw [] THEN imp_res_tac expr_doesnt_tick THEN fs []);

val lem2 = prove(``!p stk s.(?c c' stk' s' r.exec_clocked p (SOME (0, c, stk, s)) (SOME (&LENGTH p, c', stk', s') )) <=> ~(!c.exec_clocked p (SOME (0, c, stk, s)) NONE)``, cheat);

val lem3 = prove(``!e s.(!v s'.~bs_il1 (e, s) v s') <=> ~(?c r.bs_il1_c c (e, s) (SOME r))``,
rw [EQ_IMP_THM]

THEN CCONTR_TAC THEN fs []

THEN1 (imp_res_tac CLOCKED_IMP_UNCLOCKED_IL1
THEN Cases_on `r` THEN Cases_on `r'`
THEN fs [] THEN metis_tac [])

THEN imp_res_tac UNCLOCKED_IMP_CLOCKED_IL1
THEN metis_tac []);

val bs_il1_c_det_thm = prove(``!c p r r'.bs_il1_c c p r /\ bs_il1_c c p r' ==> (r = r')``, cheat);

val lem4 = prove(``!e s.(!c.bs_il1_c c (e, s) NONE) ==> (!v s'.¬bs_il1 (e, s) v s')``, rw [] THEN CCONTR_TAC THEN fs [] THEN rw []

THEN imp_res_tac UNCLOCKED_IMP_CLOCKED_IL1

THEN `∃cl. bs_il1_c (SUC cl) (e,s) (SOME (v,s',SUC 0))` by metis_tac []
THEN `bs_il1_c (SUC cl) (e,s) NONE` by metis_tac []
THEN `SOME (v, s', SUC 0) = NONE` by metis_tac [bs_il1_c_det_thm]
THEN fs []);

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
