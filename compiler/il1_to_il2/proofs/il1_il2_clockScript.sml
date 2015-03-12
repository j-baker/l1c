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

val type_means_expr_reduces = prove(``!e g t.il1_expr_type e g t ==> !s.(g ⊆ FDOM s) ==> !c.?r.bs_il1_c_expr c (e, s) r``,
ho_match_mp_tac il1_expr_type_strongind THEN rw []
THEN Cases_on `c`
THEN (TRY (rw [Once bs_il1_c_expr_cases]THEN metis_tac []))

THEN (TRY (Cases_on `l` THEN fs [] THENL [`User n' ∈ FDOM s` by metis_tac [SUBSET_DEF], `Compiler n' ∈ FDOM s` by metis_tac [SUBSET_DEF]]
THEN rw [Once bs_il1_c_expr_cases]))

THEN `?r.bs_il1_c_expr (SUC n) (e,s) r` by metis_tac []

THEN( Cases_on `r` 
THEN1 (`NONE <> NONE` by metis_tac [SUC_NOT, expr_never_none] THEN fs [])
THEN Cases_on `x`
THEN `SOME (q, r) <> NONE` by fs []
THEN `SND (THE (SOME (q, r))) = SUC n` by metis_tac [expr_doesnt_tick]
THEN fs [SND, THE_DEF] THEN rw [])

THEN `?r.bs_il1_c_expr (SUC n) (e',s) r` by metis_tac []

THEN (Cases_on `r` 
THEN1 (`NONE <> NONE` by metis_tac [SUC_NOT, expr_never_none] THEN fs [])
THEN Cases_on `x`
THEN `SOME (q', r) <> NONE` by fs []
THEN `SND (THE (SOME (q', r))) = SUC n` by metis_tac [expr_doesnt_tick]
THEN fs [SND, THE_DEF] THEN rw [])

THEN (TRY (
`?r.bs_il1_c_expr (SUC n) (e'',s) r` by metis_tac []

THEN (Cases_on `r` 
THEN1 (`NONE <> NONE` by metis_tac [SUC_NOT, expr_never_none] THEN fs [])
THEN Cases_on `x`
THEN `SOME (q'', r) <> NONE` by fs []
THEN `SND (THE (SOME (q'', r))) = SUC n` by metis_tac [expr_doesnt_tick]
THEN fs [SND, THE_DEF] THEN rw [])))

THEN rw [Once bs_il1_c_expr_cases]

THEN1 (
`?a.q = IL1_Integer a` by cheat
THEN `?b.q' = IL1_Integer b` by cheat
THEN rw []
THEN metis_tac [])

THEN1 (
`?a.q = IL1_Integer a` by cheat
THEN `?b.q' = IL1_Integer b` by cheat
THEN rw []
THEN metis_tac [])

THEN1 (
`?a.q = IL1_Boolean a` by cheat
THEN rw []
THEN Cases_on `a` THEN metis_tac [])

);

val type_imp_reduces = prove(``!e g t g'.il1_type e g t g' ==> !s.(g' ⊆ FDOM s) /\ (g ⊆ FDOM s) ==> !c.?r.bs_il1_c c (e, s) r``,
ho_match_mp_tac il1_type_strongind THEN (REVERSE (rw []))
THENL [ (Q.UNDISCH_TAC `g ⊆ FDOM s`
THEN Q.UNDISCH_TAC `g' ⊆ FDOM s`
THEN Q.SPEC_TAC (`s`, `s`)
THEN completeInduct_on `c` THEN rw []), all_tac, all_tac, all_tac, all_tac]
THEN Cases_on `c`
THEN (TRY (rw [Once bs_il1_c_cases]THEN metis_tac []))

THEN1 (`?r.bs_il1_c_expr n (e1, s) r` by metis_tac [IL1_TYPE_SUBSETS_THM, type_means_expr_reduces, SUBSET_TRANS]

THEN Cases_on `r` THEN1 (Q.EXISTS_TAC `NONE` THEN rw [Once bs_il1_c_cases]  THEN metis_tac []) THEN Cases_on `x`

THEN `?a.q = IL1_Boolean a` by cheat THEN rw []

THEN `n = r` by (`(SOME (IL1_Boolean a,r)) <> NONE` by fs [] THEN metis_tac [expr_doesnt_tick, SND, THE_DEF]) THEN rw []

THEN `?r'.bs_il1_c n (e, s) r'` by metis_tac []

THEN Cases_on `r'` THEN1 (Cases_on `a` THEN1 (Q.EXISTS_TAC `NONE` THEN rw [Once bs_il1_c_cases] THEN metis_tac []) THEN Q.EXISTS_TAC `SOME (IL1_ESkip, s, n)` THEN rw [Once bs_il1_c_cases] THEN metis_tac [])

THEN Cases_on `x`
THEN Cases_on `r`
THEN `q = IL1_ESkip` by cheat THEN rw []

THEN (REVERSE (Cases_on `a`)) THEN1 (Q.EXISTS_TAC `SOME (IL1_ESkip, s, n)` THEN rw [Once bs_il1_c_cases] THEN metis_tac [])

THEN `g' ⊆ FDOM q'` by cheat
THEN `g ⊆ FDOM q'` by cheat

THEN `r' <= n` by cheat

THEN `?r.bs_il1_c r' (IL1_While e1 e, q') r` by metis_tac [LESS_EQ_IMP_LESS_SUC]

THEN Cases_on `r` THEN1 (Q.EXISTS_TAC `NONE` THEN rw [Once bs_il1_c_cases] THEN metis_tac []) THEN Cases_on `x` THEN Cases_on `r`

THEN `q = IL1_ESkip` by cheat THEN rw []

THEN rw [Once bs_il1_c_cases] THEN metis_tac [])

THEN1 (`?r. bs_il1_c_expr (SUC n) (e1,s) r` by metis_tac [type_means_expr_reduces]
THEN Cases_on `r` THEN1 (Q.EXISTS_TAC `NONE` THEN rw [Once bs_il1_c_cases] THEN metis_tac []) THEN Cases_on `x`

THEN `?b.q = IL1_Boolean b` by cheat THEN rw []

THEN Cases_on `b` THENL [`?r'.bs_il1_c r (e, s) r'` by metis_tac [], `?r'.bs_il1_c r (e', s) r'` by metis_tac []] THEN
(Cases_on `r'` THEN1 (Q.EXISTS_TAC `NONE` THEN rw [Once bs_il1_c_cases] THEN metis_tac []) THEN Cases_on `x` THEN Cases_on `r'`

THEN rw [Once bs_il1_c_cases] THEN metis_tac []))

THEN1 (
`g' ⊆ FDOM s` by metis_tac [IL1_TYPE_SUBSETS_THM, SUBSET_DEF]
THEN `?r. bs_il1_c (SUC n) (e,s) r` by metis_tac []
THEN Cases_on `r` THEN1 (Q.EXISTS_TAC `NONE` THEN rw [Once bs_il1_c_cases] THEN metis_tac [])
THEN Cases_on `x` THEN Cases_on `r`

THEN `q = IL1_ESkip` by cheat THEN rw []
THEN `FDOM s ⊆ FDOM q'` by cheat
THEN `?r.bs_il1_c r' (e', q') r` by metis_tac [SUBSET_DEF]
THEN Cases_on `r` THEN1 (Q.EXISTS_TAC `NONE` THEN rw [Once bs_il1_c_cases] THEN metis_tac [])
THEN Cases_on `x` THEN Cases_on `r`

THEN rw [Once bs_il1_c_cases] THEN metis_tac [])

THEN1 (`l ∈ FDOM s` by metis_tac [IN_INSERT]

THEN `?r.bs_il1_c_expr (SUC n) (e, s) r` by metis_tac [type_means_expr_reduces]

THEN Cases_on `r` THEN1 (Q.EXISTS_TAC `NONE` THEN rw [Once bs_il1_c_cases] THEN Cases_on `l` THEN metis_tac [])

THEN Cases_on `x`

THEN `?a.q = IL1_Integer a` by cheat
THEN rw []
THEN rw [Once bs_il1_c_cases]
THEN Q.EXISTS_TAC `SOME (IL1_ESkip, s |+ (l, a), r)` THEN rw [] THEN Cases_on `l` THEN rw [] THEN metis_tac [])

THEN1 (imp_res_tac type_means_expr_reduces
THEN `∃r. bs_il1_c_expr (SUC n) (e,s) r` by metis_tac []
THEN Cases_on `r`
THEN1 (Q.EXISTS_TAC `NONE` THEN rw [Once bs_il1_c_cases])

THEN rw [Once bs_il1_c_cases]
THEN Cases_on `x`
THEN Q.EXISTS_TAC `SOME (q, s, r)`
THEN metis_tac []));
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
