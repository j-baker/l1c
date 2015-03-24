open HolKernel boolLib bossLib l1_to_il1_compilerTheory il1_to_il2_compilerTheory store_creationTheory il1_il2_correctnessTheory l1_il1_correctnessTheory lcsymtacs il2_to_il3_compilerTheory listTheory pairTheory pred_setTheory l1_il1_totalTheory bigstep_il1Theory ast_l1Theory store_equivalenceTheory finite_mapTheory il3_to_vsm0_correctnessTheory il3_store_propertiesTheory il2_il3_correctnessTheory bs_ss_equivalenceTheory smallstep_vsm0_clockedTheory bigstep_il1_clockedTheory bigstep_l1_clockedTheory l1_typeTheory clocked_equivTheory compilerTheory relationTheory integerTheory vsm0_clocked_equivTheory;

val _ = new_theory "divergence_preservation"

val domain_constant_thm = prove(``
!c p r.bs_l1_c c p r ==> !v s' c'.(r = SOME (v, s', c')) ==> (FDOM (SND p) = FDOM s')``,
ho_match_mp_tac bs_l1_c_strongind THEN rw [] THEN fs [FST, SND] THEN rw [EXTENSION] THEN Cases_on `x=l` THEN rw []);

val while_back_thm = prove(``!e1 e2 s s''' v cl cl'''.bs_l1_c cl (L1_While e1 e2, s) (SOME (v, s''', cl''')) ==> (v = L1_Skip) /\ ((bs_l1_c cl (e1, s) (SOME (L1_Bool F, s''', cl'''))) \/ (?cl' s' s'' cl''.bs_l1_c cl (e1, s) (SOME (L1_Bool T, s', cl')) /\ bs_l1_c cl' (e2, s') (SOME (L1_Skip, s'', SUC cl'')) /\ bs_l1_c cl'' (L1_While e1 e2, s'') (SOME (L1_Skip, s''', cl'''))))``,
rw [Once bs_l1_c_cases] THEN metis_tac []);

val l1_deterministic = prove(``!c p r.bs_l1_c c p r ==> !r'. bs_l1_c c p r' ==> (r = r')``,
ho_match_mp_tac bs_l1_c_strongind THEN rw []
THEN1 (Cases_on `v` THEN fs [Once bs_l1_c_cases])
THEN fs [Q.SPECL [`A`, `L1_Plus B C, D`] bs_l1_c_cases, Q.SPECL [`A`, `L1_Geq B C, D`] bs_l1_c_cases, Q.SPECL [`A`, `L1_Deref B, D`] bs_l1_c_cases, Q.SPECL [`A`, `L1_Assign B C, D`] bs_l1_c_cases, Q.SPECL [`A`, `L1_Seq B C, D`] bs_l1_c_cases, Q.SPECL [`A`, `L1_If A B C, D`] bs_l1_c_cases] THEN (NTAC 3 (res_tac THEN fs [] THEN rw [])) THEN 
(NTAC 3 (res_tac THEN fs [] THEN rw []))

THEN Cases_on `r'` THEN fs [Once (Q.SPECL [`A`, `L1_While B C, D`, `NONE`] bs_l1_c_cases)] THEN (TRY (Cases_on `x` THEN Cases_on `r`))

THEN imp_res_tac while_back_thm THEN (NTAC 3 (res_tac THEN fs [] THEN rw [])));

val type_means_value_type = prove(``
!c p r.bs_l1_c c p r ==> !v s' c'.(r = SOME (v, s', c')) ==> !g t.l1_type (FST p) g t ==> !s.(g ⊆ FDOM (SND p)) ==> ((t = intL1) /\ (?n.v = L1_Int n)) \/ ((t = boolL1) /\ (?b.v = L1_Bool b)) \/ ((t = unitL1) /\ (v = L1_Skip))``,

ho_match_mp_tac bs_l1_c_strongind THEN rw []

THEN1 (Cases_on `v` THEN fs [Once l1_type_cases])

THEN Cases_on `t` THEN (NTAC 3 ((TRY (`FDOM s = FDOM s'` by metis_tac [domain_constant_thm, SND])) THEN (TRY (`FDOM s' = FDOM s''` by metis_tac [domain_constant_thm, SND])) THEN res_tac THEN fs [Q.SPEC `L1_Plus A B`(Once l1_type_cases), Q.SPEC `L1_Geq A B`(Once l1_type_cases), Q.SPEC `L1_Deref A`(Once l1_type_cases), Q.SPEC `L1_Assign A B`(Once l1_type_cases), Q.SPEC `L1_Seq A B`(Once l1_type_cases), Q.SPEC `L1_If A B C`(Once l1_type_cases), Q.SPEC `L1_While A B`(Once l1_type_cases)] THEN rw [])));

val l1_clock_decreasing = prove(``!c p r.bs_l1_c c p r ==> !v s' c'.(r = SOME (v, s', c')) ==> (c' <= c)``,
ho_match_mp_tac bs_l1_c_strongind THEN rw [] THEN rw [Once bs_l1_c_cases] THEN decide_tac);

val closer = imp_res_tac type_means_value_type THEN res_tac THEN rw [] THEN res_tac THEN fs [] THEN rw [] THEN (TRY (Cases_on `b`)) THEN metis_tac [SUBSET_DEF];

val type_means_reduces = prove(``
!e g t.l1_type e g t ==> !s.(g ⊆ FDOM s) ==> !c.?r.bs_l1_c c (e, s) r
``,
ho_match_mp_tac l1_type_strongind THEN rw []

THEN1 rw [Once bs_l1_c_cases]
THEN1 rw [Once bs_l1_c_cases] 
THEN1 rw [Once bs_l1_c_cases]  

THEN1 (
rw [Once bs_l1_c_cases] THEN
`?r.bs_l1_c c (e, s) r` by metis_tac []
THEN Cases_on `r` THEN1 metis_tac [] THEN Cases_on `x` THEN Cases_on `r`
THEN `g ⊆ FDOM q'` by metis_tac [domain_constant_thm, SND]
THEN `?r.bs_l1_c r' (e', q') r` by metis_tac []
THEN Cases_on `r` THEN1 closer THEN Cases_on `x` THEN Cases_on `r`

THEN closer)

THEN1 (
rw [Once bs_l1_c_cases] THEN
`?r.bs_l1_c c (e, s) r` by metis_tac []
THEN Cases_on `r` THEN1 metis_tac [] THEN Cases_on `x` THEN Cases_on `r`
THEN `g ⊆ FDOM q'` by metis_tac [domain_constant_thm, SND]
THEN `?r.bs_l1_c r' (e', q') r` by metis_tac []
THEN Cases_on `r` THEN1 closer THEN Cases_on `x` THEN Cases_on `r`

THEN closer)

THEN1 (
rw [Once bs_l1_c_cases] THEN
`?r.bs_l1_c c (e, s) r` by metis_tac []
THEN Cases_on `r` THEN1 metis_tac [] THEN Cases_on `x` THEN Cases_on `r`
THEN `g ⊆ FDOM q'` by metis_tac [domain_constant_thm, SND]

THEN `?r.bs_l1_c r' (e', q') r` by metis_tac []
THEN `?r.bs_l1_c r' (e'', q') r` by metis_tac []
THEN Cases_on `r` THEN Cases_on `r''` THEN1 closer THEN Cases_on `x` THEN Cases_on `r`
THEN (TRY (Cases_on `x'` THEN Cases_on `r`))
THEN closer)

THEN1 (
rw [Once bs_l1_c_cases] THEN
`?r.bs_l1_c c (e, s) r` by metis_tac []
THEN Cases_on `r` THEN1 closer THEN Cases_on `x` THEN Cases_on `r` THEN closer)

THEN1 (rw [Once bs_l1_c_cases] THEN metis_tac [SUBSET_DEF])

THEN1 (
rw [Once bs_l1_c_cases] THEN
`?r.bs_l1_c c (e, s) r` by metis_tac []
THEN Cases_on `r` THEN1 metis_tac [] THEN Cases_on `x` THEN Cases_on `r`
THEN `g ⊆ FDOM q'` by metis_tac [domain_constant_thm, SND]
THEN `?r.bs_l1_c r' (e', q') r` by metis_tac []
THEN Cases_on `r` THEN1 closer THEN Cases_on `x` THEN Cases_on `r`

THEN closer)

THEN Q.UNDISCH_TAC `g ⊆ FDOM s`
THEN Q.SPEC_TAC (`s`, `s`)
THEN completeInduct_on `c` THEN rw []


THEN rw [Once bs_l1_c_cases] THEN
`?r.bs_l1_c c (e, s) r` by metis_tac []
THEN Cases_on `r` THEN1 metis_tac [] THEN Cases_on `x` THEN Cases_on `r`
THEN `g ⊆ FDOM q'` by metis_tac [domain_constant_thm, SND]
THEN `?r.bs_l1_c r' (e', q') r` by metis_tac []

THEN Cases_on `r` THEN1 closer THEN Cases_on `x` THEN Cases_on `r`

THEN Cases_on `r''` THEN1 closer

THEN `r' <= c` by (imp_res_tac l1_clock_decreasing THEN fs [])

THEN `SUC n <= r'` by (imp_res_tac l1_clock_decreasing THEN fs [])
THEN `n < c` by decide_tac
THEN `g ⊆ FDOM q'''` by metis_tac [domain_constant_thm, SND]
THEN `?r.bs_l1_c n (L1_While e e', q''') r` by metis_tac []

THEN Cases_on `r` THEN1 closer THEN Cases_on `x` THEN Cases_on `r` THEN `l1_type (L1_While e e') g unitL1` by metis_tac [l1_type_cases] THEN closer);

val lem1 = prove(``!e s g t.l1_type e g t /\ g ⊆ FDOM s ==> ~(!c.bs_l1_c c (e, s) NONE) ==> (?c r.bs_l1_c c (e, s) (SOME r))``,
rw []
THEN `?r.bs_l1_c c (e,s) r` by metis_tac [type_means_reduces, domain_constant_thm]
THEN Cases_on `r` THEN metis_tac []);

val vsm_exec_det = prove(``!P c c'.vsm_exec_c P c c' ==> !c''.vsm_exec_c P c c'' ==> vsm_exec_c P c' c'' \/ vsm_exec_c P c'' c'``,
STRIP_TAC THEN fs [vsm_exec_c_def] THEN ho_match_mp_tac RTC_STRONG_INDUCT THEN rw []

THEN `(c = c''') \/ ?u.(vsm_exec_c_one P) c u /\ (vsm_exec_c_one P)^* u c'''` by metis_tac [RTC_CASES1]

THEN rw [] THEN1 metis_tac [RTC_CASES1]

THEN fs [vsm_exec_c_one_cases] THEN rw [] THEN (`c' = u` by Cases_on `P !! pc` THEN fs [vsm_exec_c_instr_cases] THEN rw []) THEN fs [int_ge, GSYM INT_NOT_LT]);

val lem2 = prove(``!p stk s.(?c c' stk' r.vsm_exec_c p (SOME (0, c, stk)) (SOME (&LENGTH p, c', stk'))) ==> ~(!c.vsm_exec_c p (SOME (0, c, stk)) NONE)
``,
rw []

THEN CCONTR_TAC THEN fs []
THEN `vsm_exec_c p (SOME (0,c,stk)) NONE` by metis_tac []

THEN imp_res_tac vsm_exec_det THEN rw [] THEN fs [vsm_exec_c_def] THEN imp_res_tac RTC_CASES1 THEN fs [vsm_exec_c_one_cases]);

val lem3 = prove(``!e s.(!v s'.~bs_l1 (e, s) v s') <=> ~(?c r.bs_l1_c c (e, s) (SOME r))``,
rw [EQ_IMP_THM]

THEN CCONTR_TAC THEN fs []

THEN1 (imp_res_tac CLOCKED_IMP_UNCLOCKED
THEN Cases_on `r` THEN Cases_on `r'`
THEN fs [] THEN metis_tac [])

THEN imp_res_tac UNCLOCKED_IMP_CLOCKED
THEN metis_tac []);

val lem4 = prove(``!e s.(!c.bs_l1_c c (e, s) NONE) ==> (!v s'.¬bs_l1 (e, s) v s')``, rw [] THEN CCONTR_TAC THEN fs [] THEN rw []

THEN imp_res_tac UNCLOCKED_IMP_CLOCKED

THEN `∃cl. bs_l1_c (SUC cl) (e,s) (SOME (v,s',SUC 0))` by metis_tac []
THEN `bs_l1_c (SUC cl) (e,s) NONE` by metis_tac []

THEN imp_res_tac l1_deterministic
THEN fs []);

val cor_oneway = prove(``
!e g t.l1_type e g t /\ g ⊆ FDOM (create_store e) ==> (~?v s'.bs_l1 (e, create_store e) v s') ==> ~?stk' s'.vsm_exec (full_compile e) (0, []) (&LENGTH (full_compile e), stk')``,
rw []

THEN `!c.bs_l1_c c (e, create_store e) NONE` by metis_tac [lem1, lem3]

THEN `!c.vsm_exec_c (full_compile e) (SOME (0,c,[])) NONE` by metis_tac [total_c_lem_1]

THEN CCONTR_TAC THEN fs []

THEN imp_res_tac VSM0_UNCLOCKED_IMP_CLOCKED

THEN fs [FST, SND]

THEN metis_tac [lem2]);

val DIVERGENCE_PRESERVATION = store_thm("DIVERGENCE_PRESERVATION", ``!e g t.l1_type e g t /\ g ⊆ FDOM (create_store e) ==> ((~?v s'. bs_l1 (e, create_store e) v s') <=> (~?stk' s'.vsm_exec (full_compile e) (0, []) (&LENGTH (full_compile e), stk')))``,
metis_tac [EQ_IMP_THM, cor_oneway, CORRECTNESS_THM]);

val _ = export_theory ();
