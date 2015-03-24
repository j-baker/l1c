open ast_il2Theory smallstep_il2Theory smallstep_il2_clockedTheory HolKernel Parse boolLib bossLib integerTheory finite_mapTheory lcsymtacs pairTheory relationTheory


val _ = new_theory "clocked_il2_equiv"

val fsa = full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss)
val rwa = rw_tac (srw_ss () ++ intSimps.INT_ARITH_ss)

val exec_imp_clocked = prove(``
!P c c'.exec P c c' ==> !clk'.?clk.exec_clocked P (SOME (FST c, clk, FST (SND c), SND (SND c))) (SOME (FST c', SUC clk', FST (SND c'), SND (SND c')))``,

fs [exec_def] THEN STRIP_TAC THEN ho_match_mp_tac RTC_STRONG_INDUCT THEN rw []

THEN Cases_on `c` THEN Cases_on `r` THEN (TRY (Cases_on `c'` THEN Cases_on `r`)) THEN (TRY (Cases_on `c''` THEN Cases_on `r`)) THEN fs [FST, SND] THEN rw []

THEN1 metis_tac [exec_clocked_def, RTC_REFL]

THEN fs [exec_clocked_def] THEN rw [Once RTC_CASES1]

THEN fs [exec_clocked_one_cases, exec_one_cases] THEN Cases_on `P !! q` THEN fs [exec_clocked_instr_cases, exec_instr_cases] THEN rw [] THEN metis_tac [])

val clocked_imp_exec = prove(``
!P c c'.exec_clocked P c c' ==> !pc clk stk st pc' clk' stk' st'.(c = SOME (pc, clk, stk, st)) /\ (c' = SOME (pc', clk', stk', st')) ==> exec P (pc, stk, st) (pc', stk', st')``,

fs [exec_clocked_def] THEN STRIP_TAC THEN ho_match_mp_tac RTC_STRONG_INDUCT THEN rw []

THEN1 metis_tac [exec_def, RTC_REFL]

THEN Cases_on `c'`

THEN1 fs [Once RTC_CASES1, exec_clocked_one_cases]

THEN Cases_on `x` THEN Cases_on `r` THEN Cases_on `r'` THEN fs [] THEN rw []

THEN fs [exec_def] THEN rw [Once RTC_CASES1] THEN fs [exec_clocked_one_cases, exec_one_cases] THEN Cases_on `P !! pc` THEN fs [exec_clocked_instr_cases, exec_instr_cases] THEN rw [] THEN metis_tac [])

val CLOCKED_IL1_EQUIV_BIMP = store_thm("CLOCKED_IL1_EQUIV_BIMP",
``!P pc stk st pc' stk' st'. exec P (pc, stk, st) (pc', stk', st') <=> ?clk clk'. exec_clocked P (SOME (pc, clk, stk, st)) (SOME (pc', clk', stk', st'))``,
metis_tac [EQ_IMP_THM, clocked_imp_exec, exec_imp_clocked, FST, SND])

val clocked_il1_once_det = prove(``
!P c c' c''.exec_clocked_one P c c' /\ exec_clocked_one P c c'' ==> (c' = c'')``,

rw [] THEN fs [exec_clocked_one_cases] THEN rw [] THEN Cases_on `P !! pc` THEN fs [exec_clocked_instr_cases] THEN rw [] THEN metis_tac [int_ge, INT_NOT_LE])


val clocked_il1_det = prove(``!P c c'.exec_clocked P c c' ==> !c''.exec_clocked P c c'' ==> exec_clocked P c' c'' \/ exec_clocked P c'' c'``,
fs [exec_clocked_def] THEN STRIP_TAC THEN ho_match_mp_tac RTC_STRONG_INDUCT THEN rw [] THEN fs [Once RTC_CASES1] THEN rw [] THEN imp_res_tac clocked_il1_once_det THEN rw [] THEN metis_tac [RTC_CASES1])


val none_imp_no_result = prove(
``!P pc stk st. (!clk.exec_clocked P (SOME (pc, clk, stk, st)) NONE) ==> ~?stk' st'.exec P (pc, stk, st) (&LENGTH P, stk', st')``,
CCONTR_TAC THEN fs []

THEN imp_res_tac exec_imp_clocked

THEN fs [FST, SND]

THEN `?clk.exec_clocked P (SOME (pc,clk,stk,st))
                 (SOME (&LENGTH P,SUC 0,stk',st'))` by metis_tac []

THEN `exec_clocked P (SOME (pc, clk, stk, st)) NONE` by metis_tac []

THEN fs [GSYM exec_clocked_def] THEN imp_res_tac clocked_il1_det THEN fs [exec_clocked_def, Once RTC_CASES1, exec_clocked_one_cases])

val _ = export_theory ()
