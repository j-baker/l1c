open HolKernel boolLib bossLib smallstep_vsm0_clockedTheory ast_vsm0Theory relationTheory lcsymtacs il2_compositionTheory

val _ = new_theory "vsm_composition"


val fsa = full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss)
val rwa = full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss)


val APPEND_TRACE_SAME_VSM0_THM = store_thm("APPEND_TRACE_SAME_VSM0_THM",
``!P c c'.vsm_exec_c P c c' ==> !P'.vsm_exec_c (P ++ P') c c'``,
fs [vsm_exec_c_def] THEN strip_tac THEN ho_match_mp_tac RTC_STRONG_INDUCT_RIGHT1 THEN rw [] THEN fs [Once vsm_exec_c_one_cases]
THEN match_mp_tac (GEN_ALL (CONJUNCT2 (SPEC_ALL (REWRITE_RULE [EQ_IMP_THM] RTC_CASES_RTC_TWICE)))) THEN Q.EXISTS_TAC `SOME (pc, clk, stk)` THEN rw []
THEN match_mp_tac RTC_SUBSET THEN rwa [vsm_exec_c_one_cases] THEN rwa [fetch_append_thm])




val _ = export_theory ()
