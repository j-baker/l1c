open HolKernel boolLib bossLib smallstep_vsm0_clockedTheory ast_vsm0Theory relationTheory lcsymtacs il2_compositionTheory integerTheory smallstep_il2Theory

val _ = new_theory "vsm_composition"


val fsa = full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss)
val rwa = full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss)


val APPEND_TRACE_SAME_VSM0_THM = store_thm("APPEND_TRACE_SAME_VSM0_THM",
``!P c c'.vsm_exec_c P c c' ==> !P'.vsm_exec_c (P ++ P') c c'``,
fs [vsm_exec_c_def] THEN strip_tac THEN ho_match_mp_tac RTC_STRONG_INDUCT_RIGHT1 THEN rw [] THEN fs [Once vsm_exec_c_one_cases]
THEN match_mp_tac (GEN_ALL (CONJUNCT2 (SPEC_ALL (REWRITE_RULE [EQ_IMP_THM] RTC_CASES_RTC_TWICE)))) THEN Q.EXISTS_TAC `SOME (pc, clk, stk)` THEN rw []
THEN match_mp_tac RTC_SUBSET THEN rwa [vsm_exec_c_one_cases] THEN rwa [fetch_append_thm])



val incr_pc_vsm0_def = Define `(incr_pc_vsm0 (SOME (i, clk, stk)) (i':int) = SOME (i + i', clk, stk)) /\ (incr_pc_vsm0 NONE _ = NONE)`

val APPEND_TRACE_SAME_2_VSM0_THM = store_thm("APPEND_TRACE_SAME_2_VSM0_THM",
``!P c c'.vsm_exec_c P c c' ==> !P'.vsm_exec_c (P' ++ P) (incr_pc_vsm0 c (&LENGTH P')) (incr_pc_vsm0 c' (&LENGTH P'))``,
fs [vsm_exec_c_def] THEN strip_tac THEN ho_match_mp_tac RTC_STRONG_INDUCT_RIGHT1 THEN rw [] THEN Cases_on `c` THEN Cases_on `c'` THEN Cases_on `c''` THEN fs [Once vsm_exec_c_one_cases] THEN rw [] THEN fs [incr_pc_vsm0_def] THEN rw []

THEN Cases_on `P !! pc` THEN fs [vsm_exec_c_instr_cases] THEN rw [] THEN
(TRY (imp_res_tac RTC_CASES1 THEN fsa [vsm_exec_c_one_cases] THEN rw [] THEN FAIL_TAC "foo"))

THEN Cases_on `x` THEN Cases_on `r` THEN fs [incr_pc_vsm0_def] THEN

 match_mp_tac (GEN_ALL(CONJUNCT2 (SPEC_ALL (REWRITE_RULE [EQ_IMP_THM] RTC_CASES2)))) THEN rw [] THEN (TRY (DISJ2_TAC)) THEN fs [incr_pc_vsm0_def]


THENL (map Q.EXISTS_TAC [`SOME (pc + &LENGTH P', 0, stk)`, `SOME (pc + &LENGTH P', clk, stk)`, `SOME (pc + &LENGTH P', SUC c, stk)`, `SOME (pc + &LENGTH P', clk, stk)`, `SOME (pc + &LENGTH P', clk, stk)`, `SOME (pc + &LENGTH P', clk, v::stk')`, `SOME (pc + &LENGTH P', clk, v::stk')`,  `SOME (pc + &LENGTH P', clk, v1::v2::stk')`, `SOME (pc + &LENGTH P', clk, v1::v2::stk')`, `SOME (pc + &LENGTH P', clk, v1::v2::stk')`, `SOME (pc + &LENGTH P', clk, stk)`, `SOME (pc + &LENGTH P', clk, 0::stk')`, `SOME (pc + &LENGTH P', clk, t::stk')`])

THEN rwa [vsm_exec_c_one_cases, vsm_exec_c_instr_cases, fetch_def, fetch_append_thm, INT_SUB_CALCULATE, INT_ADD_RINV, GSYM INT_ADD_ASSOC, true_value_def, false_value_def])

val _ = export_theory ()
