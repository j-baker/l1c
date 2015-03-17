open HolKernel boolLib bossLib listTheory Parse IndDefLib finite_mapTheory relationTheory arithmeticTheory pred_setTheory pairTheory lcsymtacs integerTheory ast_il2Theory smallstep_il2Theory smallstep_il2_clockedTheory;

val _ = new_theory "il2_composition";


val FETCH_SUC_THM = store_thm("FETCH_SUC_THM",
``!x xs i.(i >= 0) ==> (xs !! i = (x::xs) !! (i+1))``,
rw [fetch_def] THEN1
full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss) []
THEN `i + 1 - 1 = i` by full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss) [] THEN rw []);

val fsa = full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss);
val rwa = full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss);

val fetch_append_thm = store_thm("fetch_append_thm",
``!i xs ys.(&0 <= i) ==> ((xs ++ ys) !! i = (if i < &LENGTH xs then xs !! i else ys !! (i - &LENGTH xs)))``,
Induct_on `xs` THEN rw []

THEN1 metis_tac [int_le]

THEN1 (Cases_on `i = 0` THEN rw [APPEND, fetch_def]

THEN `xs ++ ys !! (i-1) = xs !! (i-1)` by (`0 <= (i-1)` by fsa [] THEN `i - 1 < &LENGTH xs` by fsa [] THEN metis_tac []))

THEN fsa [INT_NOT_LT]

THEN `~(i-1 < &LENGTH xs)` by fsa []
THEN `xs ++ ys !! (i-1) = ys !! (i-1) - &LENGTH xs` by (fsa [])

THEN Cases_on `i = 0` THEN fsa [APPEND, fetch_def] THEN rw []
THEN fsa [INT]
THEN `i - 1 - &LENGTH xs = i - (&LENGTH xs + 1)` by fsa [INT, INT_SUB_LNEG, INT_ADD_COMM]
THEN rw []);

val LIST_APPEND_THM = store_thm("LIST_APPEND_THM",
``!xs.(xs ++ [] = xs)``,
rw [APPEND]);


val FETCH_RANGE_THM = store_thm("FETCH_RANGE_THM",
``!xs.&LENGTH xs > 0 ==> !n.(n >= &0) /\ (n < &(LENGTH xs)) ==> ?x.(xs !! n = x)``,
rw []);

val APPEND_TRACE_SAME_THM = store_thm("APPEND_TRACE_SAME_THM",
``!P c c'.exec_clocked P c c' ==> !P'.exec_clocked (P ++ P') c c'``,
fs [exec_clocked_def] THEN strip_tac THEN ho_match_mp_tac RTC_STRONG_INDUCT_RIGHT1 THEN rw []
THEN fs [Once exec_clocked_one_cases]
THEN rw []

THEN match_mp_tac (GEN_ALL(CONJUNCT2 (SPEC_ALL (REWRITE_RULE [EQ_IMP_THM] RTC_CASES_RTC_TWICE))))
THEN Q.EXISTS_TAC `SOME (pc, clk, stk, st)` THEN rw []
THEN match_mp_tac RTC_SUBSET THEN rwa [exec_clocked_one_cases] THEN rwa [fetch_append_thm]);

val incr_pc_def = Define `(incr_pc (SOME (i, clk, s, stk)) (i':int) = SOME (i + i', clk, s, stk)) /\ (incr_pc NONE _ = NONE)`;

val CHANGE_PC_INSTR_THM = store_thm("CHANGE_PC_INSTR_THM",
``!n x pc clk s stk pc' clk' s' stk'.exec_clocked_instr x (SOME (pc, clk, s, stk)) (SOME (pc', clk', s', stk')) <=> exec_clocked_instr x (SOME (n + pc, clk, s, stk)) (SOME (n + pc', clk', s', stk'))``,
Cases_on `x` THEN rwa [EQ_IMP_THM, exec_clocked_instr_cases] THEN Cases_on `s` THEN fsa [exec_clocked_instr_cases] THEN rw[] THEN rwa []);

val APPEND_TRACE_SAME_2_THM = store_thm("APPEND_TRACE_SAME_2_THM",
``!P c c'.exec_clocked P c c' ==> !P'.exec_clocked (P' ++ P) (incr_pc c (&LENGTH P')) (incr_pc c' (&LENGTH P'))``,
fs [exec_clocked_def] THEN strip_tac
THEN ho_match_mp_tac RTC_STRONG_INDUCT_RIGHT1 THEN rw [] THEN Cases_on `c` THEN Cases_on `c'` THEN Cases_on `c''` THEN fs [Once exec_clocked_one_cases] THEN rw [] THEN fs [incr_pc_def] THEN rw []

THEN (TRY (Cases_on `x` THEN Cases_on `r` THEN Cases_on `r'`)) THEN (TRY (Cases_on `x''` THEN Cases_on `r'` THEN Cases_on `r''`)) THEN (TRY (Cases_on `x'` THEN Cases_on `r'` THEN Cases_on `r''`))

THEN1 (imp_res_tac RTC_CASES1 THEN fs [Once exec_clocked_one_cases, exec_clocked_instr_cases])


THEN1 (Cases_on `P !! pc` THEN fs [Once exec_clocked_instr_cases] THEN rw []
THEN fs [incr_pc_def] THEN match_mp_tac (GEN_ALL(CONJUNCT2 (SPEC_ALL (REWRITE_RULE [EQ_IMP_THM] RTC_CASES2)))) THEN rw [] THEN Q.EXISTS_TAC `SOME (pc + &LENGTH P', 0, stk, st)` THEN rw [] THEN rwa [exec_clocked_one_cases, exec_clocked_instr_cases, fetch_def, fetch_append_thm, INT_SUB_CALCULATE, INT_ADD_RINV, GSYM INT_ADD_ASSOC])

THEN match_mp_tac (GEN_ALL(CONJUNCT2 (SPEC_ALL (REWRITE_RULE [EQ_IMP_THM] RTC_CASES2)))) THEN rw [] THEN DISJ2_TAC THEN Q.EXISTS_TAC `SOME (pc + &LENGTH P', clk, stk, st)` THEN rwa [exec_clocked_one_cases] THEN rwa [fetch_append_thm, INT_SUB_CALCULATE, INT_ADD_RINV, GSYM INT_ADD_ASSOC, incr_pc_def] THEN Cases_on `P !! pc` THEN fsa [exec_clocked_instr_cases]);

val EXECUTION_COMPOSE_THM = store_thm("EXECUTION_COMPOSE_THM",
``!P P' clk stk st i' clk' stk' st' i'' clk'' stk'' st''.exec_clocked P (SOME (0, clk, stk, st)) (SOME (i', clk', stk', st')) /\ (&LENGTH P <= i') /\ exec_clocked 
P' (SOME (i' - &LENGTH P, clk', stk', st')) (SOME (i'', clk'', stk'', st'')) ==> exec_clocked (P ++ P') (SOME (0, clk, stk, st)) (SOME (&LENGTH P + i'', clk'', stk'', st''))``,
rw [] THEN fs [exec_clocked_def]

THEN match_mp_tac (GEN_ALL(CONJUNCT2 (SPEC_ALL (REWRITE_RULE [EQ_IMP_THM] RTC_CASES_RTC_TWICE))))

THEN fs [GSYM exec_clocked_def]

THEN Q.EXISTS_TAC `SOME (i', clk', stk', st')` THEN rw [] THEN1 metis_tac [APPEND_TRACE_SAME_THM]

THEN fs [INT_SUB_CALCULATE, INT_ADD_RINV, GSYM INT_ADD_ASSOC]

THEN imp_res_tac APPEND_TRACE_SAME_2_THM

THEN fs [incr_pc_def, GSYM INT_ADD_ASSOC, INT_ADD_COMM] THEN metis_tac [INT_ADD_RINV, INT_ADD_LID, INT_ADD_COMM]);

val EX_COM_THM = store_thm("EX_COM_THM",
``!P P' clk stk st clk' stk' st' clk'' stk'' st''.exec_clocked P (SOME (0, clk, stk, st)) (SOME (&LENGTH P, clk', stk', st')) /\ exec_clocked P' (SOME (0, clk', stk', st')) (SOME (&LENGTH P', clk'', stk'', st'')) ==> exec_clocked (P ++ P') (SOME (0, clk, stk, st)) (SOME (&LENGTH P + &LENGTH P', clk'', stk'', st''))``,
mp_tac EXECUTION_COMPOSE_THM
THEN rw []
THEN `&LENGTH P <= &LENGTH P` by metis_tac [INT_LE_REFL]
THEN `&LENGTH P - &LENGTH P = 0` by rwa []
THEN metis_tac [EXECUTION_COMPOSE_THM, INT_LE_REFL]);

val _ = export_theory ();
