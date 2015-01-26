open HolKernel boolLib bossLib listTheory Parse IndDefLib finite_mapTheory relationTheory arithmeticTheory pred_setTheory pairTheory lcsymtacs integerTheory ast_il2Theory smallstep_il2Theory;

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
``!P c c'.exec P c c' ==> !P'.exec (P ++ P') c c'``,
fs [exec_def] THEN strip_tac THEN ho_match_mp_tac exec_strongind_right THEN rw []
THEN fs [Once exec_one_cases]

THEN `(exec_one (P ++ P'))^* c (pc, stk, st)` by metis_tac []
THEN `exec_instr ((P ++ P') !! pc) (pc, stk, st) (pc', stk', st')` by metis_tac [fetch_append_thm, int_ge]
THEN `(exec_one (P ++ P')) (pc, stk, st) (pc', stk', st')` by rwa [exec_one_cases]
THEN rw [Once RTC_CASES2] THEN metis_tac []);

val incr_pc_def = Define `incr_pc (i, s, stk) (i':int) = (i + i', s, stk)`;

val CHANGE_PC_INSTR_THM = store_thm("CHANGE_PC_INSTR_THM",
``!n x pc s stk pc' s' stk'.exec_instr x (pc, s, stk) (pc', s', stk') <=> exec_instr x (n + pc, s, stk) (n + pc', s', stk')``,
Cases_on `x` THEN rwa [EQ_IMP_THM, exec_instr_cases] THEN Cases_on `s` THEN fsa [exec_instr_cases] THEN rw[] THEN rwa []);

val APPEND_TRACE_SAME_2_THM = store_thm("APPEND_TRACE_SAME_2_THM",
``!P c c'.exec P c c' ==> !P'.exec (P' ++ P) (incr_pc c (&LENGTH P')) (incr_pc c' (&LENGTH P'))``,
fs [exec_def] THEN strip_tac
THEN ho_match_mp_tac exec_strongind_right THEN rw [] THEN Cases_on `c` THEN Cases_on `c'` THEN Cases_on `c''` THEN fs [Once exec_one_cases] THEN rw [] THEN fs [incr_pc_def] THEN rw []


THEN `exec_instr ((P' ++ P) !! (q' + &LENGTH P')) (&LENGTH P' + q', stk, st) (&LENGTH P' + q'', stk', st')` by (

`P' ++ P !! q' + &LENGTH P' = P !! q'` by (

`0 <= q' + &LENGTH P'` by fsa [int_ge]
THEN fsa [fetch_append_thm]
THEN `q' + &LENGTH P' - &LENGTH P' = q'` by fsa []
THEN metis_tac [])

THEN metis_tac [CHANGE_PC_INSTR_THM])

THEN Cases_on `r` THEN fs [incr_pc_def]

THEN rw [Once RTC_CASES2]

THEN `exec_one (P' ++ P) (q' + &LENGTH P', stk, st) (q'' + &LENGTH P', stk', st')` by rw [exec_one_cases] THEN fsa [] THEN metis_tac [INT_ADD_COMM]);

val EXECUTION_COMPOSE_THM = store_thm("EXECUTION_COMPOSE_THM",
``!P P' stk st i' stk' st' i'' stk'' st''.exec P (0, stk, st) (i', stk', st') /\ (&LENGTH P <= i') /\ exec 
P' (i' - &LENGTH P, stk', st') (i'', stk'', st'') ==> exec (P ++ P') (0, stk, st) (&LENGTH P + i'', stk'', st'')``,
rw []

THEN `(exec (P ++ P')) (0, stk, st) (i', stk', st')` by fsa [APPEND_TRACE_SAME_THM]

THEN `(exec (P ++ P')) (incr_pc (i' - &LENGTH P,stk',st') (&LENGTH P)) (incr_pc (i'',stk'',st'') (&LENGTH P))` by fsa [APPEND_TRACE_SAME_2_THM]

THEN fsa [incr_pc_def]

THEN fsa [exec_def, INT_ADD_COMM]
THEN metis_tac [RTC_TRANSITIVE, transitive_def]);

val EX_COM_THM = store_thm("EX_COM_THM",
``!P P' stk st stk' st' stk'' st''.exec P (0, stk, st) (&LENGTH P, stk', st') /\ exec P' (0, stk', st') (&LENGTH P', stk'', st'') ==> exec (P ++ P') (0, stk, st) (&LENGTH P + &LENGTH P', stk'', st'')``,
mp_tac EXECUTION_COMPOSE_THM
THEN rw []
THEN `&LENGTH P <= &LENGTH P` by metis_tac [INT_LE_REFL]
THEN `&LENGTH P - &LENGTH P = 0` by rwa []
THEN metis_tac [EXECUTION_COMPOSE_THM, INT_LE_REFL]);


val _ = export_theory ();
