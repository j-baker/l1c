open HolKernel boolLib bossLib il2_to_il3_compilerTheory pairTheory lcsymtacs finite_mapTheory pred_setTheory integerTheory il3_store_propertiesTheory smallstep_il3Theory smallstep_vsm0Theory listTheory smallstep_il2Theory relationTheory;


val _ = new_theory "il2_il3_correctness";


val map_fetch_thm = prove(``!f xs n.(n < LENGTH xs) ==> ((MAP f xs) !! (&n) = f (xs !! (&n)))``,
Induct_on `xs`
THEN1 rw [LENGTH]

THEN rw []

THEN rw [fetch_def]

THEN Cases_on `n` THEN1 metis_tac []
THEN `n' < LENGTH xs` by DECIDE_TAC
THEN ` MAP f xs !! &n' = f (xs !! &n')` by metis_tac []
THEN rw [int_of_num]

THEN rw [INT_1]
THEN rw [int_sub]
THEN REWRITE_TAC [GSYM INT_ADD_ASSOC]
THEN REWRITE_TAC [Once INT_ADD_SYM]
THEN rw [INT_ADD_LINV]);

val fetch_append_thm = store_thm("fetch_append_thm",
``!i xs ys.(&0 <= i) ==> ((xs ++ ys) !! i = (if i < &LENGTH xs then xs !! i else ys !! (i - &LENGTH xs)))``,
Induct_on `xs` THEN rw []

THEN1 metis_tac [int_le]

THEN1 (Cases_on `i = 0` THEN rw [APPEND, fetch_def]

THEN `xs ++ ys !! (i-1) = xs !! (i-1)` by (`0 <= (i-1)` by full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss) [] THEN `i - 1 < &LENGTH xs` by full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss) [] THEN metis_tac []))

THEN full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss) [INT_NOT_LT]

THEN `~(i-1 < &LENGTH xs)` by full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss) []
THEN `xs ++ ys !! (i-1) = ys !! (i-1) - &LENGTH xs` by (full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss) [])

THEN Cases_on `i = 0` THEN full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss) [APPEND, fetch_def] THEN rw []
THEN full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss) [INT]
THEN `i - 1 - &LENGTH xs = i - (&LENGTH xs + 1)` by full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss) [INT, INT_SUB_LNEG, INT_ADD_COMM]
THEN rw []);

val il3_eql_il2 = prove(``!P c c'. exec P c c' ==> (ms_il2 P (SND (SND c))) ==> exec_il3 (MAP (il2_to_il3m (FST (make_loc_map P))) P) (FST c, FST (SND c), MAP_KEYS (map_fun (FST (make_loc_map P))) (SND (SND c))) (FST c', FST (SND c'), MAP_KEYS (map_fun (FST (make_loc_map P))) (SND (SND c')))``, 
STRIP_TAC
THEN fs [exec_def]
THEN ho_match_mp_tac RTC_STRONG_INDUCT
THEN rw []

THEN rw [exec_il3_def]

THEN Cases_on `c` THEN Cases_on `c'` THEN Cases_on `c''` THEN Cases_on `r` THEN Cases_on `r'` THEN Cases_on `r''` THEN fs [FST, SND]

THEN rw [exec_il3_def]
THEN rw [Once RTC_CASES1]
THEN DISJ2_TAC
THEN `ms_il2 P r` by metis_tac [ms_const_2, SND, exec_def, RTC_SUBSET]
THEN fs [exec_il3_def]
THEN HINT_EXISTS_TAC
THEN rw []
THEN rw [exec_il3_one_cases] THEN fs [exec_one_cases]
THEN fs [int_ge]
THEN rw []

THEN Cases_on `P !! q` THEN fs [exec_instr_cases] THEN rw []

THEN (TRY (
`?nq.q = &nq` by rw [NUM_POSINT_EXISTS, int_ge]
THEN rw []
THEN `nq < LENGTH P` by rw [int_monotonic_thm]

THEN rw [map_fetch_thm]

THEN rw [il2_to_il3m_def]
THEN rw [exec_il3_instr_cases]
THEN FAIL_TAC "fail"
))

THEN (TRY (
`?nq.pc' = &nq` by rw [NUM_POSINT_EXISTS, int_ge]
THEN rw []
THEN `nq < LENGTH P` by rw [int_monotonic_thm]

THEN rw [map_fetch_thm]

THEN rw [il2_to_il3m_def]
THEN rw [exec_il3_instr_cases]
THEN FAIL_TAC "fail"
))

THEN (TRY (`?nq.q = &nq` by rw [NUM_POSINT_EXISTS, int_ge]
THEN rw []
THEN `nq < LENGTH P` by rw [int_monotonic_thm]

THEN rw [map_fetch_thm]

THEN rw [il2_to_il3m_def]


THEN rw [exec_il3_instr_cases]

THEN `(FST (make_loc_map P) ' i) = map_fun (FST (make_loc_map P)) i` by metis_tac [map_fun_def]

THEN fs []
THEN imp_res_tac ms_il2_trans
THEN rw []

THEN TRY (match_mp_tac MAP_KEYS_FUPDATE
THEN fs [FDOM_FUPDATE]
THEN ` i INSERT FDOM r''' = FDOM r'''` by metis_tac []
THEN fs [])

THEN rw [MAP_KEYS_def]

THEN metis_tac [MAP_KEYS_FUPDATE, make_loc_map_inj, INJ_SUBSET, ms_il2_def, map_fun_def, ms_il2_trans, map_deref_thm, map_fun_def, MAP_KEYS_def, map_fun_def])))


val nice_il3_eql_il2 = store_thm("nice_il3_eql_il2", ``!P pc stk st pc' stk' st'.exec P (pc, stk, st) (pc', stk', st') /\ ms_il2 P st ==>
exec_il3 (il2_to_il3 P) (pc, stk, MAP_KEYS (map_fun (FST (make_loc_map P))) st)
(pc', stk', MAP_KEYS (map_fun (FST (make_loc_map P))) st')``,
metis_tac [il3_eql_il2, FST, SND, il2_to_il3_def]);

val _ = export_theory ();
