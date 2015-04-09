open HolKernel boolLib bossLib il2_to_il3_compilerTheory pairTheory lcsymtacs finite_mapTheory pred_setTheory integerTheory il3_store_propertiesTheory smallstep_il3Theory smallstep_vsm0Theory listTheory smallstep_il2Theory relationTheory smallstep_il2_clockedTheory smallstep_il3_clockedTheory


val _ = new_theory "il2_il3_correctness"

val fsa = full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss)


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
THEN rw [INT_ADD_LINV])

val map_deref_match = prove(``∀P st x.
     ms_il2 P st ∧ x ∈ FDOM st ⇒
     (MAP_KEYS (map_fun (FST (make_loc_map P))) st '
      ((FST (make_loc_map P)) ' x) =
      st ' x)``, metis_tac [map_deref_thm, map_fun_def])

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
THEN rw [])

val il3_eql_il2 = prove(``!P c c'. exec_clocked P c c' ==> !pc ck stk st.(c = SOME (pc, ck, stk, st)) /\ (ms_il2 P st) ==> (?pc' ck' stk' st'.(c' = SOME (pc', ck', stk', st')) /\ exec_il3_c (MAP (il2_to_il3m (FST (make_loc_map P))) P) (SOME (pc, ck, stk, MAP_KEYS (map_fun (FST (make_loc_map P))) st)) (SOME (pc', ck', stk', MAP_KEYS (map_fun (FST (make_loc_map P))) st'))) \/ ((c' = NONE) /\ exec_il3_c (MAP (il2_to_il3m (FST (make_loc_map P))) P) (SOME (pc, ck, stk, MAP_KEYS (map_fun (FST (make_loc_map P))) st)) NONE)``, 
STRIP_TAC
THEN fs [exec_clocked_def]
THEN ho_match_mp_tac RTC_STRONG_INDUCT
THEN rw []

THEN rw [exec_il3_c_def]

THEN Cases_on `c''` THEN fs [] THENL [Cases_on `c'`, all_tac] THEN1 (fsa [exec_clocked_one_cases, exec_il3_c_one_cases] THEN rw [] THEN match_mp_tac RTC_SUBSET THEN Cases_on `P !! pc` THEN fs [exec_clocked_instr_cases] THEN rw [exec_il3_c_one_cases] THEN `?n.pc = &n` by metis_tac [NUM_POSINT_EXISTS, int_ge] THEN fs [int_monotonic_thm]
THEN rfs [FETCH_EL] THEN rw [FETCH_EL, EL_MAP, il2_to_il3m_def] THEN rw [exec_il3_c_instr_cases])

THENL [Cases_on `x` THEN Cases_on `r` THEN Cases_on `r'`, Cases_on `x` THEN Cases_on `r` THEN Cases_on `r'` THEN fs [] THEN (Cases_on `c'` THEN1 (imp_res_tac RTC_CASES1 THEN fs [exec_clocked_one_cases])) THEN Cases_on `x` THEN Cases_on `r'` THEN Cases_on `r''`] THEN fs [] THEN imp_res_tac ms_const_2 THEN fs [] THEN fs [exec_il3_c_def] THEN rw [Once RTC_CASES1] THENL [Q.EXISTS_TAC `(SOME (q,q',q'',MAP_KEYS (map_fun (FST (make_loc_map P))) r))`, DISJ2_TAC THEN Q.EXISTS_TAC `(SOME
           (q''',q'''',q''''',
            MAP_KEYS (map_fun (FST (make_loc_map P))) r'))`] THEN (rw [] THEN fs [exec_il3_c_one_cases, exec_clocked_one_cases] THEN `?n.pc = &n` by metis_tac [NUM_POSINT_EXISTS, int_ge] THEN fs [int_monotonic_thm]
THEN rfs [FETCH_EL] THEN rw [FETCH_EL, EL_MAP] THEN Cases_on `EL n P` THEN fs [exec_clocked_instr_cases] THEN rw [il2_to_il3m_def, exec_il3_c_instr_cases]

THEN1 (match_mp_tac EQ_SYM THEN match_mp_tac map_deref_match THEN rw [])
THEN1 (rw [MAP_KEYS_def, map_fun_def] THEN HINT_EXISTS_TAC THEN rw [])
THEN1 (`(FST (make_loc_map P) ' i, v) = (map_fun (FST (make_loc_map P)) i, v)` by metis_tac [map_fun_def] THEN fs [ms_il2_def] THEN metis_tac [make_loc_map_inj, MAP_KEYS_FUPDATE])))

val IL2_IL3_EQ_1 = store_thm("IL2_IL3_EQ_1", ``!P pc c stk st.exec_clocked P (SOME (pc, c, stk, st)) NONE /\ ms_il2 P st ==> exec_il3_c (il2_to_il3 P) (SOME (pc, c, stk, MAP_KEYS (map_fun (FST (make_loc_map P))) st)) NONE``, rw [] THEN imp_res_tac il3_eql_il2 THEN fs [il3_eql_il2, FST, SND, il2_to_il3_def])

val IL2_IL3_EQ_2 = store_thm("IL2_IL3_EQ_2", ``!P pc c stk st pc' c' stk' st'.exec_clocked P (SOME (pc, c, stk, st)) (SOME (pc', c', stk', st')) /\ ms_il2 P st ==> exec_il3_c (il2_to_il3 P) (SOME (pc, c, stk, MAP_KEYS (map_fun (FST (make_loc_map P))) st)) (SOME (pc', c', stk', MAP_KEYS (map_fun (FST (make_loc_map P))) st'))``, rw [] THEN imp_res_tac il3_eql_il2 THEN fs [il3_eql_il2, FST, SND, il2_to_il3_def])

val _ = export_theory ()
