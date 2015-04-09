open ast_vsm0Theory smallstep_vsm0_clockedTheory smallstep_vsm0Theory HolKernel Parse boolLib bossLib integerTheory finite_mapTheory lcsymtacs relationTheory pairTheory

val _ = new_theory "vsm0_clocked_equiv"


val VSM0_CLOCKED_IMP_UNCLOCKED = store_thm("VSM0_CLOCKED_IMP_UNCLOCKED", ``!P c c'.vsm_exec_c P c c' ==> !pc cl stk pc' cl' stk'.(c = SOME (pc, cl, stk)) /\ (c' = SOME (pc', cl', stk')) ==> vsm_exec P (pc, stk) (pc', stk')``, 
STRIP_TAC THEN fs [vsm_exec_c_def, vsm_exec_def] THEN ho_match_mp_tac RTC_STRONG_INDUCT THEN rw [] THEN1 metis_tac [RTC_REFL] THEN rw [Once RTC_CASES1] THEN Cases_on `c'` THEN1 (imp_res_tac RTC_CASES1 THEN fs [vsm_exec_c_one_cases]) THEN DISJ2_TAC THEN Cases_on `x` THEN Cases_on `r` THEN fs [] THEN Q.EXISTS_TAC `(q, r')` THEN rw [] THEN fs [vsm_exec_one_cases, vsm_exec_c_one_cases] THEN Cases_on `P !! pc` THEN fs [vsm_exec_c_instr_cases, vsm_exec_instr_cases])

val VSM0_UNCLOCKED_IMP_CLOCKED = store_thm("VSM0_UNCLOCKED_IMP_CLOCKED", ``!P c c'.vsm_exec P c c' ==> !cl'. ?cl.vsm_exec_c P (SOME (FST c, cl, SND c)) (SOME (FST c', cl', SND c'))``,
STRIP_TAC THEN fs [vsm_exec_c_def, vsm_exec_def] THEN ho_match_mp_tac RTC_STRONG_INDUCT THEN rw [] THEN1 metis_tac [RTC_REFL] THEN rw [Once RTC_CASES1] THEN Cases_on `c` THEN Cases_on `c'` THEN fs [FST, SND] THEN fs [vsm_exec_one_cases, vsm_exec_c_one_cases] THEN Cases_on `P !! q` THEN fs [vsm_exec_c_instr_cases, vsm_exec_instr_cases] THEN rw [] THEN metis_tac [])

val _ = export_theory ()
