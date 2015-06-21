open HolKernel boolLib bossLib bigstep_l1_clockedTheory ast_l1Theory lcsymtacs

val _ = new_theory "bigstep_determinacy"

val while_back_thm = prove(``!e1 e2 s s''' v cl cl'''.bs_l1_c cl (L1_While e1 e2, s) (SOME (v, s''', cl''')) ==> (v = L1_Skip) /\ ((bs_l1_c cl (e1, s) (SOME (L1_Bool F, s''', cl'''))) \/ (?cl' s' s'' cl''.bs_l1_c cl (e1, s) (SOME (L1_Bool T, s', cl')) /\ bs_l1_c cl' (e2, s') (SOME (L1_Skip, s'', SUC cl'')) /\ bs_l1_c cl'' (L1_While e1 e2, s'') (SOME (L1_Skip, s''', cl'''))))``,
rw [Once bs_l1_c_cases] THEN metis_tac []);

val L1_DETERMINISTIC = store_thm("L1_DETERMINISTIC",
``!c p r.bs_l1_c c p r ==> !r'. bs_l1_c c p r' ==> (r = r')``,
ho_match_mp_tac bs_l1_c_strongind THEN rw []
THEN1 (Cases_on `v` THEN fs [Once bs_l1_c_cases])
THEN fs [Q.SPECL [`A`, `L1_Plus B C, D`] bs_l1_c_cases, Q.SPECL [`A`, `L1_Geq B C, D`] bs_l1_c_cases, Q.SPECL [`A`, `L1_Deref B, D`] bs_l1_c_cases, Q.SPECL [`A`, `L1_Assign B C, D`] bs_l1_c_cases, Q.SPECL [`A`, `L1_Seq B C, D`] bs_l1_c_cases, Q.SPECL [`A`, `L1_If A B C, D`] bs_l1_c_cases] THEN (NTAC 3 (res_tac THEN fs [] THEN rw [])) THEN 
(NTAC 3 (res_tac THEN fs [] THEN rw []))

THEN Cases_on `r'` THEN fs [Once (Q.SPECL [`A`, `L1_While B C, D`, `NONE`] bs_l1_c_cases)] THEN (TRY (Cases_on `x` THEN Cases_on `r`))

THEN imp_res_tac while_back_thm THEN (NTAC 3 (res_tac THEN fs [] THEN rw [])));

val _ = export_theory ()
