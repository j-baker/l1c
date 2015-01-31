open HolKernel Parse boolLib bossLib integerTheory finite_mapTheory ast_l1Theory smallstep_l1Theory lcsymtacs pairTheory;

val _ = new_theory "smallstep_determinacy";

val L1_DETERMINACY_THM = store_thm("L1_DETERMINACY_THM",
``!p p'.ss_l1 p p' ==> !p''.ss_l1 p p'' ==> (p' = p'')``,

ho_match_mp_tac ss_l1_strongind >> rw []

>- (fs [Once ss_l1_cases] >> fs [Once ss_l1_cases])

>- (fs [Once (Q.SPEC `(L1_Plus e1 e2, s)` ss_l1_cases)]
        >- (rw [] >> fs [Once ss_l1_cases])
        >- (rw [] >> metis_tac [PAIR_EQ])
        >- (rw [] >> fs [Once ss_l1_cases]))

>- (fs [Once (Q.SPEC `(L1_Plus e1 e2, s)` ss_l1_cases)]
        >- (rw [] >> fs [Once ss_l1_cases])
        >- (rw [] >> fs [Once ss_l1_cases])
        >- (rw [] >> metis_tac [PAIR_EQ]))

>- (fs [Once ss_l1_cases] >> fs [Once ss_l1_cases])

>- (fs [Once (Q.SPEC `(L1_Geq e1 e2, s)` ss_l1_cases)]
        >- (rw [] >> fs [Once ss_l1_cases])
        >- (rw [] >> metis_tac [PAIR_EQ])
        >- (rw [] >> fs [Once ss_l1_cases]))

>- (fs [Once (Q.SPEC `(L1_Geq e1 e2, s)` ss_l1_cases)]
        >- (rw [] >> fs [Once ss_l1_cases])
        >- (rw [] >> fs [Once ss_l1_cases])
        >- (rw [] >> metis_tac [PAIR_EQ]))

>- (fs [Once ss_l1_cases] >> fs [Once ss_l1_cases])

>- (fs [Once ss_l1_cases] >> fs [Once ss_l1_cases])

>- (fs [Once (Q.SPEC `(L1_Assign l e, s)` ss_l1_cases)]
        >- (rw [] >> fs [Once ss_l1_cases])
        >- (rw [] >> metis_tac [PAIR_EQ]))

>- (fs [Once ss_l1_cases] >> fs [Once ss_l1_cases])

>- (fs [Once (Q.SPEC `(L1_Seq e1 e2, s)` ss_l1_cases)]
        >- (rw [] >> fs [Once ss_l1_cases])
        >- (rw [] >> metis_tac [PAIR_EQ]))

>- (fs [Once ss_l1_cases] >> fs [Once ss_l1_cases])

>- (fs [Once ss_l1_cases] >> fs [Once ss_l1_cases])

>- (fs [Once (Q.SPEC `(L1_If e1 e2 e3, s)` ss_l1_cases)]
        >- (rw [] >> fs [Once ss_l1_cases])
        >- (rw [] >> fs [Once ss_l1_cases])
        >- (rw [] >> metis_tac [PAIR_EQ]))

>- (fs [Once ss_l1_cases] >> fs [Once ss_l1_cases]));


val _ = export_theory ();
