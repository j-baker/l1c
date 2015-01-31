open HolKernel Parse boolLib bossLib integerTheory finite_mapTheory ast_l1Theory smallstep_l1Theory lcsymtacs pairTheory l1_typeTheory;

val _ = new_theory "smallstep_type_preservation";

val domain_constant_thm = prove(``!p p'.ss_l1 p p' ==> (FDOM (SND p) = FDOM (SND p'))``, ho_match_mp_tac ss_l1_strongind >> rw [SND, FDOM_EQ_FDOM_FUPDATE]);

val pres = prove(``!p p'.ss_l1 p p' ==> (!t.l1_type (FST p) (FDOM (SND p)) t ==> l1_type (FST p') (FDOM (SND p')) t)``,

ho_match_mp_tac ss_l1_strongind THEN rw [FST, SND]

>- fs [Once l1_type_cases]
>- (fs [Once (Q.SPEC `L1_Plus e1 e2` l1_type_cases)] >> metis_tac [domain_constant_thm, SND])
>- (fs [Once (Q.SPEC `L1_Plus e1 e2` l1_type_cases)] >> metis_tac [domain_constant_thm, SND])

>- fs [Once l1_type_cases]
>- (fs [Once (Q.SPEC `L1_Geq e1 e2` l1_type_cases)] >> metis_tac [domain_constant_thm, SND])
>- (fs [Once (Q.SPEC `L1_Geq e1 e2` l1_type_cases)] >> metis_tac [domain_constant_thm, SND])

>- fs [Once l1_type_cases]
>- fs [Once l1_type_cases]

>- (fs [Once (Q.SPEC `L1_Assign l e` l1_type_cases)] >> metis_tac [domain_constant_thm, SND])

>- (fs [Once (Q.SPEC `L1_Seq e1 e2` l1_type_cases)] >> metis_tac [domain_constant_thm, SND])

>- (fs [Once (Q.SPEC `L1_Seq e1 e2` l1_type_cases)] >> metis_tac [domain_constant_thm, SND])

>- fs [Once l1_type_cases]
>- fs [Once l1_type_cases]

>- (fs [Once (Q.SPEC `L1_If e1 e2 e3` l1_type_cases)] >> metis_tac [domain_constant_thm, SND])

>- (fs [Once (Q.SPEC `L1_While e1 e2` l1_type_cases)] >> rw [Once l1_type_cases] >> rw [Once l1_type_cases] >> rw [Once l1_type_cases]));

val SMALLSTEP_TYPE_PRESERVATION = store_thm("SMALLSTEP_TYPE_PRESERVATION",
``!e s e' s' t.ss_l1 (e, s) (e', s') /\ l1_type e (FDOM s) t ==> l1_type e' (FDOM s') t``, metis_tac [pres, FST, SND]);

val _ = export_theory ();
