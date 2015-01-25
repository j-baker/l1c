open HolKernel Parse boolLib bossLib integerTheory finite_mapTheory ast_l1Theory smallstep_l1Theory lcsymtacs pairTheory l1_typeTheory pred_setTheory;

val _ = new_theory "smallstep_progress";

val L1_PROGRESS_THM = store_thm("L1_PROGRESS_THM",
``!e g t.l1_type e g t ==> !s.g ⊆ (FDOM s) ==> (?v.e = L1_Value v) \/ (?e' s'.ss_l1 (e, s) (e', s'))``,
ho_match_mp_tac l1_type_strongind
THEN rw [] THEN rw [Once ss_l1_cases] THEN fs [Once l1_type_cases] THEN rw [] THEN metis_tac [SUBSET_DEF]);

val _ = export_theory ();
