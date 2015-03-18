open HolKernel boolLib bossLib l1_to_il1_compilerTheory il1_to_il2_compilerTheory store_creationTheory il1_il2_correctnessTheory l1_il1_correctnessTheory lcsymtacs il2_to_il3_compilerTheory listTheory pairTheory pred_setTheory l1_il1_totalTheory bigstep_il1Theory ast_l1Theory store_equivalenceTheory finite_mapTheory il3_to_vsm0_correctnessTheory il3_store_propertiesTheory il2_il3_correctnessTheory bs_ss_equivalenceTheory smallstep_vsm0_clockedTheory bigstep_il1_clockedTheory bigstep_l1_clockedTheory l1_typeTheory;

val _ = new_theory "divergence_preservation"


val domain_constant_thm = prove(``
!c p r.bs_l1_c c p r ==> !v s' c'.(r = SOME (v, s', c')) ==> (FDOM (SND p) = FDOM s')``,
ho_match_mp_tac bs_l1_c_strongind THEN rw [] THEN fs [FST, SND] THEN rw [EXTENSION] THEN Cases_on `x=l` THEN rw []);

val type_means_value_type = prove(``
!c p r.bs_l1_c c p r ==> !v s' c'.(r = SOME (v, s', c')) ==> !g t.l1_type (FST p) g t ==> !s.(g ⊆ FDOM (SND p)) ==> ((t = intL1) /\ (?n.v = L1_Int n)) \/ ((t = boolL1) /\ (?b.v = L1_Bool b)) \/ ((t = unitL1) /\ (v = L1_Skip))``,

ho_match_mp_tac bs_l1_c_strongind THEN rw []

THEN1 (Cases_on `v` THEN fs [Once l1_type_cases])

THEN Cases_on `t` THEN (NTAC 3 ((TRY (`FDOM s = FDOM s'` by metis_tac [domain_constant_thm, SND])) THEN (TRY (`FDOM s' = FDOM s''` by metis_tac [domain_constant_thm, SND])) THEN res_tac THEN fs [Q.SPEC `L1_Plus A B`(Once l1_type_cases), Q.SPEC `L1_Geq A B`(Once l1_type_cases), Q.SPEC `L1_Deref A`(Once l1_type_cases), Q.SPEC `L1_Assign A B`(Once l1_type_cases), Q.SPEC `L1_Seq A B`(Once l1_type_cases), Q.SPEC `L1_If A B C`(Once l1_type_cases), Q.SPEC `L1_While A B`(Once l1_type_cases)] THEN rw [])));

val _ = export_theory ();
