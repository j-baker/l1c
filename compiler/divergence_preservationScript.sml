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

val closer = imp_res_tac type_means_value_type THEN res_tac THEN rw [] THEN res_tac THEN fs [] THEN rw [] THEN (TRY (Cases_on `b`)) THEN metis_tac [SUBSET_DEF];

val type_means_reduces = prove(``
!e g t.l1_type e g t ==> !s.(g ⊆ FDOM s) ==> !c.?r.bs_l1_c c (e, s) r
``,
ho_match_mp_tac l1_type_strongind THEN rw []

THEN1 rw [Once bs_l1_c_cases]
THEN1 rw [Once bs_l1_c_cases] 
THEN1 rw [Once bs_l1_c_cases]  

THEN1 (
rw [Once bs_l1_c_cases] THEN
`?r.bs_l1_c c (e, s) r` by metis_tac []
THEN Cases_on `r` THEN1 metis_tac [] THEN Cases_on `x` THEN Cases_on `r`
THEN `g ⊆ FDOM q'` by metis_tac [domain_constant_thm, SND]
THEN `?r.bs_l1_c r' (e', q') r` by metis_tac []
THEN Cases_on `r` THEN1 closer THEN Cases_on `x` THEN Cases_on `r`

THEN closer)

THEN1 (
rw [Once bs_l1_c_cases] THEN
`?r.bs_l1_c c (e, s) r` by metis_tac []
THEN Cases_on `r` THEN1 metis_tac [] THEN Cases_on `x` THEN Cases_on `r`
THEN `g ⊆ FDOM q'` by metis_tac [domain_constant_thm, SND]
THEN `?r.bs_l1_c r' (e', q') r` by metis_tac []
THEN Cases_on `r` THEN1 closer THEN Cases_on `x` THEN Cases_on `r`

THEN closer)

THEN1 (
rw [Once bs_l1_c_cases] THEN
`?r.bs_l1_c c (e, s) r` by metis_tac []
THEN Cases_on `r` THEN1 metis_tac [] THEN Cases_on `x` THEN Cases_on `r`
THEN `g ⊆ FDOM q'` by metis_tac [domain_constant_thm, SND]

THEN `?r.bs_l1_c r' (e', q') r` by metis_tac []
THEN `?r.bs_l1_c r' (e'', q') r` by metis_tac []
THEN Cases_on `r` THEN Cases_on `r''` THEN1 closer THEN Cases_on `x` THEN Cases_on `r`
THEN (TRY (Cases_on `x'` THEN Cases_on `r`))
THEN closer)

THEN1 (
rw [Once bs_l1_c_cases] THEN
`?r.bs_l1_c c (e, s) r` by metis_tac []
THEN Cases_on `r` THEN1 closer THEN Cases_on `x` THEN Cases_on `r` THEN closer)

THEN1 (rw [Once bs_l1_c_cases] THEN metis_tac [SUBSET_DEF])

THEN1 (
rw [Once bs_l1_c_cases] THEN
`?r.bs_l1_c c (e, s) r` by metis_tac []
THEN Cases_on `r` THEN1 metis_tac [] THEN Cases_on `x` THEN Cases_on `r`
THEN `g ⊆ FDOM q'` by metis_tac [domain_constant_thm, SND]
THEN `?r.bs_l1_c r' (e', q') r` by metis_tac []
THEN Cases_on `r` THEN1 closer THEN Cases_on `x` THEN Cases_on `r`

THEN closer)

THEN Q.UNDISCH_TAC `g ⊆ FDOM s`
THEN Q.SPEC_TAC (`s`, `s`)
THEN completeInduct_on `c` THEN rw []


THEN rw [Once bs_l1_c_cases] THEN
`?r.bs_l1_c c (e, s) r` by metis_tac []
THEN Cases_on `r` THEN1 metis_tac [] THEN Cases_on `x` THEN Cases_on `r`
THEN `g ⊆ FDOM q'` by metis_tac [domain_constant_thm, SND]
THEN `?r.bs_l1_c r' (e', q') r` by metis_tac []

THEN Cases_on `r` THEN1 closer THEN Cases_on `x` THEN Cases_on `r`

THEN Cases_on `r''` THEN1 closer

THEN `r' <= c` by cheat
THEN `SUC n <= r'` by cheat
THEN `n < c` by decide_tac
THEN `g ⊆ FDOM q'''` by metis_tac [domain_constant_thm, SND]
THEN `?r.bs_l1_c n (L1_While e e', q''') r` by metis_tac []

THEN Cases_on `r` THEN1 closer THEN Cases_on `x` THEN Cases_on `r` THEN `l1_type (L1_While e e') g unitL1` by metis_tac [l1_type_cases] THEN closer);
val _ = export_theory ();
