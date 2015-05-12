open ast_l1Theory bigstep_l1_clockedTheory pairTheory lcsymtacs boolLib bossLib HolKernel bigstep_determinacyTheory l1_typeTheory pred_setTheory finite_mapTheory store_creationTheory

val _ = new_theory "constant_folding"

val cfold_def = Define `
(cfold (L1_Value v) = L1_Value v) /\
(cfold (L1_Plus e1 e2) = let f1 = cfold e1
                      in let f2 = cfold e2
                      in case f1 of L1_Value (L1_Int n1) =>
                            (case f2 of L1_Value (L1_Int n2) => L1_Value (L1_Int (n1 + n2)) 
	                             | _ => L1_Plus f1 f2)
                                 | _ => L1_Plus f1 f2) /\
(cfold (L1_Geq e1 e2) = let f1 = cfold e1
                      in let f2 = cfold e2
                      in case f1 of L1_Value (L1_Int n1) =>
                            (case f2 of L1_Value (L1_Int n2) => L1_Value (L1_Bool (n1 >= n2)) 
	                             | _ => L1_Geq f1 f2)
                                 | _ => L1_Geq f1 f2) /\
(cfold (L1_If e1 e2 e3) = case cfold e1 of L1_Value (L1_Bool T) => cfold e2
					| L1_Value (L1_Bool F) => cfold e3
					| x => L1_If x (cfold e2) (cfold e3)) /\
(cfold (L1_Assign l e) = L1_Assign l (cfold e)) /\
(cfold (L1_Deref l) = L1_Deref l) /\
(cfold (L1_Seq e1 e2) = case cfold e1 of L1_Value (L1_Skip) => cfold e2 
				      | x => L1_Seq x (cfold e2)) /\
(cfold (L1_While e1 e2) = case cfold e1 of L1_Value (L1_Bool F) => L1_Value L1_Skip
                                        | L1_Value (L1_Bool T) => L1_While (L1_Value (L1_Bool T)) (L1_Value L1_Skip)
					| x => L1_While x (cfold e2))
`

val while_true_div = store_thm("while_true_div", ``!c s.bs_l1_c c (L1_While (L1_Value (L1_Bool T)) (L1_Value L1_Skip), s) NONE``,
Induct_on `c` THEN rw [Once bs_l1_c_cases] THEN DISJ2_TAC THEN DISJ2_TAC THEN1 (DISJ1_TAC THEN Q.LIST_EXISTS_TAC [`0`, `s`, `s`] THEN rw [] THEN rw [Once bs_l1_c_cases])
THEN 
DISJ2_TAC
 THEN Q.LIST_EXISTS_TAC [`SUC c`, `c`, `s`, `s`] THEN rw [] THEN rw [Once bs_l1_c_cases])

val l1_clock_decreasing = prove(``!c p r.bs_l1_c c p r ==> !v s' c'.(r = SOME (v, s', c')) ==> (c' <= c)``,
ho_match_mp_tac bs_l1_c_strongind THEN rw [] THEN rw [Once bs_l1_c_cases] THEN decide_tac)

val plus_case = Cases_on `f1` THEN rw [] THEN1 (Cases_on `f2` THEN1 (Cases_on `l` THEN Cases_on `l'` THEN rw [] THEN fs [Q.SPECL [`A`, `L1_Value B, C`] bs_l1_c_cases])
THEN Cases_on `l` THEN rw [] THEN rw [Once bs_l1_c_cases] THEN metis_tac []) THEN rw [Once bs_l1_c_cases] THEN metis_tac [];

val data_case = rw [Once bs_l1_c_cases] THEN metis_tac [];

val CFOLD_SAFE = store_thm("CFOLD_SAFE",
``!c p r.bs_l1_c c p r ==> bs_l1_c c (cfold (FST p), SND p) r``,
ho_match_mp_tac bs_l1_c_strongind THEN rw [] THEN fs [cfold_def, FST, SND] THEN rw []

THEN1 rw [Once bs_l1_c_cases]

THEN1 plus_case
THEN1 plus_case
THEN1 plus_case
THEN1 plus_case
THEN1 plus_case
THEN1 plus_case

THEN1 data_case
THEN1 data_case
THEN1 data_case

THEN (Cases_on `cfold e1` THEN fs [] THEN rw [] THEN1 (Cases_on `l` THEN rw [] THEN fs [Q.SPECL [`A`, `L1_Value A, B`] bs_l1_c_cases] THEN rw [] THEN rw [Once bs_l1_c_cases] THEN (TRY (DISJ2_TAC THEN (TRY (DISJ2_TAC)) THEN Cases_on `c` THENL [DISJ1_TAC, DISJ2_TAC])) THEN 
(TRY (DISJ2_TAC THEN Cases_on `c` THEN1 (imp_res_tac l1_clock_decreasing THEN fs []) THEN Q.LIST_EXISTS_TAC [`SUC n`, `SUC n`, `s`, `s`] THEN `bs_l1_c c'' (L1_While (L1_Value (L1_Bool T)) (L1_Value L1_Skip), s'') NONE` by metis_tac [while_true_div] THEN imp_res_tac L1_DETERMINISTIC THEN fs []))
THEN metis_tac [bs_l1_c_cases, while_true_div]) THEN rw [Once bs_l1_c_cases] THEN metis_tac [while_true_div]))



val domain_constant_thm = prove(``
!c p r.bs_l1_c c p r ==> !v s' c'.(r = SOME (v, s', c')) ==> (FDOM (SND p) = FDOM s')``,
ho_match_mp_tac bs_l1_c_strongind THEN rw [] THEN fs [FST, SND] THEN rw [EXTENSION] THEN Cases_on `x=l` THEN rw [])

val submap_fupdate2 = prove(``
!f1 f2 k v.(f1 ⊑ f2) ==> (f1 |+ (k, v)  ⊑ f2 |+ (k, v))``,
rw [SUBMAP_DEF] THEN fs [FAPPLY_FUPDATE_THM])


val supdate_def = Define `(supdate _ NONE = NONE) /\ (supdate s' (SOME (v, s, c)) = SOME (v, s', c))`

val submap_reduces_thm = store_thm("submap_reduces_thm", ``!c p r.bs_l1_c c p r ==> !s2.(s2 ⊑ (SND p)) ==> !t.l1_type (FST p) (FDOM s2) t ==> ?s2'.bs_l1_c c (FST p, s2) (supdate s2' r) /\ ((r <> NONE) ==> (s2' ⊑ FST (SND (THE r))))``,
(REVERSE (ho_match_mp_tac bs_l1_c_strongind THEN rw []))

THEN fs [Once (Q.SPEC `L1_Plus A B` l1_type_cases), Once (Q.SPEC `L1_Geq A B` l1_type_cases), Once (Q.SPEC `L1_Deref L` l1_type_cases), Once (Q.SPEC `L1_Assign L E` l1_type_cases), Once (Q.SPEC `L1_Seq A B` l1_type_cases), Once (Q.SPEC `L1_If A B C` l1_type_cases), Once (Q.SPEC `L1_While A B` l1_type_cases)]
THEN rw [Once bs_l1_c_cases] THEN fs [supdate_def] THEN res_tac THEN imp_res_tac domain_constant_thm THEN fs [] THEN rw []
THEN1 (TRY (Cases_on `c` THEN imp_res_tac l1_clock_decreasing THEN fs [] THEN (NTAC 4 res_tac THEN imp_res_tac domain_constant_thm THEN fs [] THEN rfs []) THEN Q.EXISTS_TAC `s2'''''''` THEN rw [] THEN DISJ2_TAC THEN metis_tac [bs_l1_c_cases, SUBMAP_DEF, submap_fupdate2, l1_clock_decreasing]))

THEN1 (TRY (Cases_on `c` THEN imp_res_tac l1_clock_decreasing THEN fs [] THEN (NTAC 3 DISJ2_TAC) THEN res_tac THEN Q.LIST_EXISTS_TAC [`c'`, `c''`, `s2''`, `s2'''`] THEN rw [] THEN res_tac THEN imp_res_tac domain_constant_thm THEN fs []))


THEN metis_tac [bs_l1_c_cases, SUBMAP_DEF, submap_fupdate2, l1_clock_decreasing])

val subset_cfold = prove(``!e.FDOM (create_store (cfold e)) ⊆ FDOM (create_store e)``,

Induct_on `e` THEN rw [] THEN fs [create_store_def, cfold_def, LET_DEF] THEN rw []

THEN Cases_on `cfold e` THEN (TRY (Cases_on `l:l1_value`)) THEN fs [create_store_def] THEN (Cases_on `cfold e'`) THEN (TRY (Cases_on `l:l1_value`)) THEN fs [create_store_def, SUBSET_DEF] THEN rw [] THEN (TRY (metis_tac [])) THEN fs [create_store_def] )

val type_sub = store_thm("type_sub", ``!e g g' t.l1_type e g t /\ g ⊆ g' ==> l1_type e g' t``,
Induct_on `e` THEN rw [] THEN fs [Once (Q.SPEC `L1_Plus A B` l1_type_cases), Once (Q.SPEC `L1_Geq A B` l1_type_cases), Once (Q.SPEC `L1_Deref L` l1_type_cases), Once (Q.SPEC `L1_Assign L E` l1_type_cases), Once (Q.SPEC `L1_Seq A B` l1_type_cases), Once (Q.SPEC `L1_If A B C` l1_type_cases), Once (Q.SPEC `L1_While A B` l1_type_cases)] THEN1 (Cases_on `l` THEN fs [Once l1_type_cases]) THEN metis_tac [SUBSET_DEF])


val cs_prop = prove(``!e x.x ∈ FDOM (create_store e) ==> ((create_store e) ' x = 0)``,

Induct_on `e` THEN fs [create_store_def] THEN rw [] THEN fs [FUNION_DEF] THEN metis_tac [])


val subset_imp = prove(``!e e'.(FDOM (create_store e) ⊆ FDOM (create_store e')) ==> (create_store e ⊑ create_store e')``,
rw [] THEN fs [SUBMAP_DEF, SUBSET_DEF] THEN rw [cs_prop])

val submap_cfold = store_thm("submap_cfold",
``!e.(create_store (cfold e)) ⊑ (create_store e)``,
metis_tac [subset_cfold, subset_imp])

val cs_min = store_thm("cs_min", ``!e g t.l1_type e g t ==> l1_type e (FDOM (create_store e)) t``,
Induct_on `e` THEN rw [] THEN fs [Once (Q.SPEC `L1_Plus A B` l1_type_cases), Once (Q.SPEC `L1_Geq A B` l1_type_cases), Once (Q.SPEC `L1_Deref L` l1_type_cases), Once (Q.SPEC `L1_Assign L E` l1_type_cases), Once (Q.SPEC `L1_Seq A B` l1_type_cases), Once (Q.SPEC `L1_If A B C` l1_type_cases), Once (Q.SPEC `L1_While A B` l1_type_cases)] THEN1 (Cases_on `l` THEN fs [Once l1_type_cases]) THEN rw [] THEN (TRY (match_mp_tac type_sub)) THEN rw [create_store_def]  THEN res_tac

THEN (TRY (Q.EXISTS_TAC `FDOM (create_store e)` THEN rw [SUBSET_DEF] THEN FAIL_TAC ""))
THEN (TRY (Q.EXISTS_TAC `FDOM (create_store e')` THEN rw [SUBSET_DEF] THEN FAIL_TAC ""))
THEN (TRY (Q.EXISTS_TAC `FDOM (create_store e'')` THEN rw [SUBSET_DEF] THEN FAIL_TAC "")))

val ltcfold = store_thm("ltcfold",
``!e g t.l1_type e g t /\ (FDOM (create_store e)) ⊆ g ==> l1_type (cfold e) g t``,
Induct_on `e` THEN rw []
THEN fs [Once (Q.SPEC `L1_Plus A B` l1_type_cases), Once (Q.SPEC `L1_Geq A B` l1_type_cases), Once (Q.SPEC `L1_Deref L` l1_type_cases), Once (Q.SPEC `L1_Assign L E` l1_type_cases), Once (Q.SPEC `L1_Seq A B` l1_type_cases), Once (Q.SPEC `L1_If A B C` l1_type_cases), Once (Q.SPEC `L1_While A B` l1_type_cases)]


THEN fs [cfold_def] THEN rw [] 

THEN1 (Cases_on `f1` THEN (TRY (Cases_on `l:l1_value`)) THEN fs [create_store_def] THEN (Cases_on `f2`) THEN (TRY (Cases_on `l:l1_value`)) THEN fs [create_store_def, FUNION_FEMPTY_1, FUNION_FEMPTY_2] THEN rw [Once l1_type_cases] )

THEN1 (Cases_on `f1` THEN (TRY (Cases_on `l:l1_value`)) THEN fs [create_store_def] THEN (Cases_on `f2`) THEN (TRY (Cases_on `l:l1_value`)) THEN fs [create_store_def, FUNION_FEMPTY_1, FUNION_FEMPTY_2] THEN rw [Once l1_type_cases] )

THEN1 (Cases_on `cfold e` THEN (TRY (Cases_on `l:l1_value`)) THEN fs [create_store_def] THEN (Cases_on `cfold e'`) THEN (TRY (Cases_on `l:l1_value`)) THEN (Cases_on `cfold e''`) THEN (TRY (Cases_on `l:l1_value`)) THEN fs [create_store_def, FUNION_FEMPTY_1, FUNION_FEMPTY_2] THEN rw [Once l1_type_cases] THEN res_tac THEN fs [Q.SPEC `L1_Value A` l1_type_cases]
THEN  fs [Once (Q.SPEC `L1_Plus A B` l1_type_cases), Once (Q.SPEC `L1_Geq A B` l1_type_cases), Once (Q.SPEC `L1_Deref L` l1_type_cases), Once (Q.SPEC `L1_Assign L E` l1_type_cases), Once (Q.SPEC `L1_Seq A B` l1_type_cases), Once (Q.SPEC `L1_If A B C` l1_type_cases), Once (Q.SPEC `L1_While A B` l1_type_cases)]
)

THEN1 (Cases_on `cfold e` THEN (TRY (Cases_on `l:l1_value`)) THEN fs [create_store_def] THEN fs [create_store_def, FUNION_FEMPTY_1, FUNION_FEMPTY_2] THEN rw [Once l1_type_cases])

THEN1 fs [Once l1_type_cases]

THEN1 (Cases_on `cfold e` THEN (TRY (Cases_on `l:l1_value`)) THEN fs [create_store_def] THEN (Cases_on `cfold e'`) THEN (TRY (Cases_on `l:l1_value`)) THEN fs [create_store_def, FUNION_FEMPTY_1, FUNION_FEMPTY_2] THEN rw [Once l1_type_cases] )

THEN1 (Cases_on `cfold e` THEN (TRY (Cases_on `l:l1_value`)) THEN fs [create_store_def] THEN fs [create_store_def, FUNION_FEMPTY_1, FUNION_FEMPTY_2] THEN rw [Once l1_type_cases] THEN rw [Once l1_type_cases]))

val cf_1 = store_thm("cf_1",
``!c e s t.l1_type e (FDOM (create_store e)) t /\ bs_l1_c c (e, create_store e) NONE ==> bs_l1_c c (cfold e, create_store (cfold e)) NONE``,
rw []
THEN imp_res_tac CFOLD_SAFE THEN fs []
THEN imp_res_tac submap_reduces_thm THEN fs []
THEN `create_store (cfold e) ⊑ create_store e` by metis_tac [submap_cfold] THEN res_tac THEN fs [supdate_def]
THEN `FDOM (create_store e) ⊆ FDOM (create_store e)` by metis_tac [SUBSET_REFL]
THEN imp_res_tac ltcfold THEN res_tac
THEN fs [] THEN imp_res_tac cs_min THEN rw [] THEN metis_tac [])


val cf_2 = store_thm("cf_2",
``!c e s t v c' s'.l1_type e (FDOM (create_store e)) t /\ bs_l1_c c (e, create_store e) (SOME (v, s', c')) ==> ?s''.bs_l1_c c (cfold e, create_store (cfold e)) (SOME (v, s'', c'))``,
rw []
THEN imp_res_tac CFOLD_SAFE THEN fs []
THEN imp_res_tac submap_reduces_thm THEN fs []
THEN `create_store (cfold e) ⊑ create_store e` by metis_tac [submap_cfold] THEN res_tac THEN fs [supdate_def]
THEN `FDOM (create_store e) ⊆ FDOM (create_store e)` by metis_tac [SUBSET_REFL]
THEN imp_res_tac ltcfold THEN res_tac
THEN fs [] THEN imp_res_tac cs_min THEN rw [] THEN metis_tac [])

val _ = export_theory ()
