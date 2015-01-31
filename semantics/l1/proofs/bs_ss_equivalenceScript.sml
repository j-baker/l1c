open HolKernel Parse boolLib bossLib integerTheory finite_mapTheory ast_l1Theory bigstep_l1Theory smallstep_l1Theory lcsymtacs pairTheory l1_typeTheory relationTheory;

val _ = new_theory "bs_ss_equivalence";


val DOMAIN_CONSTANT_THM = prove(``!p1 p2. ss_l1 p1 p2 ==> (FDOM (SND p1) = FDOM (SND p2))``,
    HO_MATCH_MP_TAC ss_l1_strongind THEN rw [SND, FDOM_EQ_FDOM_FUPDATE]);

val DOMAIN_CONSTANT_STAR_THM = prove(``!p1 p2. ss_l1^* p1 p2 ==> (FDOM (SND p1) = FDOM (SND p2))``,
    HO_MATCH_MP_TAC RTC_INDUCT THEN METIS_TAC [DOMAIN_CONSTANT_THM]);

val SS_STAR_ASSIGN_THM = prove(``!p p'.ss_l1^* p p' ==> !l.ss_l1^* (L1_Assign l (FST p), SND p) (L1_Assign l (FST p'), SND p')``,
    ho_match_mp_tac RTC_INDUCT
    THEN rw [FST, SND]
    THEN rw [Once RTC_CASES1]
    THEN Cases_on `p`
    THEN Cases_on `p'`
    THEN Cases_on `p''`
    THEN metis_tac [FST, SND, ss_l1_cases]);

val SS_STAR_IF_THM = prove(``!p p'.ss_l1^* p p' ==> !e2 e3.ss_l1^* (L1_If (FST p) e2 e3, SND p) (L1_If (FST p') e2 e3, SND p')``,
    HO_MATCH_MP_TAC RTC_INDUCT
    THEN rw []
    THEN Cases_on `p`
    THEN Cases_on `p'`
    THEN Cases_on `p''`
    THEN fs [FST, SND]
    THEN rw [Once RTC_CASES1]
    THEN METIS_TAC [FST, SND, ss_l1_cases]);

val SS_BS_STAR_IF_T_THM = prove(``!e1 e2 e3 s s'.ss_l1^* (e1, s) (L1_Value (L1_Bool T), s') ==> ss_l1^* (L1_If e1 e2 e3, s) (e2, s')``,
    METIS_TAC ([FST, SND, SS_STAR_IF_THM, RTC_SUBSET, RTC_CASES_RTC_TWICE]@[FST, SND, ss_l1_cases]));

val SS_BS_STAR_IF_F_THM = prove(``!e1 e2 e3 s s'.ss_l1^* (e1, s) (L1_Value (L1_Bool F), s') ==> ss_l1^* (L1_If e1 e2 e3, s) (e3, s')``,
    METIS_TAC ([FST, SND, SS_STAR_IF_THM, RTC_SUBSET, RTC_CASES_RTC_TWICE]@[FST, SND, ss_l1_cases]));

val SS_STAR_ASSIGN_CASE_THM = prove(``!e1 n s s' l.ss_l1^* (e1, s) (L1_Value (L1_Int n), s') ==> ss_l1^* (L1_Assign l e1, s) (L1_Assign l (L1_Value (L1_Int n)), s')``,
    METIS_TAC [FST, SND, SS_STAR_ASSIGN_THM]);

val SS_BS_STAR_ASSIGN_THM = prove(``!e1 n s s' l.l ∈ FDOM s /\ ss_l1^* (e1, s) (L1_Value (L1_Int n), s') ==> ss_l1^* (L1_Assign l e1, s) (L1_Value L1_Skip, s' |+ (l, n))``,
    rw []
    THEN `FDOM s = FDOM s'` by METIS_TAC [DOMAIN_CONSTANT_STAR_THM, SND]
    THEN METIS_TAC ([SS_STAR_ASSIGN_CASE_THM, RTC_CASES_RTC_TWICE, RTC_SUBSET]@[FST, SND, ss_l1_cases]));

val SS_STAR_GEQ_1_THM = prove(``!p p'.ss_l1^* p p' ==> !e2.ss_l1^* (L1_Geq (FST p) e2, (SND p)) (L1_Geq (FST p') e2, SND p')``,
    HO_MATCH_MP_TAC RTC_INDUCT
    THEN rw []
    THEN Cases_on `p`
    THEN Cases_on `p'`
    THEN Cases_on `p''`
    THEN fs [FST, SND]
    THEN rw [Once RTC_CASES1]
    THEN METIS_TAC [FST, SND, ss_l1_cases]);

val SS_STAR_GEQ_2_THM = prove(``!p p'.ss_l1^* p p' ==> !n1.ss_l1^* (L1_Geq (L1_Value (L1_Int n1)) (FST p), (SND p)) (L1_Geq (L1_Value (L1_Int n1)) (FST p'), SND p')``,
    HO_MATCH_MP_TAC RTC_INDUCT
    THEN rw []
    THEN Cases_on `p`
    THEN Cases_on `p'`
    THEN Cases_on `p''`
    THEN fs [FST, SND]
    THEN rw [Once RTC_CASES1]
    THEN METIS_TAC [FST, SND, ss_l1_cases]);


val SS_STAR_PLUS_1_THM = prove(``!p p'.ss_l1^* p p' ==> !e2.ss_l1^* (L1_Plus (FST p) e2, (SND p)) (L1_Plus (FST p') e2, SND p')``,
    HO_MATCH_MP_TAC RTC_INDUCT
    THEN rw []
    THEN Cases_on `p`
    THEN Cases_on `p'`
    THEN Cases_on `p''`
    THEN fs [FST, SND]
    THEN rw [Once RTC_CASES1]
    THEN METIS_TAC [FST, SND, ss_l1_cases]);

val SS_STAR_PLUS_2_THM = prove(``!p p'.ss_l1^* p p' ==> !n1.ss_l1^* (L1_Plus (L1_Value (L1_Int n1)) (FST p), (SND p)) (L1_Plus (L1_Value (L1_Int n1)) (FST p'), SND p')``,
    HO_MATCH_MP_TAC RTC_INDUCT
    THEN rw []
    THEN Cases_on `p`
    THEN Cases_on `p'`
    THEN Cases_on `p''`
    THEN fs [FST, SND]
    THEN rw [Once RTC_CASES1]
    THEN METIS_TAC [FST, SND, ss_l1_cases]);


val SS_STAR_PLUS_1_CASE_THM = prove(``!e1 e2 n1 s s'.ss_l1^* (e1, s) (L1_Value (L1_Int n1), s') ==> ss_l1^* (L1_Plus e1 e2, s) (L1_Plus (L1_Value (L1_Int n1)) e2, s')``,
    METIS_TAC [SS_STAR_PLUS_1_THM, FST, SND]);

val SS_STAR_PLUS_2_CASE_THM = prove(``!e2 n1 n2 s s'.ss_l1^* (e2, s) (L1_Value (L1_Int n2), s') ==> ss_l1^* (L1_Plus (L1_Value (L1_Int n1)) e2, s) (L1_Plus (L1_Value (L1_Int n1)) (L1_Value (L1_Int n2)), s')``,
    METIS_TAC [SS_STAR_PLUS_2_THM, FST, SND]);

val SS_BS_STAR_PLUS_THM = prove(``!e1 e2 n1 n2 s s' s''.ss_l1^* (e1, s) (L1_Value (L1_Int n1), s') /\ ss_l1^* (e2, s') (L1_Value (L1_Int n2), s'') ==> ss_l1^* (L1_Plus e1 e2, s) (L1_Value (L1_Int (n1 + n2)), s'')``,
    METIS_TAC ([SS_STAR_PLUS_1_CASE_THM, SS_STAR_PLUS_2_CASE_THM, RTC_CASES_RTC_TWICE, RTC_SUBSET]@[FST, SND, ss_l1_cases]));

val SS_STAR_GEQ_1_CASE_THM = prove(``!e1 e2 n1 s s'.ss_l1^* (e1, s) (L1_Value (L1_Int n1), s') ==> ss_l1^* (L1_Geq e1 e2, s) (L1_Geq (L1_Value (L1_Int n1)) e2, s')``,
    METIS_TAC [SS_STAR_GEQ_1_THM, FST, SND]);

val SS_STAR_GEQ_2_CASE_THM = prove(``!e2 n1 n2 s s'.ss_l1^* (e2, s) (L1_Value (L1_Int n2), s') ==> ss_l1^* (L1_Geq (L1_Value (L1_Int n1)) e2, s) (L1_Geq (L1_Value (L1_Int n1)) (L1_Value (L1_Int n2)), s')``,
    METIS_TAC [SS_STAR_GEQ_2_THM, FST, SND]);

val SS_BS_STAR_GEQ_THM = prove(``!e1 e2 n1 n2 s s' s''.ss_l1^* (e1, s) (L1_Value (L1_Int n1), s') /\ ss_l1^* (e2, s') (L1_Value (L1_Int n2), s'') ==> ss_l1^* (L1_Geq e1 e2, s) (L1_Value (L1_Bool (n1 >= n2)), s'')``,
    METIS_TAC ([SS_STAR_GEQ_1_CASE_THM, SS_STAR_GEQ_2_CASE_THM, RTC_CASES_RTC_TWICE, RTC_SUBSET]@[FST, SND, ss_l1_cases]));

val SS_STAR_SEQ_THM = prove(``!p p'.ss_l1^* p p' ==> !e2.ss_l1^* (L1_Seq (FST p) e2, (SND p)) (L1_Seq (FST p') e2, SND p')``,
    HO_MATCH_MP_TAC RTC_INDUCT
    THEN rw []
    THEN Cases_on `p`
    THEN Cases_on `p'`
    THEN Cases_on `p''`
    THEN fs [FST, SND]
    THEN rw [Once RTC_CASES1]
    THEN METIS_TAC [FST, SND, ss_l1_cases]);

val SS_STAR_SEQ_CASE_1_THM = prove(``!e1 e2 s s'.ss_l1^* (e1, s) (L1_Value L1_Skip, s') ==> ss_l1^* (L1_Seq e1 e2, s) (L1_Seq (L1_Value L1_Skip) e2, s')``,
    METIS_TAC [SS_STAR_SEQ_THM, FST, SND]);

val SS_STAR_SEQ_CASE_2_THM = prove(``!e2 e2' s s'.ss_l1^* (e2, s) (e2', s') ==> ss_l1^* (L1_Seq (L1_Value L1_Skip) e2, s) (e2', s')``,
    METIS_TAC ([SS_STAR_SEQ_THM, FST, SND, RTC_SUBSET, RTC_CASES_RTC_TWICE]@[FST, SND, ss_l1_cases]));

val SS_BS_STAR_SEQ_THM = prove(``!e1 e2 e2' s s' s''.ss_l1^* (e1, s) (L1_Value L1_Skip, s') /\ ss_l1^* (e2, s') (e2', s'') ==> ss_l1^* (L1_Seq e1 e2, s) (e2', s'')``,
    METIS_TAC [SS_STAR_SEQ_CASE_1_THM, SS_STAR_SEQ_CASE_2_THM, RTC_CASES_RTC_TWICE]);



val bs_imp_ss = prove(``!p v s'.bs_l1 p v s' ==> ss_l1^* p (L1_Value v, s')``,

ho_match_mp_tac bs_l1_strongind THEN (REVERSE (rw [FST, SND]))

THEN_LT (Tactical.NTH_GOAL (        `ss_l1 (L1_While e1 e2, s) (L1_If e1 (L1_Seq e2 (L1_While e1 e2)) (L1_Value (L1_Skip)), s)` by METIS_TAC [ss_l1_cases]
THEN        imp_res_tac SS_BS_STAR_IF_T_THM
THEN        imp_res_tac SS_BS_STAR_SEQ_THM
THEN  METIS_TAC [RTC_SUBSET, RTC_CASES_RTC_TWICE]) 2)

THEN
metis_tac [SS_BS_STAR_PLUS_THM, SS_BS_STAR_GEQ_THM, RTC_SUBSET, SS_BS_STAR_ASSIGN_THM, SS_BS_STAR_SEQ_THM, SS_BS_STAR_IF_T_THM, RTC_CASES_RTC_TWICE, SS_BS_STAR_IF_F_THM, RTC_SUBSET, ss_l1_cases]);

val BS_PLUS_BACK_THM = prove(``!e1 e2 s v t.bs_l1 (L1_Plus e1 e2, s) v t ==> ?n1 n2 s'.bs_l1 (e1, s) (L1_Int n1) s' /\ bs_l1 (e2, s') (L1_Int n2) t /\ (v = L1_Int (n1 + n2))``,
    rw [Once bs_l1_cases]
    THEN METIS_TAC []);

val BS_GEQ_BACK_THM = prove(``!e1 e2 s v t.bs_l1 (L1_Geq e1 e2, s) v t ==> ?n1 n2 s'.bs_l1 (e1, s) (L1_Int n1) s' /\ bs_l1 (e2, s') (L1_Int n2) t /\ (v = L1_Bool (n1 >= n2))``,
    rw [Once bs_l1_cases]
    THEN METIS_TAC []);

val BS_ASSIGN_BACK_THM = prove(``!l e s n t v.bs_l1 (L1_Assign l e, s) v t ==> ?n s'. l ∈ FDOM s /\ bs_l1 (e, s) (L1_Int n) s' /\ (v = L1_Skip) /\ (t = s' |+ (l, n))``,
    rw [Once bs_l1_cases]
    THEN METIS_TAC []);

val BS_SEQ_BACK_THM = prove(``!e1 e2 s t v.bs_l1 (L1_Seq e1 e2, s) v t ==> ?s'.bs_l1 (e1, s) L1_Skip s' /\ bs_l1 (e2, s') v t``,
    rw [Once bs_l1_cases]
    THEN METIS_TAC []);

val BS_IF_BACK_THM = prove(``!e1 e2 e3 s t v.bs_l1 (L1_If e1 e2 e3, s) v t ==> (?s'.bs_l1 (e1, s) (L1_Bool T) s' /\ bs_l1 (e2, s') v t) \/ (?s'.bs_l1 (e1, s) (L1_Bool F) s' /\ bs_l1 (e3, s') v t)``,
    rw [Once bs_l1_cases]
    THEN METIS_TAC []);

val BS_WHILE_BACK_THM = prove(``!e1 e2 s t v.bs_l1 (L1_While e1 e2, s) v t ==> (v = L1_Skip)``,
    rw [Once bs_l1_cases]
    THEN METIS_TAC []);

val BS_VALUE_BACK_THM = prove(``!v v' s t.bs_l1 (L1_Value v, s) v' t ==> ((v = v') /\ (t = s))``,
    rw [Once bs_l1_cases]
    THEN METIS_TAC []);

val SS_STEP_BS_THM = prove(``!p p'.ss_l1 p p' ==> !v t.(bs_l1 p' v t ==> bs_l1 p v t)``,
    HO_MATCH_MP_TAC ss_l1_strongind
    THEN rw []
    THEN rw [Once bs_l1_cases]
    THEN1 (fs [Once bs_l1_cases] THEN
           rw [Once bs_l1_cases])
    THEN1 METIS_TAC [BS_PLUS_BACK_THM]
    THEN1 (IMP_RES_TAC BS_PLUS_BACK_THM
        THEN `s' = s''` by fs [Once bs_l1_cases]
        THEN `n = n1` by fs [Once bs_l1_cases]
        THEN rw []
        THEN RES_TAC
        THEN `bs_l1 (L1_Value (L1_Int n), s) (L1_Int n) s` by METIS_TAC [bs_l1_cases]
        THEN METIS_TAC [])
    THEN1 (fs [Once bs_l1_cases]
        THEN rw [Once bs_l1_cases])
    THEN1 METIS_TAC [BS_GEQ_BACK_THM]
    THEN1 (IMP_RES_TAC BS_GEQ_BACK_THM
        THEN `s' = s''` by fs [Once bs_l1_cases]
        THEN `n = n1` by fs [Once bs_l1_cases]
        THEN rw []
        THEN RES_TAC
        THEN `bs_l1 (L1_Value (L1_Int n), s) (L1_Int n) s` by METIS_TAC [bs_l1_cases]
        THEN METIS_TAC [])
    THEN1 fs [Once bs_l1_cases]
    THEN1 (fs [Once bs_l1_cases]
        THEN rw [Once bs_l1_cases])
    THEN1 fs [Once bs_l1_cases]
    THEN1 fs [Once bs_l1_cases]
    THEN1 (IMP_RES_TAC BS_ASSIGN_BACK_THM
        THEN `FDOM s = FDOM s'` by METIS_TAC [DOMAIN_CONSTANT_THM, SND]
        THEN rw []
        THEN METIS_TAC [])
    THEN1 (`bs_l1 (L1_Value L1_Skip, s) L1_Skip s` by METIS_TAC [bs_l1_cases]
         THEN METIS_TAC [])
    THEN1 METIS_TAC [BS_SEQ_BACK_THM]
    THEN1 (`bs_l1 (L1_Value (L1_Bool T), s) (L1_Bool T) s` by METIS_TAC [bs_l1_cases] THEN METIS_TAC [])
    THEN1 (`bs_l1 (L1_Value (L1_Bool F), s) (L1_Bool F) s` by METIS_TAC [bs_l1_cases] THEN METIS_TAC [])
    THEN1 METIS_TAC [BS_IF_BACK_THM]
    THEN1 (IMP_RES_TAC BS_IF_BACK_THM
        THEN1 (IMP_RES_TAC BS_SEQ_BACK_THM
            THEN IMP_RES_TAC BS_WHILE_BACK_THM
            THEN rw []
	    THEN METIS_TAC [])
	THEN IMP_RES_TAC BS_IF_BACK_THM
        THEN IMP_RES_TAC BS_SEQ_BACK_THM
        THEN IMP_RES_TAC BS_WHILE_BACK_THM
        THEN IMP_RES_TAC BS_VALUE_BACK_THM
        THEN `bs_l1 (L1_Value L1_Skip, s'') L1_Skip s''` by METIS_TAC [bs_l1_cases]
        THEN rw []));

val ss_imp_bs_thm = prove(``!p p'.ss_l1^* p p' ==> !x.(FST p' = L1_Value x) ==> bs_l1 p x (SND p')``,
ho_match_mp_tac RTC_STRONG_INDUCT
THEN rw [FST, SND]

THEN1 (Cases_on `FST p` THEN rw [] THEN Cases_on `p` THEN fs [FST] THEN rw [Once bs_l1_cases])
THEN metis_tac [SS_STEP_BS_THM]);


val SS_EQ_BS_THM = store_thm("SS_EQ_BS_THM",
``!p v s'. ss_l1^* p (L1_Value v, s') <=> bs_l1 p v s'``,
rw [EQ_IMP_THM]

THEN1 (imp_res_tac ss_imp_bs_thm
THEN fs [FST])

THEN imp_res_tac bs_imp_ss);

val _ = export_theory ();

