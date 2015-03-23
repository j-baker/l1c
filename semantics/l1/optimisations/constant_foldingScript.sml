open ast_l1Theory bigstep_l1_clockedTheory pairTheory lcsymtacs boolLib bossLib HolKernel bigstep_determinacyTheory

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
					| x => L1_While x (cfold e2))
`;

val while_true_div = prove(``!c s.bs_l1_c c (L1_While (L1_Value (L1_Bool T)) (L1_Value L1_Skip), s) NONE``,
Induct_on `c` THEN rw [Once bs_l1_c_cases] THEN DISJ2_TAC THEN DISJ2_TAC THEN1 (DISJ1_TAC THEN Q.LIST_EXISTS_TAC [`0`, `s`, `s`] THEN rw [] THEN rw [Once bs_l1_c_cases])
THEN 
DISJ2_TAC
 THEN Q.LIST_EXISTS_TAC [`SUC c`, `c`, `s`, `s`] THEN rw [] THEN rw [Once bs_l1_c_cases]);

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

THEN (Cases_on `cfold e1` THEN fs [] THEN rw [] THEN1 (Cases_on `l` THEN rw [] THEN fs [Q.SPECL [`A`, `L1_Value A, B`] bs_l1_c_cases] THEN rw [] THEN rw [Once bs_l1_c_cases] THEN metis_tac [bs_l1_c_cases]) THEN rw [Once bs_l1_c_cases] THEN metis_tac []));

val _ = export_theory ()
