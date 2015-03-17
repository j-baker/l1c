open ast_il1Theory bigstep_il1Theory bigstep_il1_clockedTheory HolKernel Parse boolLib bossLib integerTheory finite_mapTheory lcsymtacs pairTheory l1_to_il1_compilerTheory l1_il1_correctnessTheory bigstep_il1Theory bigstep_l1_clockedTheory bigstep_l1Theory clocked_unclocked_il1_equivTheory clocked_equivTheory l1_il1_totalTheory store_equivalenceTheory;

val _ = new_theory "l1_il1_clock";

val dud_diverge_thm = prove(``!e s.(!c.bs_l1_c c (e, s) NONE) ==> !tc. bs_il1_c tc (l1_to_il1 e 0, con_store s) NONE``, cheat);

val bs_il1_c_det_thm = prove(``!c p r r'.bs_il1_c c p r /\ bs_il1_c c p r' ==> (r = r')``, cheat);


val lem1 = prove(``!e s.(?c r.bs_l1_c c (e, s) (SOME r)) <=> ~(!c.bs_l1_c c (e, s) NONE)``, cheat);

val lem2 = prove(``!e s.(?c r.bs_il1_c c (e, s) (SOME r)) <=> ~(!c.bs_il1_c c (e, s) NONE)``, cheat);

val lem3 = prove(``!e s.(!v s'.~bs_l1 (e, s) v s') <=> ~(?c r.bs_l1_c c (e, s) (SOME r))``, cheat);

val lem4 = prove(``!e s.(!c.bs_il1_c c (e, s) NONE) ==> (!v s'.¬bs_il1 (e, s) v s')``, cheat);


val cor_oneway = prove(``!e s.(~?v s'. bs_l1 (e, s) v s') ==> (~?v s'.bs_il1 (l1_to_il1 e 0, con_store s) v s')``,
rw []

THEN `!c.bs_l1_c c (e, s) NONE` by metis_tac [lem3, lem1]

THEN imp_res_tac dud_diverge_thm

THEN CCONTR_TAC THEN fs []

THEN imp_res_tac UNCLOCKED_IMP_CLOCKED_IL1

THEN `∃cl.
          bs_il1_c (SUC cl) (l1_to_il1 e 0,con_store s)
            (SOME (v,s',SUC 0))` by metis_tac []

THEN `bs_il1_c (SUC cl) (l1_to_il1 e 0,con_store s) NONE` by metis_tac []
THEN imp_res_tac bs_il1_c_det_thm

THEN rw []);

val correctness_thm = prove(``!e s.(~?v s'. bs_l1 (e, s) v s') <=> (~?v s'.bs_il1 (l1_to_il1 e 0, con_store s) v s')``,
metis_tac [EQ_IMP_THM, cor_oneway, L1_TO_IL1_EXISTS_CORRECTNESS_THM]);

val _ = export_theory ();
