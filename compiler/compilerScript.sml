open HolKernel boolLib bossLib l1_to_il1_compilerTheory il1_to_il2_compilerTheory store_creationTheory il1_il2_correctnessTheory l1_il1_correctnessTheory lcsymtacs;

val _ = new_theory "compiler"

val compile_def = Define `compile e = il1_to_il2 (l1_to_il1 e 0)`;

val TOTAL_CORRECTNESS_THM = store_thm("TOTAL_CORRECTNESS_THM",
``!e v s'.bs_l1 (e, create_store e) v s' ==> ?pc' s''.exec (compile e) (0, [], con_store (create_store e)) (pc', [(il1_il2_val (l1_il1_val v))], s'')``,
metis_tac [compile_def, L1_TO_IL1_EXISTS_CORRECTNESS_THM, CORRECTNESS_THM]);

val _ = export_theory ();
