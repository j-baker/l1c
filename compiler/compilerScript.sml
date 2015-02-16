open HolKernel boolLib bossLib l1_to_il1_compilerTheory il1_to_il2_compilerTheory store_creationTheory il1_il2_correctnessTheory l1_il1_correctnessTheory lcsymtacs il2_to_il3_compilerTheory listTheory pairTheory pred_setTheory;

val _ = new_theory "compiler"

val compile_il2_def = Define `compile_il2 e = il1_to_il2 (l1_to_il1 e 0)`;

val compile_def = Define `compile e = il2_to_il3 (compile_il2 e)`;

val create_il2_store_def = Define `
(create_il2_store [] = FEMPTY) /\
(create_il2_store (IL2_Store l::xs) = (create_il2_store xs) |+ (l, 0)) /\
(create_il2_store (IL2_Load l::xs) = (create_il2_store xs) |+ (l, 0)) /\
(create_il2_store (_::xs) = (create_il2_store xs))`;

val ms_il2_st_thm = prove(``!e.ms_il2 e (create_il2_store e)``,

Induct_on `e` THEN rw [ms_il2_def, create_il2_store_def, make_loc_map_def, locs_to_map_def, get_locations_def, FST]

THEN Cases_on `h` THEN fs [create_il2_store_def, get_locations_def] THEN rw [] THEN fs [make_loc_map_def, ms_il2_def]

THEN fs [locs_to_map_def]

THEN `?m n.locs_to_map (get_locations e) = (m, n)` by metis_tac [locs_to_map_total_thm]

THEN rw [LET_DEF]

THEN metis_tac [ABSORPTION_RWT]);

(* Weaker but sufficient thm follows immediately from L1_IL1_CORRECTNESS_LEMMA *)
val il2_equiv_thm = prove(``!e st1 pc v st1' st2. exec (compile_il2 e) (0, [], st1) (pc, [v], st1') /\ equiv st1 st2 ==> ?st2'.
exec (compile_il2 e) (0, [], st2) (pc, [v], st2') /\ equiv st1' st2'``, cheat);

val store_equiv_gen_thm = prove(``!e.equiv (con_store (create_store e)) (create_il2_store (compile_il2 e))``, cheat);

val TOTAL_CORRECTNESS_THM = store_thm("TOTAL_CORRECTNESS_THM",
``!e v s'.bs_l1 (e, create_store e) v s' ==> ?s''.exec (compile_il2 e) (0, [], con_store (create_store e)) (&LENGTH (compile_il2 e), [(il1_il2_val (l1_il1_val v))], s'')``,
metis_tac [compile_il2_def, L1_TO_IL1_EXISTS_CORRECTNESS_THM, CORRECTNESS_THM]);

val length_prog_thm = prove(``!e.LENGTH (compile e) = LENGTH (compile_il2 e)``, rw [compile_def, compile_il2_def, il2_to_il3_def]);

val make_stack_def = Define `make_stack e = astack (compile e)
            (MAP_KEYS (map_fun (FST (make_loc_map (compile_il2 e))))
               (create_il2_store (compile_il2 e))) []`;

val total_c_lem = prove(``!e v s'.
    bs_l1 (e, create_store e) v s' ==> 
    ?astk.
        vsm_exec (compile e) (0, make_stack e) (&LENGTH (compile e), (il1_il2_val (l1_il1_val v))::astk)``,

rw [make_stack_def]

THEN imp_res_tac TOTAL_CORRECTNESS_THM

THEN `equiv (con_store (create_store e)) (create_il2_store (compile_il2 e))` by metis_tac [store_equiv_gen_thm]

THEN imp_res_tac il2_equiv_thm

THEN `ms_il2 (compile_il2 e) (create_il2_store (compile_il2 e))` by metis_tac [ms_il2_st_thm]

THEN imp_res_tac il2_vsm_correctness

THEN `?atsk.astk''' = (il1_il2_val (l1_il1_val v))::atsk` by (Cases_on `astk'''` THEN fs [TAKE_def]
THEN Cases_on `n''' = 0` THEN fs [])

THEN metis_tac [compile_def, length_prog_thm]);

val _ = export_theory ();
