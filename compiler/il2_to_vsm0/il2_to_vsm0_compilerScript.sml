 open HolKernel bossLib Parse boolLib listTheory lcsymtacs ast_vsm0Theory ast_il2Theory finite_mapTheory;

val _ = new_theory "il2_to_vsm0_compiler";

val get_locations_def = Define `
(get_locations [] = []) /\
(get_locations ((IL2_Store l)::stms) = l::(get_locations stms)) /\
(get_locations ((IL2_Load l)::stms) = l::(get_locations stms)) /\
(get_locations (_::stms) = get_locations stms)`;

val locs_to_map_def = Define `
(locs_to_map [] = (FEMPTY,(0:num))) /\
(locs_to_map (l::ls) = let (map, next_loc) = locs_to_map ls
                        in (if l ∈ FDOM map then (map, next_loc) else (map |+ (l, next_loc), next_loc + 1)))`;

val make_loc_map_def = Define `make_loc_map il2_prog = (locs_to_map (get_locations il2_prog))`;

val il2_to_vsm0m_def = Define `
(il2_to_vsm0m m IL2_Nop = VSM_Nop) /\
(il2_to_vsm0m m (IL2_Push x) = VSM_Push x) /\
(il2_to_vsm0m m (IL2_Store x) = VSM_Store (m ' x)) /\
(il2_to_vsm0m m (IL2_Load x) = VSM_Load (m ' x)) /\
(il2_to_vsm0m m IL2_Pop = VSM_Pop) /\
(il2_to_vsm0m m IL2_Plus = VSM_Plus) /\
(il2_to_vsm0m m IL2_Geq = VSM_Geq) /\
(il2_to_vsm0m m IL2_Halt = VSM_Halt) /\
(il2_to_vsm0m m (IL2_Jump n) = (VSM_Jump n)) /\
(il2_to_vsm0m m (IL2_Jz n) = VSM_Jz n)`;

val repeatn_def = Define `(repeatn 0 _ = []) /\ (repeatn (SUC n) x = x::(repeatn n x))`;

val il2_to_vsm0_def = Define `il2_to_vsm0 prog = let (map,  num_locs) = (locs_to_map (get_locations prog)) in
((repeatn num_locs (VSM_Push 0)) ++ (MAP (il2_to_vsm0m map) prog))`;

val _ = export_theory ();
