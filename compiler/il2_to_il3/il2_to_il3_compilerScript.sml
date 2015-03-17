open HolKernel bossLib boolLib Parse ast_il2Theory ast_vsm0Theory lcsymtacs pairTheory finite_mapTheory pred_setTheory integerTheory smallstep_il2Theory relationTheory listTheory smallstep_vsm0Theory arithmeticTheory smallstep_il3Theory;

val _ = new_theory "il2_to_il3_compiler";

val il2_to_il3m_def = Define `
(il2_to_il3m m IL2_Nop = VSM_Nop) /\
(il2_to_il3m m IL2_Tick = VSM_Tick) /\
(il2_to_il3m m (IL2_Push x) = VSM_Push x) /\
(il2_to_il3m m (IL2_Store x) = VSM_Store (m ' x)) /\
(il2_to_il3m m (IL2_Load x) = VSM_Load (m ' x)) /\
(il2_to_il3m m IL2_Pop = VSM_Pop) /\
(il2_to_il3m m IL2_Plus = VSM_Plus) /\
(il2_to_il3m m IL2_Geq = VSM_Geq) /\
(il2_to_il3m m IL2_Halt = VSM_Halt) /\
(il2_to_il3m m (IL2_Jump n) = (VSM_Jump n)) /\
(il2_to_il3m m (IL2_Jz n) = VSM_Jz n)`;

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

val il2_to_il3_def = Define `il2_to_il3 P = MAP (il2_to_il3m (FST (make_loc_map P))) P`;

val _ = export_theory ();
