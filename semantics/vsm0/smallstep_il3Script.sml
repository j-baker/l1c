open HolKernel bossLib boolLib ast_vsm0Theory relationTheory finite_mapTheory integerTheory smallstep_il2Theory;

val _ = new_theory "smallstep_il3";


val (exec_il3_instr_rules, exec_il3_instr_ind, exec_il3_instr_cases) = Hol_reln `
(!pc stk st.exec_il3_instr VSM_Nop (pc, stk, st) (pc+1, stk, st)) /\
(!pc stk st.exec_il3_instr VSM_Tick (pc, stk, st) (pc+1, stk, st)) /\
(!n pc stk st.exec_il3_instr (VSM_Push n) (pc, stk, st) (pc+1, n::stk, st)) /\
(!l pc stk st.l ∈ FDOM st ==> exec_il3_instr (VSM_Load l) (pc, stk, st) (pc+1, (st ' l)::stk, st)) /\
(!l pc v stk st.exec_il3_instr (VSM_Store l) (pc, v::stk, st) (pc+1, stk, st |+ (l, v))) /\
(!pc v stk st.exec_il3_instr VSM_Pop (pc, v::stk, st) (pc+1, stk, st)) /\
(!pc v1 v2 stk st.exec_il3_instr VSM_Plus (pc, v1::v2::stk, st) (pc+1, (v1+v2)::stk, st)) /\
(!pc stk st.exec_il3_instr VSM_Halt (pc, stk, st) (pc, stk, st)) /\
(!n pc stk st.exec_il3_instr (VSM_Jump n) (pc, stk, st) (pc + 1 + n, stk, st)) /\
(!n pc stk st.exec_il3_instr (VSM_Jz n) (pc, 0::stk, st) (pc + 1 + n, stk, st)) /\
(!n pc t stk st.(t <> 0) ==> exec_il3_instr (VSM_Jz n) (pc, t::stk, st) (pc + 1, stk, st)) /\
(!v1 v2 pc stk st.(v1 >= v2) ==> exec_il3_instr (VSM_Geq) (pc, v1::v2::stk, st) (pc + 1, true_value::stk, st)) /\
(!v1 v2 pc stk st.(v1 < v2) ==> exec_il3_instr (VSM_Geq) (pc, v1::v2::stk, st) (pc + 1, false_value::stk, st))`;


val (exec_il3_one_rules, exec_il3_one_ind, exec_il3_one_cases) = Hol_reln `
!instrs pc stk st pc' stk' st'.
       ((pc >= 0) /\ (pc < &(LENGTH instrs)) /\
        (exec_il3_instr (instrs !! pc) (pc, stk, st) (pc', stk', st')))
    ==> exec_il3_one instrs (pc, stk, st) (pc', stk', st')`;

val exec_il3_def = Define `exec_il3 P c c' = (exec_il3_one P)^* c c'`;

val _ = export_theory ();
