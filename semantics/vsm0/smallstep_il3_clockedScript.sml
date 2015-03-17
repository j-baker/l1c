open HolKernel boolLib bossLib listTheory Parse IndDefLib finite_mapTheory relationTheory arithmeticTheory pred_setTheory pairTheory lcsymtacs integerTheory ast_vsm0Theory smallstep_il2Theory;

val _ = new_theory "smallstep_il3_clocked";

val (exec_il3_c_instr_rules, exec_il3_c_instr_ind, exec_il3_c_instr_cases) = Hol_reln `
(!pc clk stk st.exec_il3_c_instr VSM_Nop (SOME (pc, clk, stk, st)) (SOME (pc+1, clk, stk, st))) /\
(!pc stk st.exec_il3_c_instr VSM_Tick (SOME (pc, 0, stk, st)) NONE) /\
(!pc clk stk st.exec_il3_c_instr VSM_Tick (SOME (pc, SUC clk, stk, st)) (SOME (pc+1, clk, stk, st))) /\
(!n pc clk stk st.exec_il3_c_instr (VSM_Push n) (SOME (pc, clk, stk, st)) (SOME (pc+1, clk, n::stk, st))) /\
(!l pc clk stk st.l ∈ FDOM st ==> exec_il3_c_instr (VSM_Load l) (SOME (pc, clk, stk, st)) (SOME (pc+1, clk, (st ' l)::stk, st))) /\
(!l pc clk v stk st.exec_il3_c_instr (VSM_Store l) (SOME (pc, clk, v::stk, st)) (SOME (pc+1, clk, stk, st |+ (l, v)))) /\
(!pc clk v stk st.exec_il3_c_instr VSM_Pop (SOME (pc, clk, v::stk, st)) (SOME (pc+1, clk, stk, st))) /\
(!pc clk v1 v2 stk st.exec_il3_c_instr VSM_Plus (SOME (pc, clk, v1::v2::stk, st)) (SOME (pc+1, clk, (v1+v2)::stk, st))) /\
(!pc clk stk st.exec_il3_c_instr VSM_Halt (SOME (pc, clk, stk, st)) (SOME (pc, clk, stk, st))) /\
(!n pc clk stk st.exec_il3_c_instr (VSM_Jump n) (SOME (pc, clk, stk, st)) (SOME (pc + 1 + n, clk, stk, st))) /\
(!n pc clk stk st.exec_il3_c_instr (VSM_Jz n) (SOME (pc, clk, 0::stk, st)) (SOME (pc + 1 + n, clk, stk, st))) /\
(!n pc clk t stk st.(t <> 0) ==> exec_il3_c_instr (VSM_Jz n) (SOME (pc, clk, t::stk, st)) (SOME (pc + 1, clk, stk, st))) /\
(!v1 v2 pc clk stk st.(v1 >= v2) ==> exec_il3_c_instr VSM_Geq (SOME (pc, clk, v1::v2::stk, st)) (SOME (pc + 1, clk, true_value::stk, st))) /\
(!v1 v2 pc clk stk st.(v1 < v2) ==> exec_il3_c_instr VSM_Geq (SOME (pc, clk, v1::v2::stk, st)) (SOME (pc + 1, clk, false_value::stk, st)))`;

val (exec_il3_c_one_rules, exec_il3_c_one_ind, exec_il3_c_one_cases) = Hol_reln `
!instrs pc clk stk st r.
       ((pc >= 0) /\ (pc < &(LENGTH instrs)) /\
        (exec_il3_c_instr (instrs !! pc) (SOME (pc, clk, stk, st)) r))
    ==> exec_il3_c_one instrs (SOME (pc, clk, stk, st)) r
`;

val exec_il3_c_def = Define `exec_clocked P c c' = (exec_il3_c_one P)^* c c'`;

val _ = export_theory ();
