open HolKernel boolLib bossLib listTheory Parse IndDefLib finite_mapTheory relationTheory arithmeticTheory pred_setTheory pairTheory lcsymtacs integerTheory ast_il2Theory smallstep_il2Theory;

val _ = new_theory "smallstep_il2_clocked";

val (exec_clocked_instr_rules, exec_clocked_instr_ind, exec_clocked_instr_cases) = Hol_reln `
(!pc clk stk st.exec_clocked_instr IL2_Nop (SOME (pc, SUC clk, stk, st)) (SOME (pc+1, SUC clk, stk, st))) /\
(!pc stk st instr.exec_clocked_instr instr (SOME (pc, 0, stk, st)) NONE) /\
(!pc clk stk st.exec_clocked_instr IL2_Tick (SOME (pc, SUC clk, stk, st)) (SOME (pc+1, clk, stk, st))) /\
(!n pc clk stk st.exec_clocked_instr (IL2_Push n) (SOME (pc, SUC clk, stk, st)) (SOME (pc+1, SUC clk, n::stk, st))) /\
(!l pc clk stk st.l ∈ FDOM st ==> exec_clocked_instr (IL2_Load l) (SOME (pc, SUC clk, stk, st)) (SOME (pc+1, SUC clk, (st ' l)::stk, st))) /\
(!l pc clk v stk st.exec_clocked_instr (IL2_Store l) (SOME (pc, SUC clk, v::stk, st)) (SOME (pc+1, SUC clk, stk, st |+ (l, v)))) /\
(!pc clk v stk st.exec_clocked_instr IL2_Pop (SOME (pc, SUC clk, v::stk, st)) (SOME (pc+1, SUC clk, stk, st))) /\
(!pc clk v1 v2 stk st.exec_clocked_instr IL2_Plus (SOME (pc, SUC clk, v1::v2::stk, st)) (SOME (pc+1, SUC clk, (v1+v2)::stk, st))) /\
(!pc clk stk st.exec_clocked_instr IL2_Halt (SOME (pc, SUC clk, stk, st)) (SOME (pc, SUC clk, stk, st))) /\
(!n pc clk stk st.exec_clocked_instr (IL2_Jump n) (SOME (pc, SUC clk, stk, st)) (SOME (pc + 1 + n, SUC clk, stk, st))) /\
(!n pc clk stk st.exec_clocked_instr (IL2_Jz n) (SOME (pc, SUC clk, 0::stk, st)) (SOME (pc + 1 + n, SUC clk, stk, st))) /\
(!n pc clk t stk st.(t <> 0) ==> exec_clocked_instr (IL2_Jz n) (SOME (pc, SUC clk, t::stk, st)) (SOME (pc + 1, SUC clk, stk, st))) /\
(!v1 v2 pc clk stk st.(v1 >= v2) ==> exec_clocked_instr IL2_Geq (SOME (pc, SUC clk, v1::v2::stk, st)) (SOME (pc + 1, SUC clk, true_value::stk, st))) /\
(!v1 v2 pc clk stk st.(v1 < v2) ==> exec_clocked_instr IL2_Geq (SOME (pc, SUC clk, v1::v2::stk, st)) (SOME (pc + 1, SUC clk, false_value::stk, st)))`;

val (exec_clocked_one_rules, exec_clocked_one_ind, exec_clocked_one_cases) = Hol_reln `
!instrs pc clk stk st r.
       ((pc >= 0) /\ (pc < &(LENGTH instrs)) /\
        (exec_clocked_instr (instrs !! pc) (SOME (pc, clk, stk, st)) r))
    ==> exec_clocked_one instrs (SOME (pc, clk, stk, st)) r
`;

val exec_clocked_def = Define `exec_clocked P c c' = (exec_clocked_one P)^* c c'`;

val _ = export_theory ();
