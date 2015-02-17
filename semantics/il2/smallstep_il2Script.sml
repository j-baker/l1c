open HolKernel boolLib bossLib listTheory Parse IndDefLib finite_mapTheory relationTheory arithmeticTheory pred_setTheory pairTheory lcsymtacs integerTheory ast_il2Theory;

val _ = new_theory "smallstep_il2";

val fetch_def = Define `fetch (x::xs) n = if n = &0 then x else fetch xs (n-1)`;

val _ = Parse.overload_on("!!", ``fetch``);

val _ = Parse.set_fixity "!!" (Infix (NONASSOC, 401));

val true_value_def = Define `true_value = 1`;

val false_value_def = Define `false_value = 0`;

val skip_value_def = Define `skip_value = 0`;

val (exec_instr_rules, exec_instr_ind, exec_instr_cases) = Hol_reln `
(!pc stk st.exec_instr IL2_Nop (pc, stk, st) (pc+1, stk, st)) /\
(!n pc stk st.exec_instr (IL2_Push n) (pc, stk, st) (pc+1, n::stk, st)) /\
(!l pc stk st.l ∈ FDOM st ==> exec_instr (IL2_Load l) (pc, stk, st) (pc+1, (st ' l)::stk, st)) /\
(!l pc v stk st.exec_instr (IL2_Store l) (pc, v::stk, st) (pc+1, stk, st |+ (l, v))) /\
(!pc v stk st.exec_instr IL2_Pop (pc, v::stk, st) (pc+1, stk, st)) /\
(!pc v1 v2 stk st.exec_instr IL2_Plus (pc, v1::v2::stk, st) (pc+1, (v1+v2)::stk, st)) /\
(!pc stk st.exec_instr IL2_Halt (pc, stk, st) (pc, stk, st)) /\
(!n pc stk st.exec_instr (IL2_Jump n) (pc, stk, st) (pc + 1 + n, stk, st)) /\
(!n pc stk st.exec_instr (IL2_Jz n) (pc, 0::stk, st) (pc + 1 + n, stk, st)) /\
(!n pc t stk st.(t <> 0) ==> exec_instr (IL2_Jz n) (pc, t::stk, st) (pc + 1, stk, st)) /\
(!v1 v2 pc stk st.(v1 >= v2) ==> exec_instr (IL2_Geq) (pc, v1::v2::stk, st) (pc + 1, true_value::stk, st)) /\
(!v1 v2 pc stk st.(v1 < v2) ==> exec_instr (IL2_Geq) (pc, v1::v2::stk, st) (pc + 1, false_value::stk, st))`;

val (exec_one_rules, exec_one_ind, exec_one_cases) = Hol_reln `
!instrs pc stk st pc' stk' st'.
       ((pc >= 0) /\ (pc < &(LENGTH instrs)) /\
        (exec_instr (instrs !! pc) (pc, stk, st) (pc', stk', st')))
    ==> exec_one instrs (pc, stk, st) (pc', stk', st')`;

val exec_def = Define `exec P c c' = (exec_one P)^* c c'`;

val _ = export_theory ();
