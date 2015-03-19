open HolKernel bossLib Parse boolLib listTheory lcsymtacs smallstep_il2Theory relationTheory ast_vsm0Theory integerTheory;

val _ = new_theory "smallstep_vsm0";

val fetch_rev_def = Define `fetch_rev l n = (REVERSE l) !! &n`;

val _ = Parse.overload_on("??", ``fetch_rev``);

val _ = Parse.set_fixity "??" (Infix (NONASSOC, 402));

val update_loc_def = Define `update_loc stk l v = REVERSE (LUPDATE v l (REVERSE stk))`;

val (vsm_exec_instr_rules, vsm_exec_instr_ind, vsm_exec_instr_cases) = Hol_reln `
(!pc stk.vsm_exec_instr VSM_Nop (pc, stk) (pc+1, stk)) /\
(!pc stk.vsm_exec_instr VSM_Tick (pc, stk) (pc+1, stk)) /\
(!n pc stk.vsm_exec_instr (VSM_Push n) (pc, stk) (pc+1, n::stk)) /\
(!l pc stk.vsm_exec_instr (VSM_Load l) (pc, stk) (pc+1, (stk ?? l)::stk)) /\
(!l pc v stk.vsm_exec_instr (VSM_Store l) (pc, v::stk) (pc+1, update_loc stk l v)) /\
(!pc v stk.vsm_exec_instr VSM_Pop (pc, v::stk) (pc+1, stk)) /\
(!pc v1 v2 stk.vsm_exec_instr VSM_Plus (pc, v1::v2::stk) (pc+1, (v1+v2)::stk)) /\
(!pc stk.vsm_exec_instr VSM_Halt (pc, stk) (pc, stk)) /\
(!n pc stk.vsm_exec_instr (VSM_Jump n) (pc, stk) (pc + 1 + n, stk)) /\
(!n pc stk.vsm_exec_instr (VSM_Jz n) (pc, 0::stk) (pc + 1 + n, stk)) /\
(!n pc t stk.(t <> 0) ==> vsm_exec_instr (VSM_Jz n) (pc, t::stk) (pc + 1, stk)) /\
(!v1 v2 pc stk.(v1 >= v2) ==> vsm_exec_instr (VSM_Geq) (pc, v1::v2::stk) (pc + 1, true_value::stk)) /\
(!v1 v2 pc stk.(v1 < v2) ==> vsm_exec_instr (VSM_Geq) (pc, v1::v2::stk) (pc + 1, false_value::stk))`;

val (vsm_exec_one_rules, vsm_exec_one_ind, vsm_exec_one_cases) = Hol_reln `
!instrs pc stk pc' stk'.
       ((pc >= 0) /\ (pc < &(LENGTH instrs)) /\
        (vsm_exec_instr (instrs !! pc) (pc, stk) (pc', stk')))
    ==> vsm_exec_one instrs (pc, stk) (pc', stk')`;

val vsm_exec_def = Define `vsm_exec P c c' = (vsm_exec_one P)^* c c'`;

val _ = export_theory ();
