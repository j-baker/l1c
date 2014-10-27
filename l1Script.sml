open HolKernel boolLib bossLib wordsTheory wordsLib listTheory Parse IndDefLib finite_mapTheory;

val _ = new_theory "l1";

val _ = numLib.prefer_num();
val _ = wordsLib.prefer_word();

val _ = type_abbrev("loc", ``:word24``);

val _ = type_abbrev("int", ``:word16``);

val _ = type_abbrev("state", ``:loc |-> int``);

val _ = type_abbrev("pred", ``:state -> bool``);

val _ = Hol_datatype `exp = N of int
                        | B of bool
                        | Plus of exp => exp
                        | Geq of exp => exp
                        | If of exp => exp => exp
                        | Assign of loc => exp
                        | Deref of loc
                        | Skip
                        | Seq of exp => exp
                        | While of exp => exp`;

val (ss_rules, ss_induction, ss_ecases) = Hol_reln `
    (* Plus *)
    (!n1 n2 s.small_step (Plus (N n1) (N n2), s) (N (n1 + n2), s)) /\
    (!e1 e1' e2 s s'.
          small_step (e1, s) (e1', s')
      ==> small_step (Plus e1 e2, s) (Plus e1' e2, s')) /\
    (!n e2 e2' s s'.
          small_step (e2, s) (e2', s')
      ==> small_step (Plus (N n) e2, s) (Plus (N n) e2', s')) /\

    (* Geq *)
    (!n1 n2 s.small_step (Geq (N n1) (N n2), s) (B (n1 >= n2), s)) /\
    (!e1 e1' e2 s s'.
          small_step (e1, s) (e1', s')
      ==> small_step (Geq e1 e2, s) (Geq e1' e2, s')) /\
    (!n e2 e2' s s'.
          small_step (e2, s) (e2', s')
      ==> small_step (Geq (N n) e2, s) (Geq (N n) e2', s')) /\

    (* Deref *)
    (!l s.
          l ∈ FDOM s
      ==> small_step (Deref(l), s) (N (s ' l), s)) /\

    (* Assign *)
    (!l n s.
          l ∈ FDOM s
      ==> small_step (Assign l (N n), s) (Skip, s |+ (l, n))) /\
    (!l e e' s s'.
          small_step (e, s) (e', s')
      ==> small_step (Assign l e, s) (Assign l e', s')) /\

    (* Seq *)
    (!e2 s.small_step (Seq Skip e2, s) (e2, s)) /\
    (!e1 e1' e2 s s'.
          small_step (e1, s) (e1', s')
      ==> small_step (Seq e1 e2, s) (Seq e1' e2, s')) /\

    (* If *)
    (!e2 e3 s. small_step (If (B T) e2 e3, s) (e2, s)) /\
    (!e2 e3 s. small_step (If (B F) e2 e3, s) (e3, s)) /\
    (!e1 e1' e2 e3 s s'.
          small_step (e1, s) (e1', s')
      ==> small_step (If e1 e2 e3, s) (If e1' e2 e3, s')) /\

    (* While *)
    (!e1 e2 s. small_step (While e1 e2, s) (If e1 (Seq e2 (While e1 e2)) Skip, s))`;

val sinduction = derive_strong_induction(ss_rules, ss_induction);

val ss_rulel = CONJUNCTS ss_rules;

val small_step_fun_def = Define `
    (* Values *)
    (small_step_fun ((N _), _) = NONE) /\
    (small_step_fun ((B _), _) = NONE) /\
    (small_step_fun (Skip,_)   = NONE) /\

    (* Plus *)
    (small_step_fun (Plus (N n1) (N n2), s) = SOME (N (n1 + n2), s)) /\
    (small_step_fun (Plus (N n1) e2, s) = (case (small_step_fun (e2, s)) of
					         SOME (e2',s') => SOME (Plus (N n1) e2', s')
					       | NONE => NONE)) /\
    (small_step_fun (Plus e1 e2, s) = (case (small_step_fun (e1, s)) of
                                                 SOME (e1',s') => SOME (Plus e1' e2, s')
					       | NONE => NONE)) /\

    (* Geq *)
    (small_step_fun (Geq (N n1) (N n2), s) = SOME (B (n1 >= n2), s)) /\
    (small_step_fun (Geq (N n1) e2, s) = (case (small_step_fun (e2, s)) of
					         SOME (e2',s') => SOME (Geq (N n1) e2', s')
					       | NONE => NONE)) /\
    (small_step_fun (Geq e1 e2, s) = (case (small_step_fun (e1, s)) of
                                                 SOME (e1',s') => SOME (Geq e1' e2, s')
					       | NONE => NONE)) /\

    (* Deref *)
    (small_step_fun (Deref l, s) = if (l ∈ FDOM s) then SOME (N (s ' l), s) else NONE) /\

    (* Assign *)
    (small_step_fun (Assign l (N n), s) = if (l ∈ FDOM s) then (SOME (Skip, s |+ (l, n))) else NONE) /\
    (small_step_fun (Assign l e, s) = (case (small_step_fun (e, s)) of
                                              SOME (e', s') => SOME (Assign l e', s')
					    | NONE => NONE)) /\

    (* Seq *)
    (small_step_fun (Seq Skip e2, s) = SOME (e2, s)) /\
    (small_step_fun (Seq e1 e2, s) = (case (small_step_fun (e1, s)) of
                                              SOME (e1', s') => SOME (Seq e1' e2, s')
					    | NONE => NONE)) /\

    (* If *)
    (small_step_fun (If (B T) e2 _, s) = SOME (e2, s)) /\
    (small_step_fun (If (B F) _ e3, s) = SOME (e3, s)) /\
    (small_step_fun (If e1 e2 e3, s) = (case (small_step_fun (e1, s)) of
                                              SOME (e1', s') => SOME (If e1' e2 e3, s')
					    | NONE => NONE)) /\

    (* While *)
    (small_step_fun (While e1 e2, s) = SOME (If e1 (Seq e2 (While e1 e2)) Skip, s))`;

val NO_STEP_FROM_INT_THM = store_thm("NO_STEP_FROM_INT_THM",
    ``!c s.small_step_fun (N c, s) = NONE``, REPEAT STRIP_TAC THEN EVAL_TAC);

val NO_STEP_FROM_BOOL_THM = store_thm("NO_STEP_FROM_INT_THM",
    ``!c s.small_step_fun (B c, s) = NONE``, REPEAT STRIP_TAC THEN EVAL_TAC);

val NO_STEP_FROM_SKIP_THM = store_thm("NO_STEP_FROM_INT_THM",
    ``!s.small_step_fun (Skip, s) = NONE``, REPEAT STRIP_TAC THEN EVAL_TAC);

val ASSIGN_CASE_TAC = (Cases_on `c ∈ FDOM s` THEN1 (EVAL_TAC THEN FULL_SIMP_TAC (srw_ss ()) [] THEN `small_step_fun (Deref c, s) = SOME(N (s ' c), s)` by (EVAL_TAC THEN FULL_SIMP_TAC (srw_ss ()) []) THEN FULL_SIMP_TAC (srw_ss ()) []) THEN1 (`small_step_fun (Deref c, s) = NONE` by (EVAL_TAC THEN FULL_SIMP_TAC (srw_ss ()) []) THEN FULL_SIMP_TAC (srw_ss ()) []));

val WHILE_CASE_TAC = (EVAL_TAC THEN `small_step_fun (While e e0, s) = SOME (If e (Seq e0 (While e e0)) Skip, s)` by (EVAL_TAC THEN FULL_SIMP_TAC (srw_ss ()) []) THEN FULL_SIMP_TAC (srw_ss ()) []);

val ASSIGN_CASE_PLUS_THM = store_thm("ASSIGN_CASE_PLUS_THM",
``!c s e1' s' e2.(small_step_fun (Deref c, s) = SOME (e1', s')) ==> ((case if c ∈ FDOM s then SOME (N (s ' c), s) else NONE of NONE => NONE | SOME (e1', s') => SOME (Plus e1' e2, s')) = SOME (Plus e1' e2, s'))``,
EVAL_TAC THEN FULL_SIMP_TAC (srw_ss ()) []);

val ASSIGN_CASE_PLUS_2_THM = store_thm("ASSIGN_CASE_PLUS_THM",
``!c s n s' e2 e2'.(small_step_fun (Deref c, s) = SOME (e2', s')) ==> ((case if c ∈ FDOM s then SOME (N (s ' c), s) else NONE of NONE => NONE | SOME (e2', s') => SOME (Plus (N n) e2', s')) = SOME (Plus (N n) e2', s'))``,
EVAL_TAC THEN FULL_SIMP_TAC (srw_ss ()) []);

val ASSIGN_CASE_GEQ_THM = store_thm("ASSIGN_CASE_GEQ_THM",
``!c s e1' s' e2.(small_step_fun (Deref c, s) = SOME (e1', s')) ==> ((case if c ∈ FDOM s then SOME (N (s ' c), s) else NONE of NONE => NONE | SOME (e1', s') => SOME (Geq e1' e2, s')) = SOME (Geq e1' e2, s'))``,
EVAL_TAC THEN FULL_SIMP_TAC (srw_ss ()) []);

val ASSIGN_CASE_GEQ2_THM = store_thm("ASSIGN_CASE_PLUS_THM",
``!c s n s' e2 e2'.(small_step_fun (Deref c, s) = SOME (e2', s')) ==> ((case if c ∈ FDOM s then SOME (N (s ' c), s) else NONE of NONE => NONE | SOME (e2', s') => SOME (Geq (N n) e2', s')) = SOME (Geq (N n) e2', s'))``,
EVAL_TAC THEN FULL_SIMP_TAC (srw_ss ()) []);

val ASSIGN_CASE_WHILE_THM = store_thm("ASSIGN_CASE_WHILE_THM",
``!c s e1' s' e2.(small_step_fun (Deref c, s) = SOME (e1', s')) ==> ((case if c ∈ FDOM s then SOME (N (s ' c), s) else NONE of NONE => NONE | SOME (e1', s') => SOME (While e1' e2, s')) = SOME (While e1' e2, s'))``,
EVAL_TAC THEN FULL_SIMP_TAC (srw_ss ()) []);

val ASSIGN_CASE_IF_THM = store_thm("ASSIGN_CASE_IF_THM",
``!c s e1' s' e2 e3.(small_step_fun (Deref c, s) = SOME (e1', s')) ==> ((case if c ∈ FDOM s then SOME (N (s ' c), s) else NONE of NONE => NONE | SOME (e1', s') => SOME (If e1' e2 e3, s')) = SOME (If e1' e2 e3, s'))``,
EVAL_TAC THEN FULL_SIMP_TAC (srw_ss ()) []);

val ASSIGN_CASE_SEQ_THM = store_thm("ASSIGN_CASE_SEQ_THM",
``!c s e1' s' e2.(small_step_fun (Deref c, s) = SOME (e1', s')) ==> ((case if c ∈ FDOM s then SOME (N (s ' c), s) else NONE of NONE => NONE | SOME (e1', s') => SOME (Seq e1' e2, s')) = SOME (Seq e1' e2, s'))``,
EVAL_TAC THEN FULL_SIMP_TAC (srw_ss ()) []);

val ASSIGN_CASE_ASSIGN_THM = store_thm("ASSIGN_CASE_ASSIGN_THM",
``!c s l e' s'.(small_step_fun (Deref c, s) = SOME (e', s')) ==> ((case if c ∈ FDOM s then SOME (N (s ' c), s) else NONE of NONE => NONE | SOME (e', s') => SOME (Assign l e', s')) = SOME (Assign l e', s'))``,
EVAL_TAC THEN FULL_SIMP_TAC (srw_ss ()) []);

val WHILE_CASE_THM = store_thm("WHILE_CASE_THM",
``!e e0 s e1' s'.(small_step_fun (While e e0, s) = SOME (e1', s')) ==> ((If e (Seq e0 (While e e0)) Skip = e1') /\ (s = s'))``, WHILE_CASE_TAC);

fun make_constructor_thm name content case_thm = store_thm(name, content, REPEAT STRIP_TAC THEN Cases_on `e1` THEN EVAL_TAC THEN FULL_SIMP_TAC (srw_ss ()) [NO_STEP_FROM_INT_THM, NO_STEP_FROM_SKIP_THM, NO_STEP_FROM_BOOL_THM] THEN METIS_TAC [WHILE_CASE_THM, case_thm]);

val PLUS_1_CASE_THM = make_constructor_thm "PLUS_1_CASE_THM" ``!e1 s e1' s' e2.(small_step_fun (e1, s) = SOME (e1', s')) ==> (small_step_fun (Plus e1 e2, s) = SOME (Plus e1' e2, s'))`` ASSIGN_CASE_PLUS_THM;

val PLUS_2_CASE_THM = make_constructor_thm "PLUS_2_CASE_THM" ``!e1 s e1' n s'.(small_step_fun (e1, s) = SOME (e1', s')) ==> (small_step_fun (Plus (N n) e1, s) = SOME (Plus (N n) e1', s'))`` ASSIGN_CASE_PLUS_2_THM;

val GEQ_1_CASE_THM = make_constructor_thm "GEQ_1_CASE_THM" ``!e1 s e1' s' e2.(small_step_fun (e1, s) = SOME (e1', s')) ==> (small_step_fun (Geq e1 e2, s) = SOME (Geq e1' e2, s'))`` ASSIGN_CASE_GEQ_THM;

val GEQ_2_CASE_THM = make_constructor_thm "GEQ_2_CASE_THM" ``!e1 s e1' n s'.(small_step_fun (e1, s) = SOME (e1', s')) ==> (small_step_fun (Geq (N n) e1, s) = SOME (Geq (N n) e1', s'))`` ASSIGN_CASE_GEQ2_THM;

val SEQ_1_CASE_THM = make_constructor_thm "SEQ_1_CASE_THM" ``!e1 s e1' s' e2.(small_step_fun (e1, s) = SOME (e1', s')) ==> (small_step_fun (Seq e1 e2, s) = SOME (Seq e1' e2, s'))`` ASSIGN_CASE_SEQ_THM;

val IF_1_CASE_THM = make_constructor_thm "IF_1_CASE_THM" ``!e1 s e1' s' e2 e3.(small_step_fun (e1, s) = SOME (e1', s')) ==> (small_step_fun (If e1 e2 e3, s) = SOME (If e1' e2 e3, s'))`` ASSIGN_CASE_IF_THM;

val ASSIGN_1_CASE_THM = make_constructor_thm "ASSIGN_1_CASE_THM" ``!e1 s e1' s' l.(small_step_fun (e1, s) = SOME (e1', s')) ==> (small_step_fun (Assign l e1, s) = SOME (Assign l e1', s'))`` ASSIGN_CASE_ASSIGN_THM;

val ONE_WAY_EQ_THM = store_thm("ONE_WAY_EQ_THM",
    ``!p1 p2.small_step p1 p2 ==> ((small_step_fun p1) = SOME p2)``,
    HO_MATCH_MP_TAC ss_induction THEN
        REPEAT STRIP_TAC THEN (EVAL_TAC THEN FULL_SIMP_TAC (srw_ss ()) [PLUS_1_CASE_THM, PLUS_2_CASE_THM, GEQ_1_CASE_THM, GEQ_2_CASE_THM, SEQ_1_CASE_THM, IF_1_CASE_THM, ASSIGN_1_CASE_THM]));

val _ = Hol_datatype `T = intL1 | boolL1 | unitL1`;

val _ = Hol_datatype `LT = intrefL1`;

val (type_rules, type_induction, type_ecases) = Hol_reln `
    (!n.type (N n) intL1) /\
    (!b.type (B b) boolL1) /\
    (!e1 e2.(type e1 intL1 /\ type e2 intL1) ==> type (Plus e1 e2) intL1) /\
    (!e1 e2.(type e1 intL1 /\ type e2 intL1) ==> type (Geq e1 e2) boolL1) /\
    (!e1 e2 e3 T.(type e1 boolL1 /\ type e2 T /\ type e3 T) ==> type (If e1 e2 e3) T) /\
    (!l e.type e intL1 ==> type (Assign l e) unitL1) /\
    (!l .type (Deref l) intL1) /\
    (type Skip unitL1) /\
    (!e1 e2 T.type e1 unitL1 /\ type e2 T ==> type (Seq e1 e2) T) /\
    (!e1 e2. type e1 boolL1 /\ type e2 unitL1 ==> type (While e1 e2) unitL1)`;

val value_def = Define `(value (N _) = T) /\
                        (value (B _) = T) /\
                        (value Skip = T) /\
                        (value _ = F)`;

val (star_rules, star_induction, star_ecases) = Hol_reln `
(!x. star r x x) /\
(!x y z.(r x y ==> star r y z) ==> star r x z)`


val STAR_TRANS_THM = store_thm("STAR_TRANS_THM",
``!r x y z. star r x y ==> star r y z ==> star r x z``,
METIS_TAC [star_ecases]);

val evals_def = Define `evals x y = star small_step x y`;

val _ = export_theory ();
