open HolKernel boolLib bossLib wordsTheory wordsLib listTheory Parse IndDefLib finite_mapTheory relationTheory;

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

val _ = Hol_datatype `bval = B_N of int
                           | B_B of bool
                           | B_Skip`;

val _ = Hol_datatype `bexp = B_Value of bval
                           | B_Plus of bexp => bexp
                           | B_Geq of bexp => bexp
                           | B_If of bexp => bexp => bexp
                           | B_Assign of loc => bexp
                           | B_Deref of loc
                           | B_Seq of bexp => bexp
                           | B_While of bexp => bexp`;

val bs_to_ss_def = Define `
    (bs_to_ss (B_Value (B_N n)) = (N n)) /\
    (bs_to_ss (B_Value (B_B b)) = (B b)) /\
    (bs_to_ss (B_Value (B_Skip)) = Skip) /\
    (bs_to_ss (B_Plus e1 e2) = Plus (bs_to_ss e1) (bs_to_ss e2)) /\
    (bs_to_ss (B_Geq e1 e2) = Geq (bs_to_ss e1) (bs_to_ss e2)) /\
    (bs_to_ss (B_If e1 e2 e3) = If (bs_to_ss e1) (bs_to_ss e2) (bs_to_ss e3)) /\
    (bs_to_ss (B_Assign l e) = Assign l (bs_to_ss e)) /\
    (bs_to_ss (B_Deref l) = Deref l) /\
    (bs_to_ss (B_Seq e1 e2) = Seq (bs_to_ss e1) (bs_to_ss e2)) /\
    (bs_to_ss (B_While e1 e2) = While (bs_to_ss e1) (bs_to_ss e2))`;
    
val ss_to_bs_def = Define `
    (ss_to_bs (N n) = B_Value (B_N n)) /\
    (ss_to_bs (B b) = B_Value (B_B b)) /\
    (ss_to_bs (Skip) = B_Value B_Skip) /\
    (ss_to_bs (Plus e1 e2) = B_Plus (ss_to_bs e1) (ss_to_bs e2)) /\
    (ss_to_bs (Geq e1 e2) = B_Geq (ss_to_bs e1) (ss_to_bs e2)) /\
    (ss_to_bs (If e1 e2 e3) = B_If (ss_to_bs e1) (ss_to_bs e2) (ss_to_bs e3)) /\
    (ss_to_bs (Assign l e) = B_Assign l (ss_to_bs e)) /\
    (ss_to_bs (Deref l) = B_Deref l) /\
    (ss_to_bs (Seq e1 e2) = B_Seq (ss_to_bs e1) (ss_to_bs e2)) /\
    (ss_to_bs (While e1 e2) = B_While (ss_to_bs e1) (ss_to_bs e2))`;

val ss_to_bs_value_def = Define `
    (ss_to_bs_value (N n) = SOME (B_N n)) /\
    (ss_to_bs_value (B b) = SOME (B_B b)) /\
    (ss_to_bs_value (Skip) = SOME (B_Skip)) /\
    (ss_to_bs_value _ = NONE)`;


val REP_EQUALITY_THM = store_thm("REP_EQUALITY_THM",
    ``(!e.(bs_to_ss (ss_to_bs e)) = e) /\ (!e.(ss_to_bs (bs_to_ss e)) = e)``,
    STRIP_TAC
    THEN Induct_on `e`
    THEN EVAL_TAC
    THEN FULL_SIMP_TAC (srw_ss ()) []
    THEN Cases_on `b`
    THEN EVAL_TAC);

val (bs_rules, bs_induction, bs_ecases) = Hol_reln `
    (* Values *)
    (!v s.big_step (B_Value v, s) v s) /\

    (* Plus *)
    (!e1 e2 n1 n2 s s' s''.
        (big_step (e1, s) (B_N n1) s' /\
	 big_step (e2, s') (B_N n2) s'')
     ==> big_step (B_Plus e1 e2, s) (B_N (n1 + n2)) s'') /\

    (* Geq *)
    (!e1 e2 n1 n2 s s' s''.
        (big_step (e1, s) (B_N n1) s' /\
	 big_step (e2, s') (B_N n2) s'')
     ==> big_step (B_Geq e1 e2, s) (B_B (n1 >= n2)) s'') /\

    (* Deref *)
    (!l s.
          l ∈ FDOM s
      ==> big_step (B_Deref(l), s) (B_N (s ' l)) s) /\

    (* Assign *)
    (!l e s n s'.
        (l ∈ FDOM s /\
         big_step (e, s) (B_N n) s')
     ==> big_step (B_Assign l e, s) (B_Skip) (s' |+ (l, n))) /\

    (* Seq *)
    (!e1 e2 v s s' s''.
        (big_step (e1, s) (B_Skip) s' /\
	 big_step (e2, s') v s'')
     ==> big_step (B_Seq e1 e2, s) v s'') /\

    (* If *)
    (!e1 e2 e3 s s' s'' v.
        (big_step (e1, s) (B_B T) s' /\
	 big_step (e2, s') v s'')
     ==> big_step (B_If e1 e2 e3, s) v s'') /\
     
    (!e1 e2 e3 s s' s'' v.
        (big_step (e1, s) (B_B F) s' /\
	 big_step (e3, s') v s'')
     ==> big_step (B_If e1 e2 e3, s) v s'') /\

    (* While *)
    (!e1 e2 s s' s'' s'''.
        (big_step (e1, s) (B_B T) s' /\
	 big_step (e2, s') B_Skip s'' /\
	 big_step (B_While e1 e2, s'') B_Skip s''')
     ==> big_step (B_While e1 e2, s) B_Skip s''') /\

    (!e1 e2 s s'.
         big_step (e1, s) (B_B F) s'
     ==> big_step (B_While e1 e2, s) B_Skip s')`;

val bs_rulel = CONJUNCTS bs_rules;

val bs_sinduction = derive_strong_induction(bs_rules, bs_induction);

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

val REL_IMP_FUN_TAC = (Cases_on `e1` ORELSE Cases_on `e2` ORELSE Cases_on `e`) THEN EVAL_TAC THEN FULL_SIMP_TAC (srw_ss ()) [NO_STEP_FROM_INT_THM, NO_STEP_FROM_SKIP_THM, NO_STEP_FROM_BOOL_THM];

val RELATION_IMPLIES_FUNCTION_THM = store_thm("RELATION_IMPLIES_FUNCTION_THM",
    ``!p1 p2.small_step p1 p2 ==> ((small_step_fun p1) = SOME p2)``,
    HO_MATCH_MP_TAC ss_induction THEN
		    (EVAL_TAC THEN FULL_SIMP_TAC (srw_ss ()) [] THEN REPEAT (STRIP_TAC THEN1 REL_IMP_FUN_TAC)));

val FUNCTION_IMPLIES_RELATION_THM = store_thm("FUNCTION_IMPLIES_RELATION_THM",
    ``!e1 s e1' s'. (small_step_fun (e1, s) = SOME (e1', s')) ==> (small_step (e1, s) (e1', s'))``,
    HO_MATCH_MP_TAC (fetch "-" "small_step_fun_ind") THEN
        REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss [small_step_fun_def]
        THEN FULL_SIMP_TAC (srw_ss ()) [] THEN
        SRW_TAC[][] THEN
	TRY BasicProvers.FULL_CASE_TAC THEN
        FULL_SIMP_TAC (srw_ss ()) [] THEN 
        TRY (Cases_on `x`) THEN
        SRW_TAC[][] THEN
        FULL_SIMP_TAC (srw_ss ()) [] THEN
        RW_TAC (srw_ss ()) [Once ss_ecases]);

val FUNCTION_EQUALS_RELATION_THM = store_thm("FUNCTION_EQUALS_RELATION_THM",
    ``!e1 s e1' s'. (small_step_fun (e1, s) = SOME (e1', s')) <=> (small_step (e1, s) (e1', s'))``,
    RW_TAC (srw_ss ()) [EQ_IMP_THM, FUNCTION_IMPLIES_RELATION_THM, RELATION_IMPLIES_FUNCTION_THM]);

val SMALL_STEP_DETERMINACY_THM = store_thm("SMALL_STEP_DETERMINACY_THM",
    ``!p p' p''.(small_step p p' /\ small_step p p'') ==> (p' = p'')``,
    REPEAT STRIP_TAC THEN
        `small_step_fun p = SOME p'` by METIS_TAC [RELATION_IMPLIES_FUNCTION_THM] THEN
        `small_step_fun p = SOME p''` by METIS_TAC [RELATION_IMPLIES_FUNCTION_THM] THEN
        FULL_SIMP_TAC (srw_ss ()) []);

val _ = Hol_datatype `T = intL1 | boolL1 | unitL1`;

val _ = Hol_datatype `LT = intrefL1`;

val (type_rules, type_induction, type_ecases) = Hol_reln `
    (!n g.type (N n) g intL1) /\
    (!b g.type (B b) g boolL1) /\
    (!e1 e2 g.(type e1 g intL1 /\ type e2 g intL1) ==> type (Plus e1 e2) g intL1) /\
    (!e1 e2 g.(type e1 g intL1 /\ type e2 g intL1) ==> type (Geq e1 e2) g boolL1) /\
    (!e1 e2 e3 g T.(type e1 g boolL1 /\ type e2 g T /\ type e3 g T) ==> type (If e1 e2 e3) g T) /\
    (!l e g.(type e g intL1 /\ l ∈ (FDOM g)) ==> type (Assign l e) g unitL1) /\
    (!l g.l ∈ (FDOM g) ==> type (Deref l) g intL1) /\
    (type Skip g unitL1) /\
    (!e1 e2 T g.type e1 g unitL1 /\ type e2 g T ==> type (Seq e1 e2) g T) /\
    (!e1 e2 g. type e1 g boolL1 /\ type e2 g unitL1 ==> type (While e1 e2) g unitL1)`;

val type_fun_def = Define `
    (type_fun (N n) g = SOME intL1) /\
    (type_fun (B b) g = SOME boolL1) /\
    (type_fun (Plus e1 e2) g = if (type_fun e1 g = SOME intL1) /\ (type_fun e2 g = SOME intL1) then SOME intL1 else NONE) /\
    (type_fun (Geq e1 e2) g = if (type_fun e1 g = SOME intL1) /\ (type_fun e2 g = SOME intL1) then SOME boolL1 else NONE) /\
    (type_fun (If e1 e2 e3) g = if (type_fun e1 g = SOME boolL1) /\ (type_fun e2 g = type_fun e3 g) then type_fun e2 g else NONE) /\
    (type_fun (Assign l e) g = if (l ∈ (FDOM g) /\ (type_fun e g = SOME intL1)) then SOME unitL1 else NONE) /\
    (type_fun (Deref l) g = if (l ∈ (FDOM g)) then SOME intL1 else NONE) /\
    (type_fun (Skip) g = SOME unitL1) /\
    (type_fun (Seq e1 e2) g = if (type_fun e1 g = SOME unitL1) then type_fun e2 g else NONE) /\
    (type_fun (While e1 e2) g = if ((type_fun e1 g = SOME boolL1) /\ (type_fun e2 g = SOME unitL1)) then SOME unitL1 else NONE)`;

val type_sinduction = derive_strong_induction(type_rules, type_induction);

val TYPE_IMP_TYPE_FUN_THM = store_thm("TYPE_IMP_TYPE_FUN_THM",
``!e g t.type e g t ==> (type_fun e g = SOME t)``,
    HO_MATCH_MP_TAC type_induction THEN REPEAT STRIP_TAC THEN (EVAL_TAC THEN FULL_SIMP_TAC (srw_ss ()) []));

val TYPE_FUN_IMP_TYPE_THM = store_thm("TYPE_FUN_IMP_TYPE_THM",
    ``!e g t.(type_fun e g = SOME t) ==> type e g t``,
    Induct_on `e` THEN EVAL_TAC THEN RW_TAC (srw_ss ()) [Once type_ecases] THEN METIS_TAC []);

val TYPE_FUN_EQ_THM = store_thm("TYPE_FUN_EQ_THM",
    ``!e g t.(type_fun e g = SOME t) <=> type e g t``,
    RW_TAC (srw_ss ()) [EQ_IMP_THM, TYPE_FUN_IMP_TYPE_THM, TYPE_IMP_TYPE_FUN_THM]);

val dom_sub_def = Define `dom_sub a b = if !x.x ∈ (FDOM a) ==> x ∈ (FDOM b) then T else F`;

val BOOL_NOT_INT_TYPE_THM = store_thm("BOOL_NOT_INT_TYPE_THM",
    ``!b g.~type (B b) g intL1``, RW_TAC (srw_ss ()) [Once type_ecases]);

val SKIP_NOT_INT_TYPE_THM = store_thm("SKIP_NOT_INT_TYPE_THM",
    ``!g.~type Skip g intL1``, RW_TAC (srw_ss ()) [Once type_ecases]);

val INT_NOT_BOOL_TYPE_THM = store_thm("INT_NOT_BOOL_TYPE_THM",
    ``!n g.~type (N n) g boolL1``, RW_TAC (srw_ss ()) [Once type_ecases]);

val value_def = Define `(value (N _) = T) /\
                        (value (B _) = T) /\
                        (value Skip = T) /\
                        (value _ = F)`;

val L1_PROGRESS_THM = store_thm("L1_PROGRESS_THM",
    ``!e g t. (type e g t) ==> (!s.(dom_sub g s) ==> (value(e) \/ (?e' s'.small_step_fun (e, s) = SOME (e', s'))))``,
    HO_MATCH_MP_TAC type_sinduction
        THEN FULL_SIMP_TAC (srw_ss ()) []
	          THEN RW_TAC (srw_ss ()) []
		  THEN EVAL_TAC
		  THEN (TRY (Cases_on `e`))
		  THEN FULL_SIMP_TAC (srw_ss ()) [value_def, dom_sub_def, SKIP_NOT_INT_TYPE_THM, BOOL_NOT_INT_TYPE_THM, INT_NOT_BOOL_TYPE_THM]
		  THEN (TRY (Cases_on `e'`))
		  THEN FULL_SIMP_TAC (srw_ss ()) [value_def, dom_sub_def, SKIP_NOT_INT_TYPE_THM, BOOL_NOT_INT_TYPE_THM, INT_NOT_BOOL_TYPE_THM]
                  THEN EVAL_TAC
		  THEN RES_TAC
		  THEN RW_TAC (srw_ss ()) []
		  THEN FULL_SIMP_TAC (srw_ss ()) [small_step_fun_def, Once type_ecases]
		  THEN (TRY (Cases_on `b`))
		  THEN EVAL_TAC
		  THEN FULL_SIMP_TAC (srw_ss ()) []);

val evals_def = Define `evals x y = RTC small_step x y`;

val pair_first_def = Define `pair_first (x, _) = x`;
val pair_second_def = Define `pair_second (_, x) = x`;

val DOMAIN_CONSTANT_THM = store_thm("DOMAIN_CONSTANT_THM",
    ``!p1 p2. small_step p1 p2 ==> (FDOM (pair_second p1) = FDOM (pair_second p2))``,
    HO_MATCH_MP_TAC sinduction THEN RW_TAC (srw_ss ()) [pair_second_def, FDOM_EQ_FDOM_FUPDATE]);

val DOMAIN_CONSTANT_STAR_THM = store_thm("DOMAIN_CONSTANT_STAR_THM",
    ``!p1 p2. small_step^* p1 p2 ==> (FDOM (pair_second p1) = FDOM (pair_second p2))``,
    HO_MATCH_MP_TAC RTC_INDUCT THEN METIS_TAC [DOMAIN_CONSTANT_THM]);

val DOM_CONST_2_THM = store_thm("DOM_CONST_2_THM",
    ``!p1 p2. small_step p1 p2 ==> !e.type_fun e (pair_second p1) = type_fun e (pair_second p2)``,
    Cases_on `p1` THEN Cases_on `p2` THEN RW_TAC (srw_ss ()) [pair_second_def] THEN Induct_on `e` THEN EVAL_TAC THEN FULL_SIMP_TAC (srw_ss ()) [] THEN `FDOM r = FDOM r'` by METIS_TAC [DOMAIN_CONSTANT_THM, pair_second_def] THEN METIS_TAC []);

val PROGRESS_LEMMA = store_thm("PROGRESS_LEMMA",
    ``!p p'.small_step p p' ==> (!t.(type_fun (pair_first p) (pair_second p) = SOME t) ==> (type_fun (pair_first p') (pair_second p') = SOME t))``,
    HO_MATCH_MP_TAC sinduction THEN RW_TAC (srw_ss ()) [pair_first_def, pair_second_def] THEN FULL_SIMP_TAC (srw_ss ()) [type_fun_def] THEN RW_TAC (srw_ss ()) [] THEN METIS_TAC [pair_second_def, DOM_CONST_2_THM, DOMAIN_CONSTANT_THM]);

val PROGRESS_THM = store_thm("PROGRESS_THM",
    ``!e s e' s'.small_step (e, s) (e', s') ==> (!t.(type_fun e s = SOME t) ==> (type_fun e' s' = SOME t))``,
    METIS_TAC [PROGRESS_LEMMA, pair_first_def, pair_second_def]);

val SS_STAR_ASSIGN_THM = store_thm("SS_STAR_ASSIGN_THM",
    ``!p p'.small_step^* p p' ==> !l.small_step^* (Assign l (pair_first p), pair_second p) (Assign l (pair_first p'), pair_second p')``,
    HO_MATCH_MP_TAC RTC_INDUCT
    THEN RW_TAC (srw_ss ()) []
    THEN Cases_on `p`
    THEN Cases_on `p'`
    THEN Cases_on `p''`
    THEN FULL_SIMP_TAC (srw_ss ()) [pair_first_def, pair_second_def]
    THEN RW_TAC (srw_ss ()) [Once RTC_CASES1]
    THEN METIS_TAC ss_rulel);

val SS_STAR_IF_THM = store_thm("SS_STAR_IF_THM",
``!p p'.small_step^* p p' ==> !e2 e3.small_step^* (If (pair_first p) e2 e3, pair_second p) (If (pair_first p') e2 e3, pair_second p')``,
    HO_MATCH_MP_TAC RTC_INDUCT
    THEN RW_TAC (srw_ss ()) []
    THEN Cases_on `p`
    THEN Cases_on `p'`
    THEN Cases_on `p''`
    THEN FULL_SIMP_TAC (srw_ss ()) [pair_first_def, pair_second_def]
    THEN RW_TAC (srw_ss ()) [Once RTC_CASES1]
    THEN METIS_TAC ss_rulel);

val SS_BS_STAR_IF_T_THM = store_thm("SS_BS_STAR_IF_THM",
    ``!e1 e2 e3 s s'.small_step^* (e1, s) (B T, s') ==> small_step^* (If e1 e2 e3, s) (e2, s')``,
    METIS_TAC ([pair_first_def, pair_second_def, SS_STAR_IF_THM, RTC_SUBSET, RTC_CASES_RTC_TWICE]@ss_rulel));

val SS_BS_STAR_IF_F_THM = store_thm("SS_BS_STAR_IF_THM",
    ``!e1 e2 e3 s s'.small_step^* (e1, s) (B F, s') ==> small_step^* (If e1 e2 e3, s) (e3, s')``,
    METIS_TAC ([pair_first_def, pair_second_def, SS_STAR_IF_THM, RTC_SUBSET, RTC_CASES_RTC_TWICE]@ss_rulel));

val SS_STAR_ASSIGN_CASE_THM = store_thm("SS_STAR_ASSIGN_CASE_THM",
    ``!e1 n s s' l.small_step^* (e1, s) (N n, s') ==> small_step^* (Assign l e1, s) (Assign l (N n), s')``,
    METIS_TAC [pair_first_def, pair_second_def, SS_STAR_ASSIGN_THM]);

val SS_BS_STAR_ASSIGN_THM = store_thm("SS_BS_STAR_ASSIGN_THM",
    ``!e1 n s s' l.l ∈ FDOM s /\ small_step^* (e1, s) (N n, s') ==> small_step^* (Assign l e1, s) (Skip, s' |+ (l, n))``,
    RW_TAC (srw_ss ()) []
    THEN `FDOM s = FDOM s'` by METIS_TAC [DOMAIN_CONSTANT_STAR_THM, pair_second_def]
    THEN METIS_TAC ([SS_STAR_ASSIGN_CASE_THM, RTC_CASES_RTC_TWICE, RTC_SUBSET]@ss_rulel));

val SS_STAR_GEQ_1_THM = store_thm("SS_STAR_GEQ_THM",
    ``!p p'.small_step^* p p' ==> !e2.small_step^* (Geq (pair_first p) e2, (pair_second p)) (Geq (pair_first p') e2, pair_second p')``,
    HO_MATCH_MP_TAC RTC_INDUCT
    THEN RW_TAC (srw_ss ()) []
    THEN Cases_on `p`
    THEN Cases_on `p'`
    THEN Cases_on `p''`
    THEN FULL_SIMP_TAC (srw_ss ()) [pair_first_def, pair_second_def]
    THEN RW_TAC (srw_ss ()) [Once RTC_CASES1]
    THEN METIS_TAC ss_rulel);

val SS_STAR_GEQ_2_THM = store_thm("SS_STAR_GEQ_THM",
    ``!p p'.small_step^* p p' ==> !n1.small_step^* (Geq (N n1) (pair_first p), (pair_second p)) (Geq (N n1) (pair_first p'), pair_second p')``,
    HO_MATCH_MP_TAC RTC_INDUCT
    THEN RW_TAC (srw_ss ()) []
    THEN Cases_on `p`
    THEN Cases_on `p'`
    THEN Cases_on `p''`
    THEN FULL_SIMP_TAC (srw_ss ()) [pair_first_def, pair_second_def]
    THEN RW_TAC (srw_ss ()) [Once RTC_CASES1]
    THEN METIS_TAC ss_rulel);


val SS_STAR_PLUS_1_THM = store_thm("SS_STAR_PLUS_THM",
    ``!p p'.small_step^* p p' ==> !e2.small_step^* (Plus (pair_first p) e2, (pair_second p)) (Plus (pair_first p') e2, pair_second p')``,
    HO_MATCH_MP_TAC RTC_INDUCT
    THEN RW_TAC (srw_ss ()) []
    THEN Cases_on `p`
    THEN Cases_on `p'`
    THEN Cases_on `p''`
    THEN FULL_SIMP_TAC (srw_ss ()) [pair_first_def, pair_second_def]
    THEN RW_TAC (srw_ss ()) [Once RTC_CASES1]
    THEN METIS_TAC ss_rulel);

val SS_STAR_PLUS_2_THM = store_thm("SS_STAR_PLUS_THM",
    ``!p p'.small_step^* p p' ==> !n1.small_step^* (Plus (N n1) (pair_first p), (pair_second p)) (Plus (N n1) (pair_first p'), pair_second p')``,
    HO_MATCH_MP_TAC RTC_INDUCT
    THEN RW_TAC (srw_ss ()) []
    THEN Cases_on `p`
    THEN Cases_on `p'`
    THEN Cases_on `p''`
    THEN FULL_SIMP_TAC (srw_ss ()) [pair_first_def, pair_second_def]
    THEN RW_TAC (srw_ss ()) [Once RTC_CASES1]
    THEN METIS_TAC ss_rulel);


val SS_STAR_PLUS_1_CASE_THM = store_thm("SS_STAR_PLUS_1_THM",
    ``!e1 e2 n1 s s'.small_step^* (e1, s) (N n1, s') ==> small_step^* (Plus e1 e2, s) (Plus (N n1) e2, s')``,
    METIS_TAC [SS_STAR_PLUS_1_THM, pair_first_def, pair_second_def]);

val SS_STAR_PLUS_2_CASE_THM = store_thm("SS_STAR_PLUS_2_THM",
    ``!e2 n1 n2 s s'.small_step^* (e2, s) (N n2, s') ==> small_step^* (Plus (N n1) e2, s) (Plus (N n1) (N n2), s')``,
    METIS_TAC [SS_STAR_PLUS_2_THM, pair_first_def, pair_second_def]);

val SS_BS_STAR_PLUS_THM = store_thm("SS_BS_STAR_PLUS_THM",
    ``!e1 e2 n1 n2 s s' s''.small_step^* (e1, s) (N n1, s') /\ small_step^* (e2, s') (N n2, s'') ==> small_step^* (Plus e1 e2, s) (N (n1 + n2), s'')``,
    METIS_TAC ([SS_STAR_PLUS_1_CASE_THM, SS_STAR_PLUS_2_CASE_THM, RTC_CASES_RTC_TWICE, RTC_SUBSET]@ss_rulel));

val SS_STAR_GEQ_1_CASE_THM = store_thm("SS_STAR_PLUS_1_THM",
    ``!e1 e2 n1 s s'.small_step^* (e1, s) (N n1, s') ==> small_step^* (Geq e1 e2, s) (Geq (N n1) e2, s')``,
    METIS_TAC [SS_STAR_GEQ_1_THM, pair_first_def, pair_second_def]);

val SS_STAR_GEQ_2_CASE_THM = store_thm("SS_STAR_PLUS_2_THM",
    ``!e2 n1 n2 s s'.small_step^* (e2, s) (N n2, s') ==> small_step^* (Geq (N n1) e2, s) (Geq (N n1) (N n2), s')``,
    METIS_TAC [SS_STAR_GEQ_2_THM, pair_first_def, pair_second_def]);

val SS_BS_STAR_GEQ_THM = store_thm("SS_BS_STAR_PLUS_THM",
    ``!e1 e2 n1 n2 s s' s''.small_step^* (e1, s) (N n1, s') /\ small_step^* (e2, s') (N n2, s'') ==> small_step^* (Geq e1 e2, s) (B (n1 >= n2), s'')``,
    METIS_TAC ([SS_STAR_GEQ_1_CASE_THM, SS_STAR_GEQ_2_CASE_THM, RTC_CASES_RTC_TWICE, RTC_SUBSET]@ss_rulel));

val SS_STAR_SEQ_THM = store_thm("SS_STAR_SEQ_THM",
    ``!p p'.small_step^* p p' ==> !e2.small_step^* (Seq (pair_first p) e2, (pair_second p)) (Seq (pair_first p') e2, pair_second p')``,
    HO_MATCH_MP_TAC RTC_INDUCT
    THEN RW_TAC (srw_ss ()) []
    THEN Cases_on `p`
    THEN Cases_on `p'`
    THEN Cases_on `p''`
    THEN FULL_SIMP_TAC (srw_ss ()) [pair_first_def, pair_second_def]
    THEN RW_TAC (srw_ss ()) [Once RTC_CASES1]
    THEN METIS_TAC ss_rulel);

val SS_STAR_SEQ_CASE_1_THM = store_thm("SS_STAR_PLUS_1_THM",
    ``!e1 e2 s s'.small_step^* (e1, s) (Skip, s') ==> small_step^* (Seq e1 e2, s) (Seq Skip e2, s')``,
    METIS_TAC [SS_STAR_SEQ_THM, pair_first_def, pair_second_def]);

val SS_STAR_SEQ_CASE_2_THM = store_thm("SS_BS_STAR_SEQ_CASE_THM",
    ``!e2 e2' s s'.small_step^* (e2, s) (e2', s') ==> small_step^* (Seq Skip e2, s) (e2', s')``,
    METIS_TAC ([SS_STAR_SEQ_THM, pair_first_def, pair_second_def, RTC_SUBSET, RTC_CASES_RTC_TWICE]@ss_rulel));

val SS_BS_STAR_SEQ_THM = store_thm("SS_BS_STAR_SEQ_THM",
    ``!e1 e2 e2' s s' s''.small_step^* (e1, s) (Skip, s') /\ small_step^* (e2, s') (e2', s'') ==> small_step^* (Seq e1 e2, s) (e2', s'')``,
    METIS_TAC [SS_STAR_SEQ_CASE_1_THM, SS_STAR_SEQ_CASE_2_THM, RTC_CASES_RTC_TWICE]);

val BS_IMP_SS_LEMMA = store_thm("BS_IMP_SS_LEMMA",
    ``!p v t.big_step p v t ==> small_step^* (bs_to_ss (pair_first p), pair_second p) (bs_to_ss (B_Value v), t)``,
    HO_MATCH_MP_TAC bs_sinduction
    THEN RW_TAC (srw_ss ()) [pair_first_def, pair_second_def]
    THEN FULL_SIMP_TAC (srw_ss ()) [bs_to_ss_def]
    THEN1 METIS_TAC [SS_BS_STAR_PLUS_THM]
    THEN1 METIS_TAC [SS_BS_STAR_GEQ_THM]
    THEN1 METIS_TAC (RTC_SUBSET::ss_rulel)
    THEN1 METIS_TAC [SS_BS_STAR_ASSIGN_THM]
    THEN1 METIS_TAC [SS_BS_STAR_SEQ_THM]
    THEN1 METIS_TAC [SS_BS_STAR_IF_T_THM, RTC_CASES_RTC_TWICE]
    THEN1 METIS_TAC [SS_BS_STAR_IF_F_THM, RTC_CASES_RTC_TWICE]
    THEN1 (
        `small_step (While (bs_to_ss e1) (bs_to_ss e2), s) (If (bs_to_ss e1) (Seq (bs_to_ss e2) (While (bs_to_ss e1) (bs_to_ss e2))) Skip, s)` by METIS_TAC ss_rulel
	THEN `small_step^* (If (bs_to_ss e1) (Seq (bs_to_ss e2) (While (bs_to_ss e1) (bs_to_ss e2))) Skip, s) (Seq (bs_to_ss e2) (While (bs_to_ss e1) (bs_to_ss e2)), t)` by METIS_TAC [SS_BS_STAR_IF_T_THM]
	THEN `small_step^* (Seq (bs_to_ss e2) (While (bs_to_ss e1) (bs_to_ss e2)), t) (Skip, t'')` by METIS_TAC [SS_BS_STAR_SEQ_THM]
       THEN METIS_TAC [RTC_SUBSET, RTC_CASES_RTC_TWICE])
    THEN1 (
        `small_step (While (bs_to_ss e1) (bs_to_ss e2), s) (If (bs_to_ss e1) (Seq (bs_to_ss e2) (While (bs_to_ss e1) (bs_to_ss e2))) Skip, s)` by METIS_TAC ss_rulel
        THEN `small_step^* (If (bs_to_ss e1) (Seq (bs_to_ss e2) (While (bs_to_ss e1) (bs_to_ss e2))) Skip, s) (Skip, t)` by METIS_TAC [SS_BS_STAR_IF_F_THM]
        THEN METIS_TAC [RTC_SUBSET, RTC_CASES_RTC_TWICE]));

val BS_IMP_SS_THM = store_thm("BS_IMP_SS_THM",
    ``!e s v t.big_step (e, s) v t ==> small_step^* (bs_to_ss e, s) (bs_to_ss (B_Value v), t)``,
    METIS_TAC [BS_IMP_SS_LEMMA, pair_first_def, pair_second_def]);

val SS_IMP_BS_FAKE_THM = store_thm("SS_IMP_BS_FAKE_THM",
    ``(!p p'.small_step p p' ==> !v t.(big_step (ss_bs p') v t ==> big_step (ss_bs p) v t)) ==> (!p p'.small_step^* p p' ==> value (pair_first p') ==> ?x.((ss_to_bs_value (pair_first p') = SOME x) /\ big_step (ss_to_bs (pair_first p), pair_second p) x (pair_second p')))``,
    STRIP_TAC
    THEN HO_MATCH_MP_TAC RTC_STRONG_INDUCT
    THEN RW_TAC (srw_ss ()) [pair_first_def, pair_second_def, ss_bs_def]

    THEN1 (Cases_on `pair_first p`
        THEN FULL_SIMP_TAC (srw_ss ()) [value_def]
	THEN EVAL_TAC
	THEN RW_TAC (srw_ss ()) [Once bs_ecases])

    THEN Cases_on `p`
    THEN Cases_on `p'`
    THEN Cases_on `p''`
    THEN FULL_SIMP_TAC (srw_ss ()) [pair_first_def, pair_second_def]
    THEN METIS_TAC [ss_bs_def, pair_first_def, pair_second_def]);
val _ = export_theory ();
