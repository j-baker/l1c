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


val small_step_def = Define `
(* Plus *)
(small_step (Plus (N n1) (N n2), s) = (N (n1 + n2), s)) /\
(small_step (Plus (N n1) e2, s) = (let (e2', s') = small_step (e2, s) in (Plus (N n1) e2', s'))) /\
(small_step (Plus e1 e2, s) = (let (e1', s') = small_step (e1, s) in (Plus e1' e2, s'))) /\
(* Geq *)
(small_step (Geq (N n1) (N n2), s) = (B (n1 >= n2), s)) /\
(small_step (Geq (N n1) e2, s) = (let (e2', s') = small_step (e2, s) in (Geq (N n1) e2', s'))) /\
(small_step (Geq e1 e2, s) = (let (e1', s') = small_step (e1, s) in (Geq e1' e2, s'))) /\
(* Deref (Todo improve) *)
(small_step (Deref(l), s) = (N (s ' l), s)) /\
(* Assign (Todo improve) *)
(small_step (Assign l (N n), s) = (Skip, s |+ (l, n))) /\
(small_step (Assign l e, s) = (let (e', s') = small_step (e, s) in (Assign l e', s'))) /\
(* Seq *)
(small_step (Seq Skip e2, s) = (e2, s)) /\
(small_step (Seq e1 e2, s) = (let (e1', s') = small_step (e1, s) in (Seq e1' e2, s'))) /\
(* If *)
(small_step (If (B T) e2 e3, s) = (e2, s)) /\
(small_step (If (B F) e2 e3, s) = (e3, s)) /\
(small_step (If e1 e2 e3, s) = (let (e1', s') = small_step (e1, s) in (If e1' e2 e3, s'))) /\
(* While *)
(small_step (While e1 e2, s) = (If e1 (Seq e2 (While e1 e2)) Skip, s))`;

(* Determinacy *)
val DETERMINACY_THM = store_thm("DETERMINACY_THM",
``!e s e1 s1 e2 s2.((small_step (e, s) = (e1, s1)) /\ (small_step (e, s) = (e2, s2))) ==> ((e1, s1) = (e2, s2))``,
REPEAT STRIP_TAC THEN
Induct_on `e` THENL[
FULL_SIMP_TAC std_ss [small_step_def],
FULL_SIMP_TAC std_ss [small_step_def],
FULL_SIMP_TAC std_ss [small_step_def],
FULL_SIMP_TAC std_ss [small_step_def],
FULL_SIMP_TAC std_ss [small_step_def],
FULL_SIMP_TAC std_ss [small_step_def],
FULL_SIMP_TAC std_ss [small_step_def],
FULL_SIMP_TAC std_ss [small_step_def],
FULL_SIMP_TAC std_ss [small_step_def],
FULL_SIMP_TAC std_ss [small_step_def]]);

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

val _ = export_theory ();
