open HolKernel boolLib bossLib listTheory Parse IndDefLib finite_mapTheory relationTheory arithmeticTheory ast_il1Theory bigstep_il1Theory pred_setTheory pairTheory lcsymtacs prim_recTheory integerTheory;

val _ = new_theory "store_equivalence";

val contains_expr_def = Define `
    (contains_expr l (IL1_Value v) = F) /\
    (contains_expr l (IL1_Plus e1 e2) = contains_expr l e1 \/ contains_expr l e2) /\
    (contains_expr l (IL1_Geq e1 e2) = contains_expr l e1 \/ contains_expr l e2) /\
    (contains_expr l1 (IL1_Deref l2) = (l1 = l2)) /\
    (contains_expr l (IL1_EIf e1 e2 e3) = contains_expr l e1 \/ contains_expr l e2 \/ contains_expr l e3)`;

val contains_def = Define `
    (contains l (IL1_Expr e) = contains_expr l e) /\
    (contains l1 (IL1_Assign l2 e) = (l1 = l2) \/ contains_expr l1 e) /\
    (contains l (IL1_Seq e1 e2) = contains l e1 \/ contains l e2) /\
    (contains l (IL1_SIf e1 e2 e3) = contains_expr l e1 \/ contains l e2 \/ contains l e3) /\
    (contains l (IL1_While e1 e2) = contains_expr l e1 \/ contains l e2)`;

val contains_a_def = Define `
    (contains_a l (IL1_Expr _) = F) /\
    (contains_a l1 (IL1_Assign l2 e) = (l1 = l2)) /\
    (contains_a l (IL1_Seq e1 e2) = contains_a l e1 \/ contains_a l e2) /\
    (contains_a l (IL1_SIf _ e2 e3) = contains_a l e2 \/ contains_a l e3) /\
    (contains_a l (IL1_While _ e2) = contains_a l e2)`;

val CONTAINS_A_SUB = store_thm("CONTAINS_A_SUB",
``!l e.contains_a l e ==> contains l e``,
Induct_on `e` THEN metis_tac [contains_a_def, contains_def]);

val equiv_def = Define `equiv s1 s2 = !k.(User k ∈ FDOM s1 <=> User k ∈ FDOM s2) /\ (s1 ' (User k) = s2 ' (User k))`;

val EQUIV_REFL_THM = store_thm("EQUIV_REFL_THM",
``!x.equiv x x``,
fs [equiv_def]);

val EQUIV_TRANS_THM = store_thm("EQUIV_TRANS_THM",
``!x y z.equiv x y /\ equiv y z ==> equiv x z``,
rw [equiv_def]);

val EQUIV_APPEND_THM = store_thm("EQUIV_APPEND_THM",
``!e1 e2 k v.equiv e1 e2 ==> equiv (e1 |+ (k, v)) (e2 |+ (k, v))``,
rw [equiv_def] THEN metis_tac [FST, FUPDATE_SAME_APPLY]);

val MAP_APPEND_EQUIV_THM = store_thm("MAP_APPEND_EQUIV_THM",
``!s k v.(MAP_KEYS User s) |+ (User k, v) = (MAP_KEYS User (s |+ (k, v)))``,
rw [] THEN `INJ User (k INSERT FDOM s) UNIV` by rw [INJ_DEF]
THEN metis_tac [MAP_KEYS_FUPDATE])

val EQUIV_SYM_THM = store_thm("EQUIV_SYM_THM",
``!s s'.equiv s s' <=> equiv s' s``,
metis_tac [equiv_def]);

val STORE_L1_IL1_INJ = store_thm("STORE_L1_IL1_INJ",
``!l s. l ∈ FDOM s ==> ((s ' l) = (MAP_KEYS User s) ' (User l))``,
rw [] THEN `FDOM (MAP_KEYS User s) = IMAGE User (FDOM s)` by rw [FDOM_DEF, MAP_KEYS_def, IMAGE_DEF]
THEN `INJ User (FDOM s) UNIV` by rw [INJ_DEF] THEN metis_tac [MAP_KEYS_def]);

val con_store_def = Define `con_store s = MAP_KEYS User s`;

val NOT_CONTAINS_MEANS_UNCHANGED_LEMMA = prove(
``!p v s'.bs_il1 p v s' ==> !l.~contains_a l (FST p) ==> (((SND p) ' l) = (s' ' l))``,
ho_match_mp_tac bs_il1_strongind THEN rw [FST, SND] THEN fs [contains_a_def] THEN metis_tac [FAPPLY_FUPDATE_THM]);

val NOT_CONTAINS_MEANS_UNCHANGED_THM = store_thm("NOT_CONTAINS_MEANS_UNCHANGED_THM",
``!e s v s'.bs_il1 (e, s) v s' ==> !l.~contains_a l e ==> (s ' l = s' ' l)``,
metis_tac [NOT_CONTAINS_MEANS_UNCHANGED_LEMMA, FST, SND]);


val _ = export_theory ();
