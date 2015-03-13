open HolKernel boolLib bossLib listTheory Parse IndDefLib finite_mapTheory relationTheory arithmeticTheory ast_il1Theory bigstep_il1Theory pred_setTheory pairTheory lcsymtacs prim_recTheory integerTheory store_equivalenceTheory l1_to_il1_compilerTheory l1_il1_totalTheory il1_backTheory il1_determinacyTheory comp_locationTheory bigstep_l1Theory bigstep_il1_clockedTheory optionTheory;

val _ = new_theory "l1_il1_correctness"

val WHILE_UNWIND_ONCE_THM = store_thm("WHILE_UNWIND_ONCE_THM",
``!e1 s e2 v s' c c'.bs_il1_expr (e1, s) (IL1_Boolean T) ==> (bs_il1_c (SUC c) (IL1_While e1 e2, s) (SOME (IL1_ESkip, s', c')) <=> bs_il1_c c (IL1_Seq e2 (IL1_While e1 e2), s) (SOME (IL1_ESkip, s', c')))``,
rw [EQ_IMP_THM] THEN1
(imp_res_tac IL1_WHILE_BACK_THM THEN rw []
THEN1 (imp_res_tac BS_IL1_EXPR_DETERMINACY THEN rw [])
THEN1 (rw [Once bs_il1_c_cases] THEN
Cases_on `c` THEN1 (fs [Once bs_il1_c_cases])
THEN metis_tac []))
THEN1 (rw [Once bs_il1_c_cases] THEN imp_res_tac IL1_SEQ_BACK_THM THEN metis_tac [IL1_SEQ_BACK_THM]));

val l1_il1_val_def = Define `(l1_il1_val (L1_Int n) = IL1_Integer n) /\
(l1_il1_val (L1_Bool b) = IL1_Boolean b) /\
(l1_il1_val (L1_Skip) = IL1_ESkip)`;

val il1_l1_val_def = Define `(il1_l1_val (IL1_Integer n) = L1_Int n) /\
(il1_l1_val (IL1_Boolean b) = L1_Bool b) /\
(il1_l1_val IL1_ESkip = L1_Skip)`;

val BS_VALUE_THM = store_thm("BS_VALUE_THM",
``!v v' s.bs_il1_expr (IL1_Value v, s) v' ==> (v = v') /\ !s'.bs_il1_expr (IL1_Value v, s') v'``,
Cases_on `v` THEN REPEAT (rw [Once bs_il1_expr_cases]));

val MAP_FDOM_AFTER_INSERT = store_thm("MAP_FDOM_AFTER_INSERT",
``!f a b.a ∈ FDOM (f |+ (a, b))``,
rw [FDOM_DEF]);

val ASSIGN_ENSURES_IN_DOM_THM = store_thm("ASSIGN_ENSURES_IN_DOM_THM",
``!l c c' e s s'.bs_il1_c c (IL1_Assign l e, s) (SOME (IL1_ESkip, s', c')) ==> l ∈ FDOM s'``,
rw [Once bs_il1_c_cases] THEN rw [FDOM_DEF]);

val DOMS_SUBSET_THM_1 = prove(
``!c p r.bs_il1_c c p r ==> !x.(r = SOME x) ==> FDOM (SND p) ⊆ FDOM (FST (SND x))``,
ho_match_mp_tac bs_il1_c_strongind THEN rw [FST, SND, SUBSET_DEF]);

val DOMS_SUBSET_THM = store_thm("DOMS_SUBSET_THM",
``!e s v s' c c'.bs_il1_c c (e, s) (SOME (v, s', c')) ==> FDOM s ⊆ FDOM s'``,
metis_tac [FST, SND, DOMS_SUBSET_THM_1]);

val NO_INTERMEDIATE_WRITES_SAME_VALUE = store_thm("NO_INTERMEDIATE_WRITES_SAME_VALUE",
``!p v.bs_il1_expr p v ==> !c c' s' s'' l.l ∈ FDOM s'' ==> bs_il1_c c (IL1_Assign l (FST p), (SND p)) (SOME (IL1_ESkip, s', c')) ==> ((s' ' l) = (s'' ' l)) ==> bs_il1_expr (IL1_Deref l, s'') v``,
Cases_on `p` THEN rw [FST, SND]
THEN fs [Once bs_il1_c_cases]
THEN rw [Once bs_il1_expr_cases]
THEN metis_tac [BS_IL1_EXPR_DETERMINACY, FAPPLY_FUPDATE]);

val SKIP_TO_SKIP_THM = store_thm("SKIP_TO_SKIP",
``!s.bs_il1_expr (IL1_Value IL1_ESkip, s) IL1_ESkip``,
rw [Once bs_il1_expr_cases] THEN metis_tac []);

val SKIP_TO_SKIP_2_THM = store_thm("SKIP_TO_SKIP_2_THM",
``!c s.bs_il1_c (SUC c) (IL1_Expr (IL1_Value IL1_ESkip), s) (SOME (IL1_ESkip, s, (SUC c)))``,
rw [Once bs_il1_c_cases, Once bs_il1_expr_cases] THEN metis_tac []);

val ASSIGN_IMPLIES_SKIP_THM = store_thm("ASSIGN_IMPLIES_SKIP_THM",
``!e lc s st ex l lc'.(l1_to_il1_pair lc (L1_Assign l e) = (st, ex, lc')) ==> (ex = IL1_Value (IL1_ESkip))``,
rw [l1_to_il1_pair_def]
THEN `?sl1 e1' lc2'.l1_to_il1_pair lc e = (sl1, e1', lc2')` by metis_tac [L1_TO_IL1_TOTAL_THM] 
THEN fs [LET_DEF]);

val CONTAINS_CONVERT_THM = store_thm("CONTAINS_CONVERT_THM",
``!e n l.contains l (l1_to_il1 e n) <=> ?st ex n'.(l1_to_il1_pair n e = (st, ex, n')) /\ (contains l st \/ contains_expr l ex)``,
rw [EQ_IMP_THM] THEN1 (`?st ex n'.l1_to_il1_pair n e = (st, ex, n')` by metis_tac [L1_TO_IL1_TOTAL_THM] THEN fs [l1_to_il1_def, LET_DEF, contains_def]) THEN rw [l1_to_il1_def, LET_DEF, contains_def]);

val L1_USELESS_LOC_EXPR_THM = prove(
``!p r.bs_il1_expr p r ==> !k.~contains_expr k (FST p) ==> !v.bs_il1_expr (FST p, SND p |+ (k, v)) r``,
HO_MATCH_MP_TAC bs_il1_expr_strongind THEN rw []
THEN1 (Cases_on `r` THEN fs [Once bs_il1_expr_cases]) THEN TRY (
rw [Once bs_il1_expr_cases]
THEN fs [contains_expr_def] THEN metis_tac [])
THEN fs [contains_expr_def]
THEN rw [Once bs_il1_expr_cases, NOT_EQ_FAPPLY]);

val USELESS_LOC_EXPR_THM = store_thm("USELESS_LOC_EXPR_THM",
``!e s r.bs_il1_expr (e, s) r ==> !k.~contains_expr k e ==> !v.bs_il1_expr (e, s |+ (k, v)) r``,
METIS_TAC [L1_USELESS_LOC_EXPR_THM, FST, SND]);


val L1_USELESS_LOC_THM = prove(
``!c p r.bs_il1_c c p r ==> !x.(r = SOME x) ==> !k.~contains k (FST p) ==> !v.bs_il1_c c (FST p, SND p |+ (k, v)) (SOME (FST x, FST (SND x) |+ (k, v), SND (SND x)))``,
HO_MATCH_MP_TAC bs_il1_c_strongind THEN rw []
THEN1 (fs [Once bs_il1_c_cases, contains_def] THEN METIS_TAC [USELESS_LOC_EXPR_THM])
THEN rw [Once bs_il1_c_cases] THEN fs [contains_def, FUPDATE_COMMUTES] THEN METIS_TAC [USELESS_LOC_EXPR_THM]);

val USELESS_LOC_THM = store_thm("USELESS_LOC_THM",
``!e s r s' c c'.bs_il1_c c (e, s) (SOME (r, s', c')) ==> !k.~contains k e ==> !v.bs_il1_c c (e, s |+ (k, v)) (SOME (r, s' |+ (k, v), c'))``,
METIS_TAC [FST, SND, L1_USELESS_LOC_THM]);

val IL1_SEQ_ASSOC_THM = store_thm("IL1_SEQ_ASSOC_THM",
``!e1 e2 e3 s v s' c c'.bs_il1_c c (IL1_Seq e1 (IL1_Seq e2 e3), s) (SOME (v, s', c')) <=> bs_il1_c c (IL1_Seq (IL1_Seq e1 e2) e3, s) (SOME (v, s', c'))``,
rw [EQ_IMP_THM]
THEN1 (fs [Once bs_il1_c_cases] THEN rw [Once bs_il1_c_cases] THEN metis_tac [IL1_SEQ_BACK_THM])
THEN rw [Once bs_il1_c_cases] THEN (NTAC 2 (imp_res_tac IL1_SEQ_BACK_THM THEN imp_res_tac IL1_SEQ_BACK_THM THEN imp_res_tac IL1_SEQ_BACK_THM THEN imp_res_tac IL1_DETERMINACY_THM THEN rw [])) THEN Cases_on `c` THEN1 fs [Once bs_il1_c_cases] THEN rw [] THEN Q.LIST_EXISTS_TAC [`cl''`, `s'''`] THEN rw [] THEN rw [Once bs_il1_c_cases]
THEN Cases_on `cl''` THEN1 fs [Once bs_il1_c_cases] THEN metis_tac []);

val EXPR_PURE_THM = store_thm("EXPR_DOES_NOTHING_THM",
``!st es s s' v c c'.bs_il1_c c (IL1_Seq st (IL1_Expr es), s) (SOME (v, s', c')) ==> bs_il1_c c (st, s) (SOME (IL1_ESkip, s', c'))``,
rw [] THEN
`bs_il1_c c (st, s) (SOME (IL1_ESkip, s', c')) /\ bs_il1_c c' (IL1_Expr es, s') (SOME (v, s', c'))` by ALL_TAC THEN
IMP_RES_TAC IL1_SEQ_BACK_THM THEN imp_res_tac IL1_DETERMINACY_THM THEN rw [] THEN
`(s'' = s') /\ (c' = cl')` by fs [Once bs_il1_c_cases] THEN
metis_tac []);

val EXPR_PURE_2_THM = store_thm("EXPR_PURE_2_THM",
``!e s v s' c c'.bs_il1_c c (IL1_Expr e, s) (SOME (v, s', c')) ==> (s = s') /\ (c = c')``,
rw [Once bs_il1_c_cases]);

val plus_case = (* Begin plus case *)
(fs [l1_to_il1_pair_def, l1_il1_val_def]

THEN `?st1 ex1 lc1''.l1_to_il1_pair lc1 e1 = (st1, ex1, lc1'')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st2 ex2 lc2''.l1_to_il1_pair lc1'' e2 = (st2, ex2, lc2'')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN fs [LET_DEF] THEN rw []

THEN rw [Once bs_il1_cases]
THEN rw [Once bs_il1_cases]


THEN `?fs'.bs_il1 (st1, fs) IL1_ESkip fs' /\ bs_il1_expr (ex1, fs') (IL1_Integer n1) /\ equiv (con_store s') fs'` by metis_tac []
THEN `bs_il1 (IL1_Assign (Compiler lc2'') ex1, fs') IL1_ESkip (fs' |+ (Compiler lc2'', n1))` by (rw [Once bs_il1_cases] THEN metis_tac [])

THEN `equiv fs' (fs' |+ (Compiler lc2'', n1))` by (rw [equiv_def] THEN `Compiler lc2'' <> User k` by rw [] THEN metis_tac [FAPPLY_FUPDATE_THM])
THEN `equiv (con_store s') (fs' |+ (Compiler lc2'', n1))` by metis_tac [EQUIV_TRANS_THM]


THEN `?fs''.bs_il1 (st2, fs' |+ (Compiler lc2'', n1)) IL1_ESkip fs'' /\ bs_il1_expr (ex2, fs'') (IL1_Integer n2) /\ equiv (con_store s'') fs''` by metis_tac []

THEN `(fs' |+ (Compiler lc2'',n1)) ' (Compiler lc2'') = fs'' ' (Compiler lc2'')` by (`~contains_a (Compiler lc2'') st2` by (CCONTR_TAC THEN fs[] THEN imp_res_tac UNCHANGED_LOC_SIMP_THM THEN decide_tac) THEN metis_tac [NOT_CONTAINS_MEANS_UNCHANGED_THM])

THEN `bs_il1_expr (IL1_Deref (Compiler lc2''), fs'') (IL1_Integer n1)` by (rw [Once bs_il1_expr_cases] THEN metis_tac [SUBSET_DEF, FAPPLY_FUPDATE, MAP_FDOM_AFTER_INSERT, DOMS_SUBSET_THM])

THEN rw [Once bs_il1_expr_cases]
THEN metis_tac []);
(* End plus case *)

val total = metis_tac [L1_TO_IL1_TOTAL_THM];

val L1_TO_IL1_CORRECTNESS_LEMMA = store_thm("L1_TO_IL1_CORRECTNESS_LEMMA",
``!p v s'.bs_l1 p v s' ==> !lc1 st ex lc1'.((st, ex, lc1') = l1_to_il1_pair lc1 (FST p)) ==> !fs.equiv (con_store (SND p)) fs ==> ?fs'.bs_il1 (st, fs) IL1_ESkip fs' /\ bs_il1_expr (ex, fs') (l1_il1_val v) /\ equiv (con_store s') fs'``,
ho_match_mp_tac bs_l1_strongind THEN rw [FST, SND]

(* Begin unit case *)

THEN1 (Cases_on `v` THEN rw [l1_il1_val_def] THEN fs [l1_to_il1_pair_def] THEN rw []
THEN rw [Once bs_il1_cases, Once bs_il1_expr_cases] THEN rw [Once bs_il1_cases, Once bs_il1_expr_cases])

(* End unit cases *)

THEN1 plus_case
THEN1 plus_case

(* Dereference case *)
THEN1 (fs [l1_to_il1_pair_def, l1_il1_val_def] THEN rw [Once bs_il1_cases]

THEN1 metis_tac [SKIP_TO_SKIP_THM]
THEN fs [Once bs_il1_expr_cases, equiv_def, con_store_def, MAP_KEYS_def, STORE_L1_IL1_INJ])
(* End dereference case *)

(* Begin assign case *)
THEN1 (fs [l1_to_il1_pair_def, l1_il1_val_def] THEN rw []
THEN `?st1 ex1 lc1''.l1_to_il1_pair lc1 e = (st1, ex1, lc1'')` by total
THEN fs [LET_DEF] THEN rw []

THEN rw [Once bs_il1_expr_cases]
THEN `?fs'.bs_il1 (st1,fs) IL1_ESkip fs' /\ bs_il1_expr (ex1, fs') (IL1_Integer n) /\ equiv (con_store s') fs'` by metis_tac []

THEN `bs_il1 (IL1_Assign (User l) ex1, fs') IL1_ESkip (fs' |+ (User l, n))` by (rw [Once bs_il1_cases] THEN
`User l ∈ FDOM (con_store s)` by rw [FDOM_DEF, con_store_def, MAP_KEYS_def] THEN
`User l ∈ FDOM fs` by metis_tac [equiv_def] THEN
metis_tac [SUBSET_DEF, DOMS_SUBSET_THM])

THEN rw [con_store_def]

THEN `equiv (MAP_KEYS User (s' |+ (l, n))) (fs' |+ (User l, n))` by (fs [con_store_def] THEN `equiv (MAP_KEYS User s' |+ (User l, n)) (fs' |+ (User l, n))` by metis_tac [EQUIV_APPEND_THM] THEN metis_tac [con_store_def, MAP_APPEND_EQUIV_THM, EQUIV_APPEND_THM])
THEN rw [Once bs_il1_cases]
THEN metis_tac [con_store_def])
(* End assign case *)

THEN fs [l1_to_il1_pair_def, l1_il1_val_def]
THEN `?st1 ex1 lc1''.l1_to_il1_pair lc1 e1 = (st1, ex1, lc1'')` by total
THEN `?st2 ex2 lc2''.l1_to_il1_pair lc1'' e2 = (st2, ex2, lc2'')` by total
THEN `?st3 ex3 lc3''.l1_to_il1_pair lc2'' e3 = (st3, ex3, lc3'')` by total
THEN res_tac
THEN fs [LET_DEF] THEN rw []

(* Begin seq case *)
THEN1 (rw [Once bs_il1_cases]
THEN rw [Once bs_il1_cases]

THEN imp_res_tac EQ_SYM

THEN res_tac

THEN `bs_il1 (IL1_Expr ex1, fs'') (IL1_ESkip) fs''` by (rw [Once bs_il1_cases])
THEN metis_tac [])
(* End seq case *)

(* Start if true case *)

THEN1 (
rw [Once bs_il1_cases]
THEN rw [Once bs_il1_cases]


THEN `?fs'.bs_il1 (st1, fs) IL1_ESkip fs' /\ bs_il1_expr (ex1, fs') (IL1_Boolean T) /\ equiv (con_store s') fs'` by metis_tac []


THEN   `bs_il1
          (IL1_Assign (Compiler lc3'')
             (IL1_EIf ex1 (IL1_Value (IL1_Integer 1))
                (IL1_Value (IL1_Integer 0))),fs') IL1_ESkip (fs' |+ (Compiler lc3'', 1))` by (rw [Once bs_il1_cases]
THEN rw [Once bs_il1_expr_cases]
THEN rw [Once bs_il1_expr_cases]
THEN metis_tac [])

THEN `equiv fs' (fs' |+ (Compiler lc3'', 1))` by (rw [equiv_def] THEN `Compiler lc3'' <> User k` by rw [] THEN metis_tac [FAPPLY_FUPDATE_THM])
THEN `equiv (con_store s') (fs' |+ (Compiler lc3'', 1))` by metis_tac [EQUIV_TRANS_THM]

THEN `?fs''.bs_il1 (st2, fs' |+ (Compiler lc3'', 1)) IL1_ESkip fs'' /\ bs_il1_expr (ex2, fs'') (l1_il1_val v) /\ equiv (con_store s'') fs''` by metis_tac []


THEN `bs_il1 (IL1_SIf ex1 st2 st3, fs' |+ (Compiler lc3'', 1)) IL1_ESkip fs''` by (rw [Once bs_il1_cases]


THEN `~contains (Compiler lc3'') (l1_to_il1 e1 lc1)` by (CCONTR_TAC THEN fs [] THEN imp_res_tac ALL_CO_LOCS_IN_RANGE THEN imp_res_tac COMP_LOC_INCREASING_THM THEN decide_tac)

THEN fs [contains_def, l1_to_il1_def] THEN rw []
THEN `~contains (Compiler lc3'') (let (s, te, lc) = (st1, ex1, lc1'') in IL1_Seq s (IL1_Expr te))` by metis_tac []
THEN fs [LET_DEF] THEN rw []
THEN fs [contains_def]
THEN metis_tac [USELESS_LOC_EXPR_THM])

(*    *)
THEN `bs_il1_expr
    (IL1_EIf
       (IL1_Geq (IL1_Deref (Compiler lc3''))
          (IL1_Value (IL1_Integer 1))) ex2 ex3,fs'') (l1_il1_val v) ∧
  equiv (con_store s'') fs''` by (
rw [Once bs_il1_expr_cases]
THEN rw [Once bs_il1_expr_cases]

THEN `bs_il1_expr (IL1_Deref (Compiler lc3''), fs'') (IL1_Integer 1)` by (

`(fs' |+ (Compiler lc3'', 1)) ' (Compiler lc3'') = fs'' ' (Compiler lc3'')` by (`~contains_a  (Compiler lc3'') st2` by (CCONTR_TAC THEN fs [] THEN imp_res_tac UNCHANGED_LOC_SIMP_THM THEN imp_res_tac COMP_LOC_INCREASING_THM THEN decide_tac) THEN metis_tac [NOT_CONTAINS_MEANS_UNCHANGED_THM])

THEN rw [Once bs_il1_expr_cases] THEN metis_tac [SUBSET_DEF, FAPPLY_FUPDATE, MAP_FDOM_AFTER_INSERT, DOMS_SUBSET_THM]




THEN metis_tac [])
THEN `bs_il1_expr (IL1_Value (IL1_Integer 1), fs'') (IL1_Integer 1)` by (rw [Once bs_il1_expr_cases] THEN metis_tac [])
THEN `1 >= 1` by metis_tac [int_ge, INT_LE_REFL]

THEN metis_tac [])

THEN metis_tac [])

(* End if true case *)

(* Start if false case *)

THEN1 (rw [Once bs_il1_cases]
THEN rw [Once bs_il1_cases]


THEN `?fs'.bs_il1 (st1, fs) IL1_ESkip fs' /\ bs_il1_expr (ex1, fs') (IL1_Boolean F) /\ equiv (con_store s') fs'` by metis_tac []


THEN   `bs_il1
          (IL1_Assign (Compiler lc3'')
             (IL1_EIf ex1 (IL1_Value (IL1_Integer 1))
                (IL1_Value (IL1_Integer 0))),fs') IL1_ESkip (fs' |+ (Compiler lc3'', 0))` by (rw [Once bs_il1_cases]
THEN rw [Once bs_il1_expr_cases]
THEN `bs_il1_expr (IL1_Value (IL1_Integer 0), fs') (IL1_Integer 0)` by (rw [Once bs_il1_expr_cases] THEN metis_tac [])
THEN metis_tac [])

THEN `equiv fs' (fs' |+ (Compiler lc3'', 0))` by (rw [equiv_def] THEN `Compiler lc3'' <> User k` by rw [] THEN metis_tac [FAPPLY_FUPDATE_THM])
THEN `equiv (con_store s') (fs' |+ (Compiler lc3'', 0))` by metis_tac [EQUIV_TRANS_THM]

THEN `?fs''.bs_il1 (st3, fs' |+ (Compiler lc3'', 0)) IL1_ESkip fs'' /\ bs_il1_expr (ex3, fs'') (l1_il1_val v) /\ equiv (con_store s'') fs''` by metis_tac []


THEN `bs_il1 (IL1_SIf ex1 st2 st3, fs' |+ (Compiler lc3'', 0)) IL1_ESkip fs''` by (rw [Once bs_il1_cases]


THEN `~contains (Compiler lc3'') (l1_to_il1 e1 lc1)` by (CCONTR_TAC THEN fs [] THEN imp_res_tac ALL_CO_LOCS_IN_RANGE THEN imp_res_tac COMP_LOC_INCREASING_THM THEN decide_tac)

THEN fs [contains_def, l1_to_il1_def] THEN rw []
THEN `~contains (Compiler lc3'') (let (s, te, lc) = (st1, ex1, lc1'') in IL1_Seq s (IL1_Expr te))` by metis_tac []
THEN fs [LET_DEF] THEN rw []
THEN fs [contains_def]
THEN metis_tac [USELESS_LOC_EXPR_THM])

(*    *)
THEN `bs_il1_expr
    (IL1_EIf
       (IL1_Geq (IL1_Deref (Compiler lc3''))
          (IL1_Value (IL1_Integer 1))) ex2 ex3,fs'') (l1_il1_val v) ∧
  equiv (con_store s'') fs''` by (
rw [Once bs_il1_expr_cases]
THEN rw [Once bs_il1_expr_cases]

THEN `bs_il1_expr (IL1_Deref (Compiler lc3''), fs'') (IL1_Integer 0)` by  (

`(fs' |+ (Compiler lc3'', 0)) ' (Compiler lc3'') = fs'' ' (Compiler lc3'')` by (`~contains_a  (Compiler lc3'') st3` by (CCONTR_TAC THEN fs [] THEN imp_res_tac UNCHANGED_LOC_SIMP_THM THEN imp_res_tac COMP_LOC_INCREASING_THM THEN decide_tac) THEN metis_tac [NOT_CONTAINS_MEANS_UNCHANGED_THM])

THEN rw [Once bs_il1_expr_cases] THEN metis_tac [SUBSET_DEF, FAPPLY_FUPDATE, MAP_FDOM_AFTER_INSERT, DOMS_SUBSET_THM])

THEN `bs_il1_expr
  (IL1_Geq (IL1_Deref (Compiler lc3'')) (IL1_Value (IL1_Integer 1)),
   fs'') (IL1_Boolean F)` by (
rw [Once bs_il1_expr_cases]
THEN `bs_il1_expr (IL1_Value (IL1_Integer 1), fs'') (IL1_Integer 1)` by (rw [Once bs_il1_expr_cases] THEN metis_tac [])
THEN `~(0 >= 1)` by metis_tac [int_ge, INT_NOT_LE, INT_LT_REFL, INT_LT_01, INT_LT_ANTISYM]


THEN metis_tac [])
THEN rw [Once bs_il1_expr_cases])
THEN metis_tac [])

(* end if false case *)

(* Begin while true case *)
THEN1 (

`?fs'.bs_il1 (st1,fs) IL1_ESkip fs' /\ bs_il1_expr (ex1, fs') (IL1_Boolean T) /\ equiv (con_store s') fs'` by metis_tac []
THEN `?fs''.bs_il1 (st2,fs') IL1_ESkip fs'' /\ bs_il1_expr (ex2, fs'') IL1_ESkip /\ equiv (con_store s'') fs''` by metis_tac []
THEN rw []
THEN res_tac

THEN fs [l1_il1_val_def]

THEN `bs_il1 (IL1_Seq st2 (IL1_Seq st1 (IL1_While ex1 (IL1_Seq st2 (IL1_Seq (IL1_Expr ex2) st1)))), fs') IL1_ESkip fs'''` by (rw [Once bs_il1_cases] THEN metis_tac [])
THEN `bs_il1 (IL1_Seq (IL1_Seq st2 st1) (IL1_While ex1 (IL1_Seq st2 (IL1_Seq (IL1_Expr ex2) st1))), fs') IL1_ESkip fs'''` by metis_tac [IL1_SEQ_ASSOC_THM]
THEN `bs_il1 (IL1_While ex1 (IL1_Seq st2 (IL1_Seq (IL1_Expr ex2) st1)), fs') IL1_ESkip fs'''` by (

rw [Once WHILE_UNWIND_ONCE_THM]
THEN rw [GSYM IL1_SEQ_ASSOC_THM]
THEN rw [Once bs_il1_cases]

THEN ` bs_il1 (st2,fs') IL1_ESkip fs'' ∧
  bs_il1
    (IL1_Seq (IL1_Seq (IL1_Expr ex2) st1)
       (IL1_While ex1 (IL1_Seq st2 (IL1_Seq (IL1_Expr ex2) st1))),fs'')
    IL1_ESkip fs'''` by (

rw []

THEN rw [Once bs_il1_cases]
THEN rw [Once bs_il1_cases]
THEN rw [Once bs_il1_cases]

THEN fs[Q.SPEC`(IL1_Seq X Y, s)`bs_il1_cases] 

THEN metis_tac [])

THEN metis_tac [])

THEN rw [Once bs_il1_cases]
THEN metis_tac [])
(*End while true case *)

(* Begin while false case *)
THEN1 (rw [Once bs_il1_cases]

THEN`?fs'.bs_il1 (st1, fs) IL1_ESkip fs' /\ bs_il1_expr (ex1, fs') (IL1_Boolean F) /\ equiv (con_store s') fs'` by metis_tac []

THEN fs [l1_il1_val_def]

THEN `bs_il1 (IL1_While ex1 (IL1_Seq st2 (IL1_Seq (IL1_Expr ex2) st1)), fs') IL1_ESkip fs'` by (rw [Once bs_il1_cases] THEN metis_tac [])
THEN rw [Once bs_il1_expr_cases] THEN metis_tac [])
(* End while false case *));

val L1_TO_IL1_EXISTS_CORRECTNESS_THM = store_thm("L1_TO_IL1_EXISTS_CORRECTNESS_THM",
``!e s v s' s''.bs_l1 (e, s) v s' ==> ?s''.bs_il1 (l1_to_il1 e 0, con_store s) (l1_il1_val v) s'' /\ equiv (con_store s') s''``,
rw [l1_to_il1_def]
THEN `?s''' te lc.l1_to_il1_pair 0 e = (s''', te, lc)` by total
THEN rw []
THEN `equiv (con_store s) (con_store s)` by metis_tac [EQUIV_REFL_THM]
THEN rw [Once bs_il1_cases]
THEN imp_res_tac EQ_SYM
THEN imp_res_tac L1_TO_IL1_CORRECTNESS_LEMMA
THEN fs [FST, SND]
THEN res_tac
THEN `bs_il1 (IL1_Expr te, fs') (l1_il1_val v) fs'` by (rw [Once bs_il1_cases] THEN metis_tac [])
THEN metis_tac []);

val L1_TO_IL1_FORALL_CORRECTNESS_THM = store_thm("L1_TO_IL1_FORALL_CORRECTNESS_THM",
``!e s v s' s''.bs_l1 (e, s) v s' ==> !s'' v'.bs_il1 (l1_to_il1 e 0, con_store s) v' s'' ==> equiv (con_store s') s'' /\ (l1_il1_val v = v')``,
rw [l1_to_il1_def] THEN `?s te lc.l1_to_il1_pair 0 e = (s,te, lc)` by total THEN fs [LET_DEF] THEN fs [Once bs_il1_cases] THEN imp_res_tac IL1_EXPR_BACK_THM
THEN rw [] THEN imp_res_tac L1_TO_IL1_CORRECTNESS_LEMMA THEN fs [FST, SND] THEN `equiv (con_store s) (con_store s)` by metis_tac [EQUIV_REFL_THM] THEN imp_res_tac EQ_SYM THEN res_tac THEN imp_res_tac IL1_DETERMINACY_THM THEN rw [] THEN metis_tac [BS_IL1_EXPR_DETERMINACY]);

val STORE_DOMAIN_INVERSE_THM = store_thm("STORE_DOMAIN_INVERSE_THM",
``!l s.User l ∈ FDOM (con_store s) ==> l ∈ FDOM s``,
rw [con_store_def, FDOM_DEF, MAP_KEYS_def]);

val _ = export_theory ();
