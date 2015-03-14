open HolKernel boolLib bossLib listTheory Parse IndDefLib finite_mapTheory relationTheory arithmeticTheory ast_l1Theory bigstep_l1Theory pred_setTheory pairTheory lcsymtacs integerTheory ast_il1Theory bigstep_il1Theory il1_backTheory bigstep_il1_clockedTheory;

val _ = new_theory "il1_determinacy";


fun mapspecs specs thm = map (fn x => Q.SPECL x thm) specs;

fun repeat n x = if n = 0 then [] else x::(repeat (n-1) x);

fun prepall xs ys = map (fn y => xs @ y) ys;

fun listify xs = map (fn x => [x]) xs;

val specs = [`(IL1_Expr A, B)`, `(IL1_Seq A B, C)`, `(IL1_SIf A B C, D)`, `(IL1_Assign A B, C)`];

fun prthen (a, b) = (a THEN b);

fun collapse_cases n rtype cthm = NTAC 2 (foldr prthen all_tac (map rtype (listify (mapspecs (prepall (repeat n `X`) (listify specs)) cthm))) THEN rw [] THEN fs []);


val BS_IL1_EXPR_DETERMINACY = store_thm("BS_IL1_EXPR_DETERMINACY",
``!p v1.bs_il1_expr p v1 ==> !v2.bs_il1_expr p v2 ==> (v1 = v2)``,
ho_match_mp_tac bs_il1_expr_strongind THEN rw []
THEN1 (Cases_on `v1` THEN Cases_on `v2` THEN fs [Once bs_il1_expr_cases])
THEN1 (imp_res_tac BS_IL1_EXPR_PLUS_BACK_THM THEN res_tac THEN rw [])
THEN1 (imp_res_tac BS_IL1_EXPR_GEQ_BACK_THM THEN res_tac THEN rw [])
THEN1 (imp_res_tac BS_IL1_EXPR_DEREF_BACK_THM THEN rw [])
THEN1 (imp_res_tac BS_IL1_EXPR_EIF_BACK_THM THEN res_tac THEN rw [])
THEN1 (imp_res_tac BS_IL1_EXPR_EIF_BACK_THM THEN res_tac THEN rw []));

val t1 = collapse_cases 1 fs bs_il1_c_cases THEN (NTAC 5 (res_tac THEN fs [] THEN rw [])) THEN (TRY (`IL1_Boolean T = IL1_Boolean F` by metis_tac [BS_IL1_EXPR_DETERMINACY] THEN fs []));

val t2 = fs [Once bs_il1_c_cases] THEN imp_res_tac BS_IL1_EXPR_DETERMINACY THEN rw [] THEN metis_tac [BS_IL1_EXPR_DETERMINACY];

val t3 = fs [Once (Q.SPECL [`SUC A`] bs_il1_c_cases)]
THEN (NTAC 2 (res_tac THEN fs [] THEN  (TRY (`IL1_Boolean T = IL1_Boolean F` by metis_tac [BS_IL1_EXPR_DETERMINACY] THEN fs [])) THEN rw []));

val IL1_DETERMINACY_THM = store_thm("IL1_DETERMINACY_THM",
``!c p r.bs_il1_c c p r ==> !r'.bs_il1_c c p r' ==> (r = r')``,
ho_match_mp_tac bs_il1_c_strongind THEN rw []
THENL [t2, t2, t2, t1, t1, t1, t1, t1, t1, t1, t3, t3, t3, t3, t2]);

val _ = export_theory ();
