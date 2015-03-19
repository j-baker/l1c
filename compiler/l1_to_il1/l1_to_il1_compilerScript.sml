open HolKernel boolLib bossLib listTheory Parse IndDefLib finite_mapTheory relationTheory arithmeticTheory ast_l1Theory ast_il1Theory bigstep_l1Theory bigstep_il1Theory pred_setTheory pairTheory lcsymtacs prim_recTheory integerTheory;

val _ = new_theory "l1_to_il1_compiler";

val l1_to_il1_pair_def = Define `
    (l1_to_il1_pair lc (L1_Value (L1_Int n)) = (IL1_Expr (IL1_Value IL1_ESkip), IL1_Value (IL1_Integer n), lc)) /\
    (l1_to_il1_pair lc (L1_Value (L1_Bool b)) = (IL1_Expr (IL1_Value IL1_ESkip), IL1_Value (IL1_Boolean b), lc)) /\
    (l1_to_il1_pair lc (L1_Value L1_Skip) = (IL1_Expr (IL1_Value IL1_ESkip), IL1_Value IL1_ESkip, lc)) /\
    (l1_to_il1_pair lc (L1_Deref l) = (IL1_Expr (IL1_Value IL1_ESkip), IL1_Deref (User l), lc)) /\

    (l1_to_il1_pair lc (L1_Assign l e) =
        let (sl, e', lc2) = l1_to_il1_pair lc e
        in
            (IL1_Seq sl (IL1_Assign (User l) e'), IL1_Value IL1_ESkip,lc2)) /\

    (l1_to_il1_pair lc (L1_Seq e1 e2) =
        let (sl1, e1', lc2) = l1_to_il1_pair lc e1 in
        let (sl2, e2', lc3) = l1_to_il1_pair lc2 e2
        in (IL1_Seq (IL1_Seq sl1 (IL1_Expr e1')) sl2, e2', lc3)) /\

    (l1_to_il1_pair lc (L1_While e1 e2) =
        let (sl1, e1', lc2) = l1_to_il1_pair lc e1 in
        let (sl2, e2', lc3) = l1_to_il1_pair lc2 e2
        in
            (IL1_Seq sl1 (IL1_While e1' (IL1_Seq (IL1_Tick sl2) (IL1_Seq (IL1_Expr e2') sl1))), IL1_Value IL1_ESkip, lc3)) /\

    (l1_to_il1_pair lc (L1_If e1 e2 e3) =
        let (sl1, e1', lc2) = l1_to_il1_pair lc e1 in 
        let (sl2, e2', lc3) = l1_to_il1_pair lc2 e2 in
        let (sl3, e3', lc4) = l1_to_il1_pair lc3 e3
        in
            (IL1_Seq
                (IL1_Seq sl1
                    (IL1_Assign (Compiler lc4) (IL1_EIf e1' (IL1_Value (IL1_Integer 1)) (IL1_Value (IL1_Integer 0)))))
                (IL1_SIf e1' sl2 sl3),
             IL1_EIf (IL1_Geq (IL1_Deref (Compiler lc4)) (IL1_Value (IL1_Integer 1))) e2' e3',
             lc4 + 1)) /\

    (l1_to_il1_pair lc (L1_Plus e1 e2) =
        let (sl1, e1', lc2) = l1_to_il1_pair lc e1 in
        let (sl2, e2', lc3) = l1_to_il1_pair lc2 e2
        in
            (IL1_Seq (IL1_Seq sl1 (IL1_Assign (Compiler lc3) e1')) sl2, IL1_Plus (IL1_Deref (Compiler lc3)) e2', lc3 + 1)) /\ 

    (l1_to_il1_pair lc (L1_Geq e1 e2) =
        let (sl1, e1', lc2) = l1_to_il1_pair lc e1 in
        let (sl2, e2', lc3) = l1_to_il1_pair lc2 e2
        in
            (IL1_Seq (IL1_Seq sl1 (IL1_Assign (Compiler lc3) e1')) sl2, IL1_Geq (IL1_Deref (Compiler lc3)) e2', lc3 + 1))
`;

val l1_to_il1_def = Define `l1_to_il1 e n = let (s, te, lc) = l1_to_il1_pair n e in IL1_Seq s (IL1_Expr te)`;

val _ = export_theory ();
