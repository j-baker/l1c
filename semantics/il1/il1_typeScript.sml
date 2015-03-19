open HolKernel boolLib bossLib listTheory Parse IndDefLib finite_mapTheory relationTheory arithmeticTheory ast_l1Theory bigstep_l1Theory pred_setTheory pairTheory lcsymtacs integerTheory ast_il1Theory;

val _ = new_theory "il1_type";

val (il1_expr_type_rules, il1_expr_type_ind, il1_expr_type_cases) = Hol_reln `
        (!g.il1_expr_type (IL1_Value IL1_ESkip) g unitL1) /\
        (!g n.il1_expr_type (IL1_Value (IL1_Integer n)) g intL1) /\
        (!g b.il1_expr_type (IL1_Value (IL1_Boolean b)) g boolL1) /\

        (!e1 e2 g.
           (il1_expr_type e1 g intL1 /\
            il1_expr_type e2 g intL1)
        ==> il1_expr_type (IL1_Plus e1 e2) g intL1) /\

        (!e1 e2 g.
           (il1_expr_type e1 g intL1 /\
            il1_expr_type e2 g intL1)
        ==> il1_expr_type (IL1_Geq e1 e2) g boolL1) /\

        (!g l.l ∈ g ==>
            il1_expr_type (IL1_Deref l) g intL1) /\

        (!e1 e2 e3 g t.
           (il1_expr_type e1 g boolL1 /\
            il1_expr_type e2 g t /\
            il1_expr_type e3 g t)
        ==> il1_expr_type (IL1_EIf e1 e2 e3) g t)`;

val (il1_type_rules, il1_type_ind, il1_type_cases) = Hol_reln `
(!e g t.il1_expr_type e g t ==> il1_type (IL1_Expr e) g t g) /\
(!e l g.il1_expr_type e g intL1 ==> il1_type (IL1_Assign l e) g unitL1 (l INSERT g)) /\

(!e1 e2 g g' g'' t.
       (il1_type e1 g unitL1 g' /\
        il1_type e2 g' t g'')
    ==> il1_type (IL1_Seq e1 e2) g t g'') /\

(!e1 e2 e3 g g' g'' t.
       (il1_expr_type e1 g boolL1 /\
        il1_type e2 g t g' /\
        il1_type e3 g t g'')
    ==> il1_type (IL1_SIf e1 e2 e3) g t (g' ∪ g'')) /\

(!e1 e2 g g'.
       (il1_expr_type e1 g boolL1 /\
        il1_type e2 g unitL1 g')
    ==> il1_type (IL1_While e1 e2) g unitL1 g') /\

(!e t g g'.
        il1_type e g t g' ==> il1_type (IL1_Tick e) g t g')
`;

val _ = export_theory ();
