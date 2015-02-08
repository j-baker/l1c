datatype lexresult= LPAREN | RPAREN | TRUE | FALSE | PLUS | GTEQT
                     IF | THEN | ELSE | ASSIGN | DEREF | SKIP | SEQ | WHILE
                     DO | IDENT of string | INTEGER of int | EOF

val linenum = ref 1
val error = fn x => output(std_out,x ^ "\n")
val eof = fn () => EOF
%%
%structure L1Lex
alpha=[A-Za-z];
digit=[0-9];
ws=[` ` `\t` `\n` `\r` ];
%%
{ws} => (lex());
"(" => (LPAREN);
")" => (RPAREN);
"true" => (TRUE);
"false" => (FALSE);
"+" => (PLUS);
">=" => (GTEQT);
"if" => (IF);
"then" => (THEN);
"else" => (ELSE);
":=" => (ASSIGN);
"!" => (DEREF);
"skip" => (SKIP);
";" => (SEQ);
"while" => (WHILE);
"do" => (DO);
[`-``~`]? [`0`-`9`]+ => (INTEGER( case Int.fromString(getLexeme lexbuf) of SOME x => x | NONE => raise Fail "ThisCannotHappen"));
[`A`-`Z` `a`-`z`] ( [`A`-`Z` `a`-`z` `0`-`9` `'` `_`] ) * => (IDENT(getLexeme lexbuf));
. => (error ("l1: ignoring bad character "^yytext); lex());
