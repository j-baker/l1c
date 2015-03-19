structure Tokens = Tokens

type pos = int

type svalue = Tokens.svalue
type ('a, 'b) token = ('a, 'b) Tokens.token
type lexresult = (svalue, pos) token

val pos = ref 0

val error = fn x => print (x ^ "\n")
val eof = fn () => Tokens.EOF(!pos, !pos)

exception ThisCannotHappen;


val reserved_words = ["while", "do", "skip", "if", "then", "else", "true", "false"]

fun contains x [] = false
  | contains x (y::ys) = x = y orelse contains x ys

%%
%header (functor L1LexFun(structure Tokens : L1_Parse_TOKENS));
%reject
%%
[\ \t\n]+ => (pos := !pos+1;lex());
"+"   => (Tokens.PLUS(!pos, !pos));
">="  => (Tokens.GTEQ(!pos, !pos));
"("   => (Tokens.LPAREN(!pos, !pos));
")"   => (Tokens.RPAREN(!pos, !pos));
"true" => (Tokens.TRUE(!pos, !pos));
"false" => (Tokens.FALSE(!pos, !pos));
"if" => (Tokens.IF(!pos, !pos));
"then" => (Tokens.THEN(!pos, !pos));
"else" => (Tokens.ELSE(!pos, !pos));
":=" => (Tokens.ASSIGN(!pos, !pos));
"!" => (Tokens.DEREF(!pos, !pos));
"skip" => (Tokens.SKIP(!pos, !pos));
";" => (Tokens.SEQ(!pos, !pos));
"while" => (Tokens.WHILE(!pos, !pos));
"do" => (Tokens.DO(!pos, !pos));
[- ~]? [0-9]+ => (Tokens.INT(case Int.fromString(yytext) of SOME x => x | NONE => raise ThisCannotHappen, !pos, !pos));
[A-Za-z] ( [A-Za-z0-9_] ) * => (if contains yytext reserved_words then REJECT () else Tokens.IDENT(yytext, !pos, !pos));
. => (error ("ignoring bad character "^yytext); lex());
