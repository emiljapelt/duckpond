%{
  open Absyn
  (*open Lexing*)

  module StringSet = Set.Make(String)
  module StringMap = Map.Make(String)

%}
%token <int> CSTINT
%token <string> NAME
%token <string> TYPE_NAME
%token <string> CSTSTRING
%token TRUE FALSE
%token LPAR RPAR LBRAKE RBRAKE LBRACE RBRACE
%token PLUS MINUS TIMES EQ NEQ LT GT LTEQ GTEQ CONS CARAT AND OR FSLASH
%token PIPE
%token COMMA DOT COLON EOF
%token WHEN IS LET REC IN IF THEN ELSE WITH
%token UNDERSCORE
%token R_ARROW LAMBDA
%token INT BOOL STRING UNIT TYPE OF

/*Low precedence*/
%nonassoc IN ELSE
%left R_ARROW
%right CONS 
%left CARAT
%left EQ NEQ GT LT GTEQ LTEQ 
%left AND OR
%left PLUS MINUS
%left TIMES FSLASH
/*High precedence*/

%start main
%type <(Absyn.term)> main
%%
main:
  term EOF     { $1 }
;

typ:
  | simple_typ { $1 }
  | typ TIMES typ { T_Tuple($1,$3) } 
  | simple_typ R_ARROW typ { T_Func($1,$3) }
  | seperated(PIPE, simple_typ) { T_Alts $1 }
  | TYPE_NAME COLON typ { T_NameBind($1,$3)}
  | simple_typ PLUS simple_typ { T_Addition($1,$3)}
;

object_type_item:
  | NAME COLON typ { ($1,$3) }
;

simple_typ:
  | INT { T_Int }
  | BOOL { T_Bool }
  | STRING { T_String }
  | NAME { T_Alias $1 }
  | TYPE_NAME { T_Name $1 }
  | UNIT { T_Unit }
  | LPAR typ RPAR { $2 }
  | LBRACE seperated(COMMA, object_type_item) RBRACE { T_Object (StringMap.of_list $2) }
;

%public seperated(S,C):
  {[]}
  | C  {[$1]}
  | C S seperated(S,C) {$1::$3}
;


term:
  | TYPE NAME EQ typ IN term { TypeAlias($2,$4,$6) }
  | term binop term { App(App(Name $2, $1), $3) }
  | simple_term { $1 }
  | app { $1 }
  | let_term { $1 }
  | IF term THEN term ELSE term { WhenIs($2, [
    ((None, P_Bool true), $4);
    ((None, P_Bool false), $6);
  ]) }
  | LAMBDA NAME COLON simple_typ R_ARROW term { Func($2,Some $4,$6) }
  | LAMBDA NAME R_ARROW term { Func($2,None,$4) }
  | simple_term WITH LBRACE object_item* RBRACE { With($1, StringMap.of_list $4)}
;

object_item:
  | NAME COLON typ EQ term { ($1, (Some $3,$5)) }
  | NAME EQ term { ($1, (None,$3)) }
;

app:
  simple_term simple_term { App($1,$2) }
  | app simple_term { App($1,$2) }
;

let_term:
  | LET NAME COLON typ EQ term IN term { Bind(false, $2, Some $4, $6, $8) }
  | LET NAME EQ term IN term { Bind(false, $2, None, $4, $6) }
  | LET REC NAME COLON typ EQ term IN term { Bind(true, $3, Some $5, $7, $9) }
  | LET REC NAME EQ term IN term { Bind(true, $3, None, $5, $7) }
;

term_with_match:
  WHEN term IS alt+ { WhenIs($2,$4) }
  | WHEN term IS pattern R_ARROW term { WhenIs($2, [(None, $4),$6]) }
  | term { $1 }
;

simple_term:
  | NAME { Name $1 }
  | simple_term DOT NAME { Access($1,$3) }
  | TRUE { Bool true }
  | FALSE { Bool false }
  | LPAR RPAR { Unit }
  | CSTINT { Int $1 }
  | CSTSTRING { String $1 }
  | LPAR term_with_match COMMA term_with_match RPAR { Tuple($2,$4) }
  | LPAR term_with_match RPAR { $2 }
  | LBRACE seperated(COMMA, object_item) RBRACE { Object (StringMap.of_list $2) }
;

%inline binop:
  | PLUS    { ("+") }
  | MINUS   { ("-") }
  | TIMES   { ("*") } 
  | FSLASH  { ("/") }
  | EQ      { ("=") }
  | NEQ     { ("!=") }
  | LT      { ("<") }
  | GT      { (">") }
  | LTEQ    { ("<=") }
  | GTEQ    { (">=") }
  | CARAT   { ("^") }
  | AND     { ("&&") }
  | OR      { ("||") }
;

alt:
  | PIPE NAME COLON pattern R_ARROW term { ((Some $2, $4), $6) }
  | PIPE pattern R_ARROW term { ((None, $2), $4) }
;

pattern:
  | simple_pattern { $1 }
;

simple_pattern:
  | UNDERSCORE { P_Any }
  | simple_typ { P_Type $1 }
  | CSTINT { P_Int $1 }
  | TRUE { P_Bool true }
  | FALSE { P_Bool false }
  | CSTSTRING { P_String $1 }
  | LPAR pattern COMMA pattern RPAR { P_Tuple($2,$4) }
  | LPAR pattern RPAR { $2 }
;
