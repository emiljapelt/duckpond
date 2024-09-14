{
  open Parser
  let keyword_table = Hashtbl.create 53
  let () = List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
                      [
                        "let", LET;
                        "in", IN;
                        "if", IF;
                        "then", THEN;
                        "else", ELSE;
                        "when", WHEN;
                        "is", IS;
                        "with", WITH;
                        "int", INT;
                        "bool", BOOL;
                        "string", STRING;
                        "type", TYPE;
                        "true", TRUE;
                        "false", FALSE;
                        "unit", UNIT;
                        "rec", REC;
                      ]

  let incr_linenum lexbuf = 
    let pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <- { pos with
      Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
      Lexing.pos_bol = pos.Lexing.pos_cnum;
    }
}

rule lex = parse
        [' ' '\t']               { lex lexbuf }
    |   ('\r''\n' | '\n')        { incr_linenum lexbuf ; lex lexbuf }
    |   "//" [^ '\n' '\r']* ('\r''\n' | '\n' | eof)       { incr_linenum lexbuf ; lex lexbuf }
    |   '-'?['0'-'9']+ as lxm { CSTINT (int_of_string lxm) }
    |   '"' [^ '"' '\n' '\r']* '"' as str { CSTSTRING (String.sub str 1 ((String.length str)-2)) }
    |   ['a'-'z'] ['A'-'Z' 'a'-'z' '0'-'9' '_'] * '''* as id
                { try
                    Hashtbl.find keyword_table id
                  with Not_found -> NAME id }
    |   ['A'-'Z'] ['A'-'Z' 'a'-'z' '0'-'9' '_'] * as id
                    { try
                        Hashtbl.find keyword_table id
                      with Not_found -> TYPE_NAME id }
    |   '+'           { PLUS }
    |   '-'           { MINUS }
    |   '*'           { TIMES }
    |   '/'           { FSLASH }
    |   '='           { EQ }
    |   "!="          { NEQ }
    |   '<'           { LT }
    |   '>'           { GT }
    |   "<="          { LTEQ }
    |   ">="          { GTEQ }
    |   '^'           { CARAT }
    |   "&&"          { AND }
    |   "||"          { OR }
    |   '('           { LPAR }
    |   ')'           { RPAR }
    |   '['           { LBRAKE }
    |   ']'           { RBRAKE }
    |   '{'           { LBRACE }
    |   '}'           { RBRACE }
    |   ','           { COMMA }
    |   '.'           { DOT }
    |   '|'           { PIPE }
    |   '\\'          { LAMBDA }
    |   "::"          { CONS }
    |   ':'           { COLON }
    |   "->"          { R_ARROW }
    |   '_'           { UNDERSCORE }
    |   eof           { EOF }
    |   _             { failwith ("Unknown token on line " ^ (string_of_int ((Lexing.lexeme_start_p lexbuf).pos_lnum))) }

and start filename = parse
       "" { lex lexbuf }
