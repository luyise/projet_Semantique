
(* The type of tokens. *)

type token = 
  | TOK_int of (string)
  | TOK_id of (string)
  | TOK_WHILE
  | TOK_VOID
  | TOK_TRUE
  | TOK_STAR_EQUAL
  | TOK_STAR
  | TOK_SEMICOLON
  | TOK_RPAREN
  | TOK_RETURN
  | TOK_RCURLY
  | TOK_RAND
  | TOK_PLUS_PLUS
  | TOK_PLUS_EQUAL
  | TOK_PLUS
  | TOK_PERCENT_EQUAL
  | TOK_PERCENT
  | TOK_NOT_EQUAL
  | TOK_MINUS_MINUS
  | TOK_MINUS_EQUAL
  | TOK_MINUS
  | TOK_LPAREN
  | TOK_LESS_EQUAL
  | TOK_LESS
  | TOK_LCURLY
  | TOK_INT
  | TOK_IF
  | TOK_GREATER_EQUAL
  | TOK_GREATER
  | TOK_GOTO
  | TOK_FOR
  | TOK_FALSE
  | TOK_EXCLAIM
  | TOK_EQUAL_EQUAL
  | TOK_EQUAL
  | TOK_EOF
  | TOK_ELSE
  | TOK_DIVIDE_EQUAL
  | TOK_DIVIDE
  | TOK_COMMA
  | TOK_COLON
  | TOK_BREAK
  | TOK_BRAND
  | TOK_BAR_BAR
  | TOK_ASSERT
  | TOK_AND_AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val file: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Abstract_syntax_tree.toplevel list Abstract_syntax_tree.ext)

module MenhirInterpreter : sig
  
  (* The incremental API. *)
  
  include MenhirLib.IncrementalEngine.INCREMENTAL_ENGINE
    with type token = token
  
end

(* The entry point(s) to the incremental API. *)

module Incremental : sig
  
  val file: Lexing.position -> (Abstract_syntax_tree.toplevel list Abstract_syntax_tree.ext) MenhirInterpreter.checkpoint
  
end
