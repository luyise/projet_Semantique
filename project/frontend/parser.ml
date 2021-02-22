
(* This generated code requires the following version of MenhirLib: *)

let () =
  MenhirLib.StaticVersion.require_20201216

module MenhirBasics = struct
  
  exception Error
  
  type token = 
    | TOK_int of (
# 67 "frontend/parser.mly"
       (string)
# 16 "frontend/parser.ml"
  )
    | TOK_id of (
# 66 "frontend/parser.mly"
       (string)
# 21 "frontend/parser.ml"
  )
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
  
end

include MenhirBasics

let _eRR =
  MenhirBasics.Error

# 14 "frontend/parser.mly"
  
open Abstract_syntax_tree

# 79 "frontend/parser.ml"

module Tables = struct
  
  include MenhirBasics
  
  let token2terminal : token -> int =
    fun _tok ->
      match _tok with
      | TOK_AND_AND ->
          46
      | TOK_ASSERT ->
          45
      | TOK_BAR_BAR ->
          44
      | TOK_BRAND ->
          43
      | TOK_BREAK ->
          42
      | TOK_COLON ->
          41
      | TOK_COMMA ->
          40
      | TOK_DIVIDE ->
          39
      | TOK_DIVIDE_EQUAL ->
          38
      | TOK_ELSE ->
          37
      | TOK_EOF ->
          36
      | TOK_EQUAL ->
          35
      | TOK_EQUAL_EQUAL ->
          34
      | TOK_EXCLAIM ->
          33
      | TOK_FALSE ->
          32
      | TOK_FOR ->
          31
      | TOK_GOTO ->
          30
      | TOK_GREATER ->
          29
      | TOK_GREATER_EQUAL ->
          28
      | TOK_IF ->
          27
      | TOK_INT ->
          26
      | TOK_LCURLY ->
          25
      | TOK_LESS ->
          24
      | TOK_LESS_EQUAL ->
          23
      | TOK_LPAREN ->
          22
      | TOK_MINUS ->
          21
      | TOK_MINUS_EQUAL ->
          20
      | TOK_MINUS_MINUS ->
          19
      | TOK_NOT_EQUAL ->
          18
      | TOK_PERCENT ->
          17
      | TOK_PERCENT_EQUAL ->
          16
      | TOK_PLUS ->
          15
      | TOK_PLUS_EQUAL ->
          14
      | TOK_PLUS_PLUS ->
          13
      | TOK_RAND ->
          12
      | TOK_RCURLY ->
          11
      | TOK_RETURN ->
          10
      | TOK_RPAREN ->
          9
      | TOK_SEMICOLON ->
          8
      | TOK_STAR ->
          7
      | TOK_STAR_EQUAL ->
          6
      | TOK_TRUE ->
          5
      | TOK_VOID ->
          4
      | TOK_WHILE ->
          3
      | TOK_id _ ->
          2
      | TOK_int _ ->
          1
  
  and error_terminal =
    0
  
  and token2value : token -> Obj.t =
    fun _tok ->
      match _tok with
      | TOK_AND_AND ->
          Obj.repr ()
      | TOK_ASSERT ->
          Obj.repr ()
      | TOK_BAR_BAR ->
          Obj.repr ()
      | TOK_BRAND ->
          Obj.repr ()
      | TOK_BREAK ->
          Obj.repr ()
      | TOK_COLON ->
          Obj.repr ()
      | TOK_COMMA ->
          Obj.repr ()
      | TOK_DIVIDE ->
          Obj.repr ()
      | TOK_DIVIDE_EQUAL ->
          Obj.repr ()
      | TOK_ELSE ->
          Obj.repr ()
      | TOK_EOF ->
          Obj.repr ()
      | TOK_EQUAL ->
          Obj.repr ()
      | TOK_EQUAL_EQUAL ->
          Obj.repr ()
      | TOK_EXCLAIM ->
          Obj.repr ()
      | TOK_FALSE ->
          Obj.repr ()
      | TOK_FOR ->
          Obj.repr ()
      | TOK_GOTO ->
          Obj.repr ()
      | TOK_GREATER ->
          Obj.repr ()
      | TOK_GREATER_EQUAL ->
          Obj.repr ()
      | TOK_IF ->
          Obj.repr ()
      | TOK_INT ->
          Obj.repr ()
      | TOK_LCURLY ->
          Obj.repr ()
      | TOK_LESS ->
          Obj.repr ()
      | TOK_LESS_EQUAL ->
          Obj.repr ()
      | TOK_LPAREN ->
          Obj.repr ()
      | TOK_MINUS ->
          Obj.repr ()
      | TOK_MINUS_EQUAL ->
          Obj.repr ()
      | TOK_MINUS_MINUS ->
          Obj.repr ()
      | TOK_NOT_EQUAL ->
          Obj.repr ()
      | TOK_PERCENT ->
          Obj.repr ()
      | TOK_PERCENT_EQUAL ->
          Obj.repr ()
      | TOK_PLUS ->
          Obj.repr ()
      | TOK_PLUS_EQUAL ->
          Obj.repr ()
      | TOK_PLUS_PLUS ->
          Obj.repr ()
      | TOK_RAND ->
          Obj.repr ()
      | TOK_RCURLY ->
          Obj.repr ()
      | TOK_RETURN ->
          Obj.repr ()
      | TOK_RPAREN ->
          Obj.repr ()
      | TOK_SEMICOLON ->
          Obj.repr ()
      | TOK_STAR ->
          Obj.repr ()
      | TOK_STAR_EQUAL ->
          Obj.repr ()
      | TOK_TRUE ->
          Obj.repr ()
      | TOK_VOID ->
          Obj.repr ()
      | TOK_WHILE ->
          Obj.repr ()
      | TOK_id _v ->
          Obj.repr _v
      | TOK_int _v ->
          Obj.repr _v
  
  and default_reduction =
    (8, "\000\000\000\000[\000D?\000\000L\000\000\000\000\000(\000\000\000\000M\000N\000O\000\000\0001\000\000\000\000\000,'\000\000\000.\000-\000\000\000\000;3\0002\000\000H\000\b\000\000\000\000\t\000\000\000\000\000\030\000\000\000\000\027\000\000\012\000\r\000\023\000\000\000\000\000\000\000\000\000\000\000\000\000\014\000\000\011\000\000\000\015\000\000 \000\000\031\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000!\000\000\0009\n\000\000\000\000\000\000\000\029\000\000\000\000\028\025\000\000\000\000=\000\\\000\000JXT\000\000\024\000\000F\000\000\000VRQWS\000\000\000\000\000\000\000\000\000\000P\0005\000\026\000$Y\000\000\000\000\000\000\000#\0007Z\000\"\001")
  
  and error =
    (47, "\b\000\000 \b\000@\000\000\000\000\000\000\000\b\000\000\000\002\000\001\000\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000@\000\000\000\128\000\000\000@\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\004\000\000\006\022\000\014`\004\128\129\166\128\004\1440\004\131\000\000\000\000\000\000\000\000\000\003\130\207\024C\021\129$\024\000\000\000\000\000\016\000\000\004\000\016@\000\000\000\000\000\000\000\000\016\000\000\000\000\000\000\000\000\000\000\000@\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\002\000\b \000\000\000\004\000\000\000\000\000\000\000\000\000\000\024\002A\128\000\0000\004\131\000\000\000`\t\006\000\000\000\002\130\136\000\002\001\128$\024\000\000\000\000\000\000\000\000\000\000\000\000\000\000\012\001 \192\000\000\000pYc\bb\176\004\131\000\000\000\000\000\000\000\000\000\192\018\012\000\000\000\000\000\000\000\000\003\000H0\000\000\000\028\022X\194\024\1608,\177\1321@pYc\bb\128\000\000\000\000\000\000\000\000\000\000\000\000\128\000\000\000\000\000\000\000\000\000\000\n\n \000\012\006\000\144`\000\000\000\000\000\000\000\000\000pQ\000\000`\000\000\000\000\000\000`\t\006\000\000\000\003\130\136\000\003\001\128$\024\000\000\000\014\n \000\012\000\000\000\000\000\000\012\001 \192\000\000\000pQ\000\000`0$\131\000\000\000\000@\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\003\000H0\000\000\000\028\020@\000\024\012\001 \192\000\000\000pQ\000\000`\000\000\000\000\000\000\000\000\002\000\000\000\200\018\012\001\128 \000\000\000\000\000\003 H0\006\000\128\000\000\000\000\000\012\129 \192\024\002\000\000\000\000\000\000\000\128\178\198\016\128`\t\006\000\000\000\003\130\136\000\002\021\128$\024\000\000\000\014\n \000\bV\000\144`\000\000\0008(\128\000!X\002A\128\000\000\000\224\162\000\000\133`\t\006\000\000\000\003\130\136\000\002\021\128$\024\000\000\000\014\n \000\bP\000\000\000\000\000\000(,\177\132 \000\016\000\000\000\002\128\000\000\000\000\000d\t\006\000\192\016\001\128\000\000\000\021\144$\024\003\000@\000\000\000\000\000\000\004\000\000\000\000\166\020\000\014`\004\128\000\000\000\000\0000D\131\000\000\000\000\128\000\000\000\000\000\000\000\000\000\000\006\005\016\000\004\001\133\128\003\152\001 \000\000 \000\000\012\129 \192\024\002\000\016\000\000\000\002\152P\0009\128\018\000\000\002\000\000\000\200\018\012\001\128 \001\000\000\000\000)\133\000\003\152\001 \000\000 \000\000\012\129 \192\024\002\000\016\000\000\000\002\152P\0009\128\018 \000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\016\000\000\002\b\000\000\000\000\000@\211\000\002@\000\000\000\000\000\000\000\000\000\000\000\000\000\128\000\000\000\000\201\018\012\001\128 \002\000\000\000\000\001\002\000\000\000\000\000\004\000\000\000\000\006\020\000\014`\004\128 \000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\200\018\012\001\128 \001\000\000\000\000(\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\b \000\000\000\000\000@\000\000\b@`\t\006\000\000\000\003\002\136\000\003\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\016\000\000\000\016\b\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\194\192\001\204\016\144\004\000\000\000\000\000\000\000\000\000\000\000\024\000\000\000\016\b\000\000\000\000\000\000\000\000\000\000\000\000\128\000\000\000\n\000\000\000\000\b\000\194\128\001\204\000\144\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\004\000a@\000\230\000H\000\000\b\000\000\001\004\000\000\000\000\000\b\000\000\000\000\012\145 \192\024\002\000 \000\000\000\000\016 \000\000\000\000\000@\000\000\000\000a@\000\230\000H\000\000\000\000\000\001\133\128\003\152\001 \000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\004\000\016\000\132\000\004\000\002\000\000\000\b\000\000\000\000\000\000\000\016\000\000\024X\0009\128\018\000\016\000\000\000\000\000\000\000\000\000\000 \000\000\128 \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000")
  
  and start =
    1
  
  and action =
    ((16, "\000*\000\014\000\016\000\r\000\000\000:\000\000\000\000\000\005\000\r\000\000\000P\0006\001j\002\018\001J\000\000\000\015\001J\000L\000\006\000\000\000~\000\000\000\142\000\000\000F\000\006\000\136\000\000\001J\001J\001J\001\158\001J\000\000\000\000\001J\0006\001J\000\000\001J\000\000\001J\000z\000\190\001\002\000\000\000\000\000\158\000\000\003~\001J\000\000\002\238\000\000\001J\003\004\001J\003\"\000\000\001J\0038\001J\000\164\000\168\000\000\001J\003V\001J\003l\000\000\000\152\002\n\000\000\002\n\000\000\002\n\000\000\001\158\001J\0022\001J\002X\001J\002v\001J\002\140\001J\002\170\001J\002\208\000\000\001\158\000&\000\000\002\n\000\007\002\n\000\000\000J\001j\000\000\003\168\000\196\000\000\003\160\001j\000\172\002\n\000d\001\204\000\184\002\n\000j\001\204\000\196\002\n\000\130\001\204\000\238\000\228\000\000\000\206\000\022\002\018\000\000\000\000\000\244\002\n\000\246\000\020\000\246\001\204\000\250\000\000\000\236\002\n\000\142\001\012\000\000\000\000\000*\000$\001J\001\158\000\000\001\014\000\000\000\\\000*\000\000\000\000\000\000\001P\001\018\000\000\000\238\000\020\000\000\000\236\000\222\001\204\000\000\000\000\000\000\000\000\000\000\000\224\001j\001\002\000\022\001$\002\n\001&\000\020\001&\001j\000\000\001j\000\000\001*\000\000\001,\000\000\000\000\000\170\000$\000\r\0018\001&\001j\001T\000\000\000*\000\000\000\000\001$\000\000\000\000"), (16, "\000\161\000\161\000\161\000\245\000V\000=\000=\001)\000\161\000\n\000\161\000\161\001\246\001\246\000\161\000J\000\161\000\161\000Z\000\221\000\018\000\161\000\161\002>\000b\000\006\000\145\000\161\001~\000\237\000\014\000\026\000\161\000\161\000\138\000\185\000\185\000\161\000&\000\161\002\242\000=\000\185\001\138\000\158\000\185\001\150\000\018\000\185\0002\000\185\000\185\0006\002B\001!\000\185\000\185\000\213\000\145\001\190\000R\000\185\001\206\001\130\000^\001\138\000\166\000\185\000\138\000\189\000\189\000\185\000f\000\185\001\222\000n\000\189\000v\000\158\000\189\002.\001\130\000\189\001\138\000\189\000\189\002Z\002\238\000\202\000\189\000\189\001\006\001\n\000\237\001\130\000\189\001\138\001\130\001&\001\138\000\166\000\189\000\138\000\169\000\169\000\189\001\166\000\189\001\182\001\130\000\169\001\138\000\158\000\169\001\198\001\130\000\169\001\138\000\169\000\169\001\214\001\230\001\234\000\169\000\169\001\242\001\001\001\017\001\017\000\169\002\006\002\014\002\022\002\030\000\166\000\169\000\138\000\165\000\165\000\169\002&\000\169\0022\002R\000\165\002r\000\158\000\165\002\138\002\166\000\165\002\174\000\165\000\165\002\182\002\190\002\198\000\165\000\165\002z\002\218\002\226\001\130\000\165\001\138\002\250\000B\000F\000\166\000\165\001=\001=\002\254\000\165\000\229\000\165\001=\000N\001=\001=\000z\003\006\003\027\000:\001\"\000\000\000~\000\130\000\000\001\154\000\000\001\158\000\205\001=\001=\001=\000\000\000\000\001=\001=\000\000\000\000\000\000\000\000\000\000\001Q\001\174\000\018\001\178\000\000\001=\001\226\002\170\001=\000\138\000\149\000\146\000\000\000\000\000\000\000\000\000\000\000\150\002\026\000\158\001B\002\"\000\000\000\174\000\000\001J\001R\000:\001\194\000\000\001Z\001b\000\000\001\154\000\000\001\158\001j\000\000\000\000\000\000\000\000\000\166\000\149\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\174\000\018\001\210\000\000\000\000\001\226\001\238\000B\000F\000\000\000\000\001*\000\000\000\000\000\253\000\000\000>\002\026\000N\000\000\002\"\000z\000\000\000\222\000\226\000\000\000\234\000~\001.\000\242\000\246\000\000\000\254\000\138\000U\000U\000\000\000\000\0012\0016\000\000\000\150\000\000\000\158\000\000\001\014\000\000\000\174\001\022\001:\000\000\001\030\000\138\000I\000I\000\000\000\000\000\000\000\000\000\000\000\150\000\000\000\158\000\000\000\000\000\166\000\174\000\138\000A\000A\000U\000\000\000U\000\000\000\000\000\150\000\000\000\158\000\138\000M\000M\000\174\000\000\000\000\000\166\000\000\000\150\000\000\000\158\000I\000\000\000I\000\174\000\138\000E\000E\000\000\000\000\000\000\000\166\000\000\000\150\000\000\000\158\000A\000\000\000A\000\174\000\000\000\000\000\166\000\000\000\138\000Q\000Q\000M\000\000\000M\000\000\000\000\000\150\000\000\000\158\000\000\000\000\000\166\000\174\000\138\000\t\000\t\000E\000\000\000E\000\000\000\000\000\150\000\000\000\158\000\138\000\021\000\021\000\174\000\000\000\000\000\166\000\000\000\150\000\000\000\158\000Q\000\000\000Q\000\174\000\138\000\017\000\017\000\000\000\000\000\000\000\166\000\t\000\150\000\000\000\158\000\138\000\025\000\025\000\174\000\000\000\000\000\166\000\021\000\150\000\000\000\158\000\000\000\000\000\000\000\174\000\138\000\005\000\005\000\000\000\000\000\000\000\166\000\017\000\150\000\000\000\158\000\138\000\r\000\r\000\174\000\000\000\000\000\166\000\025\000\150\000\138\000\158\001\025\000\000\000\000\000\174\000\000\000\000\000\150\000\000\000\158\000\000\000\166\000\005\000\174\000B\000F\000\138\001\t\000\000\000\000\000\000\001\005\000\166\000\r\000\150\000N\000\158\000\000\000z\000\000\000\174\000\166\000\210\000\000\000~\000\130\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\166"))
  
  and lhs =
    (8, "\000\028\028\028\028\028\028\028\028\027\026\026\026\026\026\026\026\026\026\026\026\026\026\025\025\025\025\025\025\025\025\025\025\024\023\023\022\022\021\021\021\021\021\021\021\021\021\021\021\021\020\019\019\018\018\017\017\016\016\015\015\014\014\r\r\012\012\011\n\n\t\t\b\b\007\007\006\006\006\005\005\005\005\005\004\004\004\004\003\003\002\001")
  
  and goto =
    ((16, "\000\003\000\000\000\000\000,\000\000\000\000\000\000\000\000\000\000\000\138\000\000\000\000\000\000\000\004\000\000\000!\000\000\000\000\000\148\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000,\000\000\000\000\000\020\000^\000b\000\000\000r\000\000\000\000\000\170\000\000\000\238\000\000\001\016\000\000\001\018\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\184\000\000\000\000\000\000\001\022\000\000\001\024\000\000\000\000\001\026\000\000\000\176\000\000\000\000\000\000\001\028\000\000\001\030\000\000\000\000\000\000\000\003\000\000\000\162\000\000\000\216\000\000\000\000\001 \000\000\001\"\000\000\001$\000\000\001&\000\000\001*\000\000\001,\000\000\000\000\000\000\000\000\000\000\000\234\000\000\000\246\000\000\000\000\000z\000\000\0004\000\000\000\000\000\000\000\014\000\000\000\252\000\000\000\018\000\000\000\254\000\000\000\028\000\000\001\004\000\000\000N\000\000\000\000\000\000\000\000\000\190\000\000\000\000\000\000\000\000\000N\000\000\000\200\000\000\000X\000\000\000\000\000\000\001\n\000\000\000\000\000\000\000\000\000\248\000\000\001.\000\000\000\000\000\000\000\000\000\000\001&\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\150\000\000\000\000\000\000\000b\000\000\000\000\000\000\000\000\000\000\000\000\000\172\000\000\000\216\000\000\000\248\000\000\000\228\000\000\000\182\000\000\000l\000\000\000\000\000\000\000\000\000\000\000\000\000\248\000\000\000\238\000\000\000\000\000p\000\000\000\000\000\194\000\000\000\000\000\000\000\000\000\000"), (8, "\186\187\195\142\1437\027\180\142\143\142\143\180\169\166\142\143\198\167\168P\184\197\200\006e\182\179\029\b\156/\179\t\155\156\012\156i\155\142\143\156\162\166\142\143k\153\154\142\143\131\164\165\142\143\142\143\180P\180\142\143\155\161\168\156.\155\"\006\156\181\155\193\011\156$\179\t\179\1560\156\160\179\142\143\1561\165\142\14324\1540\186\187\1956^\1581\127'_A4\127\179\1284\156\196\179\128\127\156\197\006\129\158\127\128\b\133\158P\t\128\147\190]\173\158\175P\148)\177\158bPP\150PPd\161PosP\152w+-\139:<?EGRTVX\150Z\\\146"))
  
  and semantic_action =
    [|
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x_inlined1;
          MenhirLib.EngineTypes.startp = _startpos_x_inlined1_;
          MenhirLib.EngineTypes.endp = _endpos_x_inlined1_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _2;
            MenhirLib.EngineTypes.startp = _startpos__2_;
            MenhirLib.EngineTypes.endp = _endpos__2_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _menhir_s;
              MenhirLib.EngineTypes.semv = x;
              MenhirLib.EngineTypes.startp = _startpos_x_;
              MenhirLib.EngineTypes.endp = _endpos_x_;
              MenhirLib.EngineTypes.next = _menhir_stack;
            };
          };
        } = _menhir_stack in
        let x_inlined1 : 'tv_int_expr = Obj.magic x_inlined1 in
        let _2 : unit = Obj.magic _2 in
        let x : (
# 66 "frontend/parser.mly"
       (string)
# 326 "frontend/parser.ml"
        ) = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_inlined1_ in
        let _v : 'tv_assign = let f =
          let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 338 "frontend/parser.ml"
          
        in
        let e =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 347 "frontend/parser.ml"
          
        in
        
# 235 "frontend/parser.mly"
    ( AST_assign (e, f) )
# 353 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x_inlined1;
          MenhirLib.EngineTypes.startp = _startpos_x_inlined1_;
          MenhirLib.EngineTypes.endp = _endpos_x_inlined1_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _1;
            MenhirLib.EngineTypes.startp = _startpos__1_;
            MenhirLib.EngineTypes.endp = _endpos__1_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _menhir_s;
              MenhirLib.EngineTypes.semv = x;
              MenhirLib.EngineTypes.startp = _startpos_x_;
              MenhirLib.EngineTypes.endp = _endpos_x_;
              MenhirLib.EngineTypes.next = _menhir_stack;
            };
          };
        } = _menhir_stack in
        let x_inlined1 : 'tv_int_expr = Obj.magic x_inlined1 in
        let _1 : unit = Obj.magic _1 in
        let x : (
# 66 "frontend/parser.mly"
       (string)
# 388 "frontend/parser.ml"
        ) = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_inlined1_ in
        let _v : 'tv_assign = let f =
          let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 400 "frontend/parser.ml"
          
        in
        let o = 
# 174 "frontend/parser.mly"
                           ( AST_MULTIPLY )
# 406 "frontend/parser.ml"
         in
        let e =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 414 "frontend/parser.ml"
          
        in
        
# 238 "frontend/parser.mly"
    ( AST_assign_op (e, o, f) )
# 420 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x_inlined1;
          MenhirLib.EngineTypes.startp = _startpos_x_inlined1_;
          MenhirLib.EngineTypes.endp = _endpos_x_inlined1_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _1;
            MenhirLib.EngineTypes.startp = _startpos__1_;
            MenhirLib.EngineTypes.endp = _endpos__1_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _menhir_s;
              MenhirLib.EngineTypes.semv = x;
              MenhirLib.EngineTypes.startp = _startpos_x_;
              MenhirLib.EngineTypes.endp = _endpos_x_;
              MenhirLib.EngineTypes.next = _menhir_stack;
            };
          };
        } = _menhir_stack in
        let x_inlined1 : 'tv_int_expr = Obj.magic x_inlined1 in
        let _1 : unit = Obj.magic _1 in
        let x : (
# 66 "frontend/parser.mly"
       (string)
# 455 "frontend/parser.ml"
        ) = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_inlined1_ in
        let _v : 'tv_assign = let f =
          let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 467 "frontend/parser.ml"
          
        in
        let o = 
# 175 "frontend/parser.mly"
                           ( AST_DIVIDE )
# 473 "frontend/parser.ml"
         in
        let e =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 481 "frontend/parser.ml"
          
        in
        
# 238 "frontend/parser.mly"
    ( AST_assign_op (e, o, f) )
# 487 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x_inlined1;
          MenhirLib.EngineTypes.startp = _startpos_x_inlined1_;
          MenhirLib.EngineTypes.endp = _endpos_x_inlined1_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _1;
            MenhirLib.EngineTypes.startp = _startpos__1_;
            MenhirLib.EngineTypes.endp = _endpos__1_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _menhir_s;
              MenhirLib.EngineTypes.semv = x;
              MenhirLib.EngineTypes.startp = _startpos_x_;
              MenhirLib.EngineTypes.endp = _endpos_x_;
              MenhirLib.EngineTypes.next = _menhir_stack;
            };
          };
        } = _menhir_stack in
        let x_inlined1 : 'tv_int_expr = Obj.magic x_inlined1 in
        let _1 : unit = Obj.magic _1 in
        let x : (
# 66 "frontend/parser.mly"
       (string)
# 522 "frontend/parser.ml"
        ) = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_inlined1_ in
        let _v : 'tv_assign = let f =
          let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 534 "frontend/parser.ml"
          
        in
        let o = 
# 176 "frontend/parser.mly"
                           ( AST_MODULO )
# 540 "frontend/parser.ml"
         in
        let e =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 548 "frontend/parser.ml"
          
        in
        
# 238 "frontend/parser.mly"
    ( AST_assign_op (e, o, f) )
# 554 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x_inlined1;
          MenhirLib.EngineTypes.startp = _startpos_x_inlined1_;
          MenhirLib.EngineTypes.endp = _endpos_x_inlined1_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _1;
            MenhirLib.EngineTypes.startp = _startpos__1_;
            MenhirLib.EngineTypes.endp = _endpos__1_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _menhir_s;
              MenhirLib.EngineTypes.semv = x;
              MenhirLib.EngineTypes.startp = _startpos_x_;
              MenhirLib.EngineTypes.endp = _endpos_x_;
              MenhirLib.EngineTypes.next = _menhir_stack;
            };
          };
        } = _menhir_stack in
        let x_inlined1 : 'tv_int_expr = Obj.magic x_inlined1 in
        let _1 : unit = Obj.magic _1 in
        let x : (
# 66 "frontend/parser.mly"
       (string)
# 589 "frontend/parser.ml"
        ) = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_inlined1_ in
        let _v : 'tv_assign = let f =
          let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 601 "frontend/parser.ml"
          
        in
        let o = 
# 177 "frontend/parser.mly"
                           ( AST_PLUS )
# 607 "frontend/parser.ml"
         in
        let e =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 615 "frontend/parser.ml"
          
        in
        
# 238 "frontend/parser.mly"
    ( AST_assign_op (e, o, f) )
# 621 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x_inlined1;
          MenhirLib.EngineTypes.startp = _startpos_x_inlined1_;
          MenhirLib.EngineTypes.endp = _endpos_x_inlined1_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _1;
            MenhirLib.EngineTypes.startp = _startpos__1_;
            MenhirLib.EngineTypes.endp = _endpos__1_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _menhir_s;
              MenhirLib.EngineTypes.semv = x;
              MenhirLib.EngineTypes.startp = _startpos_x_;
              MenhirLib.EngineTypes.endp = _endpos_x_;
              MenhirLib.EngineTypes.next = _menhir_stack;
            };
          };
        } = _menhir_stack in
        let x_inlined1 : 'tv_int_expr = Obj.magic x_inlined1 in
        let _1 : unit = Obj.magic _1 in
        let x : (
# 66 "frontend/parser.mly"
       (string)
# 656 "frontend/parser.ml"
        ) = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_inlined1_ in
        let _v : 'tv_assign = let f =
          let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 668 "frontend/parser.ml"
          
        in
        let o = 
# 178 "frontend/parser.mly"
                           ( AST_MINUS )
# 674 "frontend/parser.ml"
         in
        let e =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 682 "frontend/parser.ml"
          
        in
        
# 238 "frontend/parser.mly"
    ( AST_assign_op (e, o, f) )
# 688 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = _2;
          MenhirLib.EngineTypes.startp = _startpos__2_;
          MenhirLib.EngineTypes.endp = _endpos__2_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _menhir_s;
            MenhirLib.EngineTypes.semv = x;
            MenhirLib.EngineTypes.startp = _startpos_x_;
            MenhirLib.EngineTypes.endp = _endpos_x_;
            MenhirLib.EngineTypes.next = _menhir_stack;
          };
        } = _menhir_stack in
        let _2 : unit = Obj.magic _2 in
        let x : (
# 66 "frontend/parser.mly"
       (string)
# 716 "frontend/parser.ml"
        ) = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos__2_ in
        let _v : 'tv_assign = let e =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 727 "frontend/parser.ml"
          
        in
        
# 241 "frontend/parser.mly"
    ( AST_increment (e,1) )
# 733 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = _2;
          MenhirLib.EngineTypes.startp = _startpos__2_;
          MenhirLib.EngineTypes.endp = _endpos__2_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _menhir_s;
            MenhirLib.EngineTypes.semv = x;
            MenhirLib.EngineTypes.startp = _startpos_x_;
            MenhirLib.EngineTypes.endp = _endpos_x_;
            MenhirLib.EngineTypes.next = _menhir_stack;
          };
        } = _menhir_stack in
        let _2 : unit = Obj.magic _2 in
        let x : (
# 66 "frontend/parser.mly"
       (string)
# 761 "frontend/parser.ml"
        ) = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos__2_ in
        let _v : 'tv_assign = let e =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 772 "frontend/parser.ml"
          
        in
        
# 244 "frontend/parser.mly"
    ( AST_increment (e,-1); )
# 778 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = xs;
          MenhirLib.EngineTypes.startp = _startpos_xs_;
          MenhirLib.EngineTypes.endp = _endpos_xs_;
          MenhirLib.EngineTypes.next = _menhir_stack;
        } = _menhir_stack in
        let xs : 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_assign___ = Obj.magic xs in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_xs_ in
        let _endpos = _endpos_xs_ in
        let _v : 'tv_assign_list = let l = 
# 232 "<standard.mly>"
    ( xs )
# 803 "frontend/parser.ml"
         in
        
# 248 "frontend/parser.mly"
                                             ( l )
# 808 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = _3;
          MenhirLib.EngineTypes.startp = _startpos__3_;
          MenhirLib.EngineTypes.endp = _endpos__3_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = e;
            MenhirLib.EngineTypes.startp = _startpos_e_;
            MenhirLib.EngineTypes.endp = _endpos_e_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _menhir_s;
              MenhirLib.EngineTypes.semv = _1;
              MenhirLib.EngineTypes.startp = _startpos__1_;
              MenhirLib.EngineTypes.endp = _endpos__1_;
              MenhirLib.EngineTypes.next = _menhir_stack;
            };
          };
        } = _menhir_stack in
        let _3 : unit = Obj.magic _3 in
        let e : 'tv_bool_expr = Obj.magic e in
        let _1 : unit = Obj.magic _1 in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__3_ in
        let _v : 'tv_bool_expr = 
# 104 "frontend/parser.mly"
    ( e )
# 847 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = _1;
          MenhirLib.EngineTypes.startp = _startpos__1_;
          MenhirLib.EngineTypes.endp = _endpos__1_;
          MenhirLib.EngineTypes.next = _menhir_stack;
        } = _menhir_stack in
        let _1 : unit = Obj.magic _1 in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__1_ in
        let _v : 'tv_bool_expr = 
# 107 "frontend/parser.mly"
    ( AST_bool_const true )
# 872 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = _1;
          MenhirLib.EngineTypes.startp = _startpos__1_;
          MenhirLib.EngineTypes.endp = _endpos__1_;
          MenhirLib.EngineTypes.next = _menhir_stack;
        } = _menhir_stack in
        let _1 : unit = Obj.magic _1 in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__1_ in
        let _v : 'tv_bool_expr = 
# 110 "frontend/parser.mly"
    ( AST_bool_const false )
# 897 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x;
          MenhirLib.EngineTypes.startp = _startpos_x_;
          MenhirLib.EngineTypes.endp = _endpos_x_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _menhir_s;
            MenhirLib.EngineTypes.semv = _1;
            MenhirLib.EngineTypes.startp = _startpos__1_;
            MenhirLib.EngineTypes.endp = _endpos__1_;
            MenhirLib.EngineTypes.next = _menhir_stack;
          };
        } = _menhir_stack in
        let x : 'tv_bool_expr = Obj.magic x in
        let _1 : unit = Obj.magic _1 in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_x_ in
        let _v : 'tv_bool_expr = let e =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 932 "frontend/parser.ml"
          
        in
        let o = 
# 164 "frontend/parser.mly"
                     ( AST_NOT )
# 938 "frontend/parser.ml"
         in
        
# 113 "frontend/parser.mly"
    ( AST_bool_unary (o,e) )
# 943 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x_inlined1;
          MenhirLib.EngineTypes.startp = _startpos_x_inlined1_;
          MenhirLib.EngineTypes.endp = _endpos_x_inlined1_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _1;
            MenhirLib.EngineTypes.startp = _startpos__1_;
            MenhirLib.EngineTypes.endp = _endpos__1_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _menhir_s;
              MenhirLib.EngineTypes.semv = x;
              MenhirLib.EngineTypes.startp = _startpos_x_;
              MenhirLib.EngineTypes.endp = _endpos_x_;
              MenhirLib.EngineTypes.next = _menhir_stack;
            };
          };
        } = _menhir_stack in
        let x_inlined1 : 'tv_bool_expr = Obj.magic x_inlined1 in
        let _1 : unit = Obj.magic _1 in
        let x : 'tv_bool_expr = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_inlined1_ in
        let _v : 'tv_bool_expr = let e2 =
          let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 986 "frontend/parser.ml"
          
        in
        let o = 
# 189 "frontend/parser.mly"
                     ( AST_AND )
# 992 "frontend/parser.ml"
         in
        let e1 =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1000 "frontend/parser.ml"
          
        in
        
# 116 "frontend/parser.mly"
    ( AST_bool_binary (o,e1,e2) )
# 1006 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x_inlined1;
          MenhirLib.EngineTypes.startp = _startpos_x_inlined1_;
          MenhirLib.EngineTypes.endp = _endpos_x_inlined1_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _1;
            MenhirLib.EngineTypes.startp = _startpos__1_;
            MenhirLib.EngineTypes.endp = _endpos__1_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _menhir_s;
              MenhirLib.EngineTypes.semv = x;
              MenhirLib.EngineTypes.startp = _startpos_x_;
              MenhirLib.EngineTypes.endp = _endpos_x_;
              MenhirLib.EngineTypes.next = _menhir_stack;
            };
          };
        } = _menhir_stack in
        let x_inlined1 : 'tv_bool_expr = Obj.magic x_inlined1 in
        let _1 : unit = Obj.magic _1 in
        let x : 'tv_bool_expr = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_inlined1_ in
        let _v : 'tv_bool_expr = let e2 =
          let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1049 "frontend/parser.ml"
          
        in
        let o = 
# 190 "frontend/parser.mly"
                     ( AST_OR )
# 1055 "frontend/parser.ml"
         in
        let e1 =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1063 "frontend/parser.ml"
          
        in
        
# 116 "frontend/parser.mly"
    ( AST_bool_binary (o,e1,e2) )
# 1069 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x_inlined1;
          MenhirLib.EngineTypes.startp = _startpos_x_inlined1_;
          MenhirLib.EngineTypes.endp = _endpos_x_inlined1_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _1;
            MenhirLib.EngineTypes.startp = _startpos__1_;
            MenhirLib.EngineTypes.endp = _endpos__1_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _menhir_s;
              MenhirLib.EngineTypes.semv = x;
              MenhirLib.EngineTypes.startp = _startpos_x_;
              MenhirLib.EngineTypes.endp = _endpos_x_;
              MenhirLib.EngineTypes.next = _menhir_stack;
            };
          };
        } = _menhir_stack in
        let x_inlined1 : 'tv_int_expr = Obj.magic x_inlined1 in
        let _1 : unit = Obj.magic _1 in
        let x : 'tv_int_expr = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_inlined1_ in
        let _v : 'tv_bool_expr = let e2 =
          let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1112 "frontend/parser.ml"
          
        in
        let o = 
# 181 "frontend/parser.mly"
                     ( AST_LESS )
# 1118 "frontend/parser.ml"
         in
        let e1 =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1126 "frontend/parser.ml"
          
        in
        
# 119 "frontend/parser.mly"
    ( AST_compare (o,e1,e2) )
# 1132 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x_inlined1;
          MenhirLib.EngineTypes.startp = _startpos_x_inlined1_;
          MenhirLib.EngineTypes.endp = _endpos_x_inlined1_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _1;
            MenhirLib.EngineTypes.startp = _startpos__1_;
            MenhirLib.EngineTypes.endp = _endpos__1_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _menhir_s;
              MenhirLib.EngineTypes.semv = x;
              MenhirLib.EngineTypes.startp = _startpos_x_;
              MenhirLib.EngineTypes.endp = _endpos_x_;
              MenhirLib.EngineTypes.next = _menhir_stack;
            };
          };
        } = _menhir_stack in
        let x_inlined1 : 'tv_int_expr = Obj.magic x_inlined1 in
        let _1 : unit = Obj.magic _1 in
        let x : 'tv_int_expr = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_inlined1_ in
        let _v : 'tv_bool_expr = let e2 =
          let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1175 "frontend/parser.ml"
          
        in
        let o = 
# 182 "frontend/parser.mly"
                     ( AST_GREATER )
# 1181 "frontend/parser.ml"
         in
        let e1 =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1189 "frontend/parser.ml"
          
        in
        
# 119 "frontend/parser.mly"
    ( AST_compare (o,e1,e2) )
# 1195 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x_inlined1;
          MenhirLib.EngineTypes.startp = _startpos_x_inlined1_;
          MenhirLib.EngineTypes.endp = _endpos_x_inlined1_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _1;
            MenhirLib.EngineTypes.startp = _startpos__1_;
            MenhirLib.EngineTypes.endp = _endpos__1_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _menhir_s;
              MenhirLib.EngineTypes.semv = x;
              MenhirLib.EngineTypes.startp = _startpos_x_;
              MenhirLib.EngineTypes.endp = _endpos_x_;
              MenhirLib.EngineTypes.next = _menhir_stack;
            };
          };
        } = _menhir_stack in
        let x_inlined1 : 'tv_int_expr = Obj.magic x_inlined1 in
        let _1 : unit = Obj.magic _1 in
        let x : 'tv_int_expr = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_inlined1_ in
        let _v : 'tv_bool_expr = let e2 =
          let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1238 "frontend/parser.ml"
          
        in
        let o = 
# 183 "frontend/parser.mly"
                     ( AST_LESS_EQUAL )
# 1244 "frontend/parser.ml"
         in
        let e1 =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1252 "frontend/parser.ml"
          
        in
        
# 119 "frontend/parser.mly"
    ( AST_compare (o,e1,e2) )
# 1258 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x_inlined1;
          MenhirLib.EngineTypes.startp = _startpos_x_inlined1_;
          MenhirLib.EngineTypes.endp = _endpos_x_inlined1_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _1;
            MenhirLib.EngineTypes.startp = _startpos__1_;
            MenhirLib.EngineTypes.endp = _endpos__1_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _menhir_s;
              MenhirLib.EngineTypes.semv = x;
              MenhirLib.EngineTypes.startp = _startpos_x_;
              MenhirLib.EngineTypes.endp = _endpos_x_;
              MenhirLib.EngineTypes.next = _menhir_stack;
            };
          };
        } = _menhir_stack in
        let x_inlined1 : 'tv_int_expr = Obj.magic x_inlined1 in
        let _1 : unit = Obj.magic _1 in
        let x : 'tv_int_expr = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_inlined1_ in
        let _v : 'tv_bool_expr = let e2 =
          let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1301 "frontend/parser.ml"
          
        in
        let o = 
# 184 "frontend/parser.mly"
                     ( AST_GREATER_EQUAL )
# 1307 "frontend/parser.ml"
         in
        let e1 =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1315 "frontend/parser.ml"
          
        in
        
# 119 "frontend/parser.mly"
    ( AST_compare (o,e1,e2) )
# 1321 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x_inlined1;
          MenhirLib.EngineTypes.startp = _startpos_x_inlined1_;
          MenhirLib.EngineTypes.endp = _endpos_x_inlined1_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _1;
            MenhirLib.EngineTypes.startp = _startpos__1_;
            MenhirLib.EngineTypes.endp = _endpos__1_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _menhir_s;
              MenhirLib.EngineTypes.semv = x;
              MenhirLib.EngineTypes.startp = _startpos_x_;
              MenhirLib.EngineTypes.endp = _endpos_x_;
              MenhirLib.EngineTypes.next = _menhir_stack;
            };
          };
        } = _menhir_stack in
        let x_inlined1 : 'tv_int_expr = Obj.magic x_inlined1 in
        let _1 : unit = Obj.magic _1 in
        let x : 'tv_int_expr = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_inlined1_ in
        let _v : 'tv_bool_expr = let e2 =
          let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1364 "frontend/parser.ml"
          
        in
        let o = 
# 185 "frontend/parser.mly"
                     ( AST_EQUAL )
# 1370 "frontend/parser.ml"
         in
        let e1 =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1378 "frontend/parser.ml"
          
        in
        
# 119 "frontend/parser.mly"
    ( AST_compare (o,e1,e2) )
# 1384 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x_inlined1;
          MenhirLib.EngineTypes.startp = _startpos_x_inlined1_;
          MenhirLib.EngineTypes.endp = _endpos_x_inlined1_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _1;
            MenhirLib.EngineTypes.startp = _startpos__1_;
            MenhirLib.EngineTypes.endp = _endpos__1_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _menhir_s;
              MenhirLib.EngineTypes.semv = x;
              MenhirLib.EngineTypes.startp = _startpos_x_;
              MenhirLib.EngineTypes.endp = _endpos_x_;
              MenhirLib.EngineTypes.next = _menhir_stack;
            };
          };
        } = _menhir_stack in
        let x_inlined1 : 'tv_int_expr = Obj.magic x_inlined1 in
        let _1 : unit = Obj.magic _1 in
        let x : 'tv_int_expr = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_inlined1_ in
        let _v : 'tv_bool_expr = let e2 =
          let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1427 "frontend/parser.ml"
          
        in
        let o = 
# 186 "frontend/parser.mly"
                     ( AST_NOT_EQUAL )
# 1433 "frontend/parser.ml"
         in
        let e1 =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1441 "frontend/parser.ml"
          
        in
        
# 119 "frontend/parser.mly"
    ( AST_compare (o,e1,e2) )
# 1447 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = _1;
          MenhirLib.EngineTypes.startp = _startpos__1_;
          MenhirLib.EngineTypes.endp = _endpos__1_;
          MenhirLib.EngineTypes.next = _menhir_stack;
        } = _menhir_stack in
        let _1 : unit = Obj.magic _1 in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__1_ in
        let _v : 'tv_bool_expr = 
# 122 "frontend/parser.mly"
    ( AST_bool_rand )
# 1472 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = _2;
          MenhirLib.EngineTypes.startp = _startpos__2_;
          MenhirLib.EngineTypes.endp = _endpos__2_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _menhir_s;
            MenhirLib.EngineTypes.semv = a;
            MenhirLib.EngineTypes.startp = _startpos_a_;
            MenhirLib.EngineTypes.endp = _endpos_a_;
            MenhirLib.EngineTypes.next = _menhir_stack;
          };
        } = _menhir_stack in
        let _2 : unit = Obj.magic _2 in
        let a : 'tv_assign = Obj.magic a in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_a_ in
        let _endpos = _endpos__2_ in
        let _v : 'tv_common_stat = 
# 251 "frontend/parser.mly"
                         ( a )
# 1504 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = x;
          MenhirLib.EngineTypes.startp = _startpos_x_;
          MenhirLib.EngineTypes.endp = _endpos_x_;
          MenhirLib.EngineTypes.next = _menhir_stack;
        } = _menhir_stack in
        let x : 'tv_var_decl = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_ in
        let _v : 'tv_common_stat = let d =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1532 "frontend/parser.ml"
          
        in
        
# 252 "frontend/parser.mly"
                  ( AST_local_decl d )
# 1538 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = _3;
          MenhirLib.EngineTypes.startp = _startpos__3_;
          MenhirLib.EngineTypes.endp = _endpos__3_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = l;
            MenhirLib.EngineTypes.startp = _startpos_l_;
            MenhirLib.EngineTypes.endp = _endpos_l_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _menhir_s;
              MenhirLib.EngineTypes.semv = _1;
              MenhirLib.EngineTypes.startp = _startpos__1_;
              MenhirLib.EngineTypes.endp = _endpos__1_;
              MenhirLib.EngineTypes.next = _menhir_stack;
            };
          };
        } = _menhir_stack in
        let _3 : unit = Obj.magic _3 in
        let l : 'tv_list_ext_stat__ = Obj.magic l in
        let _1 : unit = Obj.magic _1 in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__3_ in
        let _v : 'tv_common_stat = 
# 253 "frontend/parser.mly"
                                          ( AST_block l )
# 1577 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = _2;
          MenhirLib.EngineTypes.startp = _startpos__2_;
          MenhirLib.EngineTypes.endp = _endpos__2_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _menhir_s;
            MenhirLib.EngineTypes.semv = x;
            MenhirLib.EngineTypes.startp = _startpos_x_;
            MenhirLib.EngineTypes.endp = _endpos_x_;
            MenhirLib.EngineTypes.next = _menhir_stack;
          };
        } = _menhir_stack in
        let _2 : unit = Obj.magic _2 in
        let x : (
# 66 "frontend/parser.mly"
       (string)
# 1605 "frontend/parser.ml"
        ) = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos__2_ in
        let _v : 'tv_common_stat = let e =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1616 "frontend/parser.ml"
          
        in
        
# 254 "frontend/parser.mly"
                          ( AST_label e )
# 1622 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = _5;
          MenhirLib.EngineTypes.startp = _startpos__5_;
          MenhirLib.EngineTypes.endp = _endpos__5_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _4;
            MenhirLib.EngineTypes.startp = _startpos__4_;
            MenhirLib.EngineTypes.endp = _endpos__4_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _;
              MenhirLib.EngineTypes.semv = x;
              MenhirLib.EngineTypes.startp = _startpos_x_;
              MenhirLib.EngineTypes.endp = _endpos_x_;
              MenhirLib.EngineTypes.next = {
                MenhirLib.EngineTypes.state = _;
                MenhirLib.EngineTypes.semv = _2;
                MenhirLib.EngineTypes.startp = _startpos__2_;
                MenhirLib.EngineTypes.endp = _endpos__2_;
                MenhirLib.EngineTypes.next = {
                  MenhirLib.EngineTypes.state = _menhir_s;
                  MenhirLib.EngineTypes.semv = _1;
                  MenhirLib.EngineTypes.startp = _startpos__1_;
                  MenhirLib.EngineTypes.endp = _endpos__1_;
                  MenhirLib.EngineTypes.next = _menhir_stack;
                };
              };
            };
          };
        } = _menhir_stack in
        let _5 : unit = Obj.magic _5 in
        let _4 : unit = Obj.magic _4 in
        let x : 'tv_bool_expr = Obj.magic x in
        let _2 : unit = Obj.magic _2 in
        let _1 : unit = Obj.magic _1 in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__5_ in
        let _v : 'tv_common_stat = let e =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1678 "frontend/parser.ml"
          
        in
        
# 255 "frontend/parser.mly"
                                                                  ( AST_assert e )
# 1684 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = _2;
          MenhirLib.EngineTypes.startp = _startpos__2_;
          MenhirLib.EngineTypes.endp = _endpos__2_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _menhir_s;
            MenhirLib.EngineTypes.semv = x;
            MenhirLib.EngineTypes.startp = _startpos_x_;
            MenhirLib.EngineTypes.endp = _endpos_x_;
            MenhirLib.EngineTypes.next = _menhir_stack;
          };
        } = _menhir_stack in
        let _2 : unit = Obj.magic _2 in
        let x : unit = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos__2_ in
        let _v : 'tv_common_stat = let e =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1719 "frontend/parser.ml"
          
        in
        
# 256 "frontend/parser.mly"
                                 ( AST_break e )
# 1725 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = _5;
          MenhirLib.EngineTypes.startp = _startpos__5_;
          MenhirLib.EngineTypes.endp = _endpos__5_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _4;
            MenhirLib.EngineTypes.startp = _startpos__4_;
            MenhirLib.EngineTypes.endp = _endpos__4_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _;
              MenhirLib.EngineTypes.semv = l;
              MenhirLib.EngineTypes.startp = _startpos_l_;
              MenhirLib.EngineTypes.endp = _endpos_l_;
              MenhirLib.EngineTypes.next = {
                MenhirLib.EngineTypes.state = _;
                MenhirLib.EngineTypes.semv = _2;
                MenhirLib.EngineTypes.startp = _startpos__2_;
                MenhirLib.EngineTypes.endp = _endpos__2_;
                MenhirLib.EngineTypes.next = {
                  MenhirLib.EngineTypes.state = _menhir_s;
                  MenhirLib.EngineTypes.semv = x;
                  MenhirLib.EngineTypes.startp = _startpos_x_;
                  MenhirLib.EngineTypes.endp = _endpos_x_;
                  MenhirLib.EngineTypes.next = _menhir_stack;
                };
              };
            };
          };
        } = _menhir_stack in
        let _5 : unit = Obj.magic _5 in
        let _4 : unit = Obj.magic _4 in
        let l : 'tv_int_expr_list = Obj.magic l in
        let _2 : unit = Obj.magic _2 in
        let x : (
# 66 "frontend/parser.mly"
       (string)
# 1774 "frontend/parser.ml"
        ) = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos__5_ in
        let _v : 'tv_common_stat = let e =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1785 "frontend/parser.ml"
          
        in
        
# 257 "frontend/parser.mly"
                                                                    ( AST_stat_call (e, l) )
# 1791 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = _3;
          MenhirLib.EngineTypes.startp = _startpos__3_;
          MenhirLib.EngineTypes.endp = _endpos__3_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = e;
            MenhirLib.EngineTypes.startp = _startpos_e_;
            MenhirLib.EngineTypes.endp = _endpos_e_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _menhir_s;
              MenhirLib.EngineTypes.semv = _1;
              MenhirLib.EngineTypes.startp = _startpos__1_;
              MenhirLib.EngineTypes.endp = _endpos__1_;
              MenhirLib.EngineTypes.next = _menhir_stack;
            };
          };
        } = _menhir_stack in
        let _3 : unit = Obj.magic _3 in
        let e : 'tv_option_ext_int_expr__ = Obj.magic e in
        let _1 : unit = Obj.magic _1 in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__3_ in
        let _v : 'tv_common_stat = 
# 258 "frontend/parser.mly"
                                                   ( AST_return e )
# 1830 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = _1;
          MenhirLib.EngineTypes.startp = _startpos__1_;
          MenhirLib.EngineTypes.endp = _endpos__1_;
          MenhirLib.EngineTypes.next = _menhir_stack;
        } = _menhir_stack in
        let _1 : unit = Obj.magic _1 in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__1_ in
        let _v : 'tv_common_stat = 
# 259 "frontend/parser.mly"
                ( AST_SKIP )
# 1855 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = _3;
          MenhirLib.EngineTypes.startp = _startpos__3_;
          MenhirLib.EngineTypes.endp = _endpos__3_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = x;
            MenhirLib.EngineTypes.startp = _startpos_x_;
            MenhirLib.EngineTypes.endp = _endpos_x_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _menhir_s;
              MenhirLib.EngineTypes.semv = _1;
              MenhirLib.EngineTypes.startp = _startpos__1_;
              MenhirLib.EngineTypes.endp = _endpos__1_;
              MenhirLib.EngineTypes.next = _menhir_stack;
            };
          };
        } = _menhir_stack in
        let _3 : unit = Obj.magic _3 in
        let x : (
# 66 "frontend/parser.mly"
       (string)
# 1889 "frontend/parser.ml"
        ) = Obj.magic x in
        let _1 : unit = Obj.magic _1 in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__3_ in
        let _v : 'tv_common_stat = let e =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1901 "frontend/parser.ml"
          
        in
        
# 260 "frontend/parser.mly"
                                       ( AST_goto e )
# 1907 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = _2;
          MenhirLib.EngineTypes.startp = _startpos__2_;
          MenhirLib.EngineTypes.endp = _endpos__2_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _menhir_s;
            MenhirLib.EngineTypes.semv = x;
            MenhirLib.EngineTypes.startp = _startpos_x_;
            MenhirLib.EngineTypes.endp = _endpos_x_;
            MenhirLib.EngineTypes.next = _menhir_stack;
          };
        } = _menhir_stack in
        let _2 : unit = Obj.magic _2 in
        let x : 'tv_list_toplevel_ = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos__2_ in
        let _v : (
# 82 "frontend/parser.mly"
      (Abstract_syntax_tree.toplevel list Abstract_syntax_tree.ext)
# 1939 "frontend/parser.ml"
        ) = let t =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1946 "frontend/parser.ml"
          
        in
        
# 91 "frontend/parser.mly"
                                    ( t )
# 1952 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = _8;
          MenhirLib.EngineTypes.startp = _startpos__8_;
          MenhirLib.EngineTypes.endp = _endpos__8_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = l;
            MenhirLib.EngineTypes.startp = _startpos_l_;
            MenhirLib.EngineTypes.endp = _endpos_l_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _;
              MenhirLib.EngineTypes.semv = _6;
              MenhirLib.EngineTypes.startp = _startpos__6_;
              MenhirLib.EngineTypes.endp = _endpos__6_;
              MenhirLib.EngineTypes.next = {
                MenhirLib.EngineTypes.state = _;
                MenhirLib.EngineTypes.semv = _5;
                MenhirLib.EngineTypes.startp = _startpos__5_;
                MenhirLib.EngineTypes.endp = _endpos__5_;
                MenhirLib.EngineTypes.next = {
                  MenhirLib.EngineTypes.state = _;
                  MenhirLib.EngineTypes.semv = xs;
                  MenhirLib.EngineTypes.startp = _startpos_xs_;
                  MenhirLib.EngineTypes.endp = _endpos_xs_;
                  MenhirLib.EngineTypes.next = {
                    MenhirLib.EngineTypes.state = _;
                    MenhirLib.EngineTypes.semv = _3;
                    MenhirLib.EngineTypes.startp = _startpos__3_;
                    MenhirLib.EngineTypes.endp = _endpos__3_;
                    MenhirLib.EngineTypes.next = {
                      MenhirLib.EngineTypes.state = _;
                      MenhirLib.EngineTypes.semv = x;
                      MenhirLib.EngineTypes.startp = _startpos_x_;
                      MenhirLib.EngineTypes.endp = _endpos_x_;
                      MenhirLib.EngineTypes.next = {
                        MenhirLib.EngineTypes.state = _menhir_s;
                        MenhirLib.EngineTypes.semv = t;
                        MenhirLib.EngineTypes.startp = _startpos_t_;
                        MenhirLib.EngineTypes.endp = _endpos_t_;
                        MenhirLib.EngineTypes.next = _menhir_stack;
                      };
                    };
                  };
                };
              };
            };
          };
        } = _menhir_stack in
        let _8 : unit = Obj.magic _8 in
        let l : 'tv_list_ext_stat__ = Obj.magic l in
        let _6 : unit = Obj.magic _6 in
        let _5 : unit = Obj.magic _5 in
        let xs : 'tv_loption_separated_nonempty_list_TOK_COMMA_param_decl__ = Obj.magic xs in
        let _3 : unit = Obj.magic _3 in
        let x : (
# 66 "frontend/parser.mly"
       (string)
# 2021 "frontend/parser.ml"
        ) = Obj.magic x in
        let t : 'tv_typ = Obj.magic t in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_t_ in
        let _endpos = _endpos__8_ in
        let _v : 'tv_fun_decl = let p = 
# 232 "<standard.mly>"
    ( xs )
# 2030 "frontend/parser.ml"
         in
        let i =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2038 "frontend/parser.ml"
          
        in
        let t =
          let x = 
# 223 "frontend/parser.mly"
             ( Some t )
# 2045 "frontend/parser.ml"
           in
          let (_endpos_x_, _startpos_x_) = (_endpos_t_, _startpos_t_) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2053 "frontend/parser.ml"
          
        in
        let _endpos = _endpos__8_ in
        let _startpos = _startpos_t_ in
        
# 209 "frontend/parser.mly"
  ( { Abstract_syntax_tree.fun_name = i;
      Abstract_syntax_tree.fun_typ = t;
      Abstract_syntax_tree.fun_args = p;
      Abstract_syntax_tree.fun_body = l;
      Abstract_syntax_tree.fun_ext = (_startpos, _endpos); }
  )
# 2066 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = _8;
          MenhirLib.EngineTypes.startp = _startpos__8_;
          MenhirLib.EngineTypes.endp = _endpos__8_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = l;
            MenhirLib.EngineTypes.startp = _startpos_l_;
            MenhirLib.EngineTypes.endp = _endpos_l_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _;
              MenhirLib.EngineTypes.semv = _6;
              MenhirLib.EngineTypes.startp = _startpos__6_;
              MenhirLib.EngineTypes.endp = _endpos__6_;
              MenhirLib.EngineTypes.next = {
                MenhirLib.EngineTypes.state = _;
                MenhirLib.EngineTypes.semv = _5;
                MenhirLib.EngineTypes.startp = _startpos__5_;
                MenhirLib.EngineTypes.endp = _endpos__5_;
                MenhirLib.EngineTypes.next = {
                  MenhirLib.EngineTypes.state = _;
                  MenhirLib.EngineTypes.semv = xs;
                  MenhirLib.EngineTypes.startp = _startpos_xs_;
                  MenhirLib.EngineTypes.endp = _endpos_xs_;
                  MenhirLib.EngineTypes.next = {
                    MenhirLib.EngineTypes.state = _;
                    MenhirLib.EngineTypes.semv = _3;
                    MenhirLib.EngineTypes.startp = _startpos__3_;
                    MenhirLib.EngineTypes.endp = _endpos__3_;
                    MenhirLib.EngineTypes.next = {
                      MenhirLib.EngineTypes.state = _;
                      MenhirLib.EngineTypes.semv = x;
                      MenhirLib.EngineTypes.startp = _startpos_x_;
                      MenhirLib.EngineTypes.endp = _endpos_x_;
                      MenhirLib.EngineTypes.next = {
                        MenhirLib.EngineTypes.state = _menhir_s;
                        MenhirLib.EngineTypes.semv = _1;
                        MenhirLib.EngineTypes.startp = _startpos__1_;
                        MenhirLib.EngineTypes.endp = _endpos__1_;
                        MenhirLib.EngineTypes.next = _menhir_stack;
                      };
                    };
                  };
                };
              };
            };
          };
        } = _menhir_stack in
        let _8 : unit = Obj.magic _8 in
        let l : 'tv_list_ext_stat__ = Obj.magic l in
        let _6 : unit = Obj.magic _6 in
        let _5 : unit = Obj.magic _5 in
        let xs : 'tv_loption_separated_nonempty_list_TOK_COMMA_param_decl__ = Obj.magic xs in
        let _3 : unit = Obj.magic _3 in
        let x : (
# 66 "frontend/parser.mly"
       (string)
# 2135 "frontend/parser.ml"
        ) = Obj.magic x in
        let _1 : unit = Obj.magic _1 in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__8_ in
        let _v : 'tv_fun_decl = let p = 
# 232 "<standard.mly>"
    ( xs )
# 2144 "frontend/parser.ml"
         in
        let i =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2152 "frontend/parser.ml"
          
        in
        let t =
          let x = 
# 224 "frontend/parser.mly"
             ( None )
# 2159 "frontend/parser.ml"
           in
          let (_endpos_x_, _startpos_x_) = (_endpos__1_, _startpos__1_) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2167 "frontend/parser.ml"
          
        in
        let _startpos_t_ = _startpos__1_ in
        let _endpos = _endpos__8_ in
        let _startpos = _startpos_t_ in
        
# 209 "frontend/parser.mly"
  ( { Abstract_syntax_tree.fun_name = i;
      Abstract_syntax_tree.fun_typ = t;
      Abstract_syntax_tree.fun_args = p;
      Abstract_syntax_tree.fun_body = l;
      Abstract_syntax_tree.fun_ext = (_startpos, _endpos); }
  )
# 2181 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = x;
          MenhirLib.EngineTypes.startp = _startpos_x_;
          MenhirLib.EngineTypes.endp = _endpos_x_;
          MenhirLib.EngineTypes.next = _menhir_stack;
        } = _menhir_stack in
        let x : (
# 66 "frontend/parser.mly"
       (string)
# 2202 "frontend/parser.ml"
        ) = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_ in
        let _v : 'tv_init_declarator = let v =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2213 "frontend/parser.ml"
          
        in
        
# 202 "frontend/parser.mly"
                                            ( v, None )
# 2219 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x_inlined1;
          MenhirLib.EngineTypes.startp = _startpos_x_inlined1_;
          MenhirLib.EngineTypes.endp = _endpos_x_inlined1_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _2;
            MenhirLib.EngineTypes.startp = _startpos__2_;
            MenhirLib.EngineTypes.endp = _endpos__2_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _menhir_s;
              MenhirLib.EngineTypes.semv = x;
              MenhirLib.EngineTypes.startp = _startpos_x_;
              MenhirLib.EngineTypes.endp = _endpos_x_;
              MenhirLib.EngineTypes.next = _menhir_stack;
            };
          };
        } = _menhir_stack in
        let x_inlined1 : 'tv_int_expr = Obj.magic x_inlined1 in
        let _2 : unit = Obj.magic _2 in
        let x : (
# 66 "frontend/parser.mly"
       (string)
# 2254 "frontend/parser.ml"
        ) = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_inlined1_ in
        let _v : 'tv_init_declarator = let i =
          let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2266 "frontend/parser.ml"
          
        in
        let v =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2275 "frontend/parser.ml"
          
        in
        
# 203 "frontend/parser.mly"
                                            ( v, Some i )
# 2281 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = _3;
          MenhirLib.EngineTypes.startp = _startpos__3_;
          MenhirLib.EngineTypes.endp = _endpos__3_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = e;
            MenhirLib.EngineTypes.startp = _startpos_e_;
            MenhirLib.EngineTypes.endp = _endpos_e_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _menhir_s;
              MenhirLib.EngineTypes.semv = _1;
              MenhirLib.EngineTypes.startp = _startpos__1_;
              MenhirLib.EngineTypes.endp = _endpos__1_;
              MenhirLib.EngineTypes.next = _menhir_stack;
            };
          };
        } = _menhir_stack in
        let _3 : unit = Obj.magic _3 in
        let e : 'tv_int_expr = Obj.magic e in
        let _1 : unit = Obj.magic _1 in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__3_ in
        let _v : 'tv_int_expr = 
# 127 "frontend/parser.mly"
    ( e )
# 2320 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = x;
          MenhirLib.EngineTypes.startp = _startpos_x_;
          MenhirLib.EngineTypes.endp = _endpos_x_;
          MenhirLib.EngineTypes.next = _menhir_stack;
        } = _menhir_stack in
        let x : (
# 67 "frontend/parser.mly"
       (string)
# 2341 "frontend/parser.ml"
        ) = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_ in
        let _v : 'tv_int_expr = let e =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2352 "frontend/parser.ml"
          
        in
        
# 130 "frontend/parser.mly"
    ( AST_int_const e )
# 2358 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = x;
          MenhirLib.EngineTypes.startp = _startpos_x_;
          MenhirLib.EngineTypes.endp = _endpos_x_;
          MenhirLib.EngineTypes.next = _menhir_stack;
        } = _menhir_stack in
        let x : (
# 66 "frontend/parser.mly"
       (string)
# 2379 "frontend/parser.ml"
        ) = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_ in
        let _v : 'tv_int_expr = let e =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2390 "frontend/parser.ml"
          
        in
        
# 133 "frontend/parser.mly"
    ( AST_int_identifier e )
# 2396 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x;
          MenhirLib.EngineTypes.startp = _startpos_x_;
          MenhirLib.EngineTypes.endp = _endpos_x_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _menhir_s;
            MenhirLib.EngineTypes.semv = _1;
            MenhirLib.EngineTypes.startp = _startpos__1_;
            MenhirLib.EngineTypes.endp = _endpos__1_;
            MenhirLib.EngineTypes.next = _menhir_stack;
          };
        } = _menhir_stack in
        let x : 'tv_int_expr = Obj.magic x in
        let _1 : unit = Obj.magic _1 in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_x_ in
        let _v : 'tv_int_expr = let e =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2431 "frontend/parser.ml"
          
        in
        let o = 
# 160 "frontend/parser.mly"
                     ( AST_UNARY_PLUS )
# 2437 "frontend/parser.ml"
         in
        
# 136 "frontend/parser.mly"
    ( AST_int_unary (o,e) )
# 2442 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x;
          MenhirLib.EngineTypes.startp = _startpos_x_;
          MenhirLib.EngineTypes.endp = _endpos_x_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _menhir_s;
            MenhirLib.EngineTypes.semv = _1;
            MenhirLib.EngineTypes.startp = _startpos__1_;
            MenhirLib.EngineTypes.endp = _endpos__1_;
            MenhirLib.EngineTypes.next = _menhir_stack;
          };
        } = _menhir_stack in
        let x : 'tv_int_expr = Obj.magic x in
        let _1 : unit = Obj.magic _1 in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_x_ in
        let _v : 'tv_int_expr = let e =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2477 "frontend/parser.ml"
          
        in
        let o = 
# 161 "frontend/parser.mly"
                     ( AST_UNARY_MINUS )
# 2483 "frontend/parser.ml"
         in
        
# 136 "frontend/parser.mly"
    ( AST_int_unary (o,e) )
# 2488 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x_inlined1;
          MenhirLib.EngineTypes.startp = _startpos_x_inlined1_;
          MenhirLib.EngineTypes.endp = _endpos_x_inlined1_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _1;
            MenhirLib.EngineTypes.startp = _startpos__1_;
            MenhirLib.EngineTypes.endp = _endpos__1_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _menhir_s;
              MenhirLib.EngineTypes.semv = x;
              MenhirLib.EngineTypes.startp = _startpos_x_;
              MenhirLib.EngineTypes.endp = _endpos_x_;
              MenhirLib.EngineTypes.next = _menhir_stack;
            };
          };
        } = _menhir_stack in
        let x_inlined1 : 'tv_int_expr = Obj.magic x_inlined1 in
        let _1 : unit = Obj.magic _1 in
        let x : 'tv_int_expr = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_inlined1_ in
        let _v : 'tv_int_expr = let e2 =
          let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2531 "frontend/parser.ml"
          
        in
        let o = 
# 167 "frontend/parser.mly"
                     ( AST_MULTIPLY )
# 2537 "frontend/parser.ml"
         in
        let e1 =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2545 "frontend/parser.ml"
          
        in
        
# 139 "frontend/parser.mly"
    ( AST_int_binary (o,e1,e2) )
# 2551 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x_inlined1;
          MenhirLib.EngineTypes.startp = _startpos_x_inlined1_;
          MenhirLib.EngineTypes.endp = _endpos_x_inlined1_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _1;
            MenhirLib.EngineTypes.startp = _startpos__1_;
            MenhirLib.EngineTypes.endp = _endpos__1_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _menhir_s;
              MenhirLib.EngineTypes.semv = x;
              MenhirLib.EngineTypes.startp = _startpos_x_;
              MenhirLib.EngineTypes.endp = _endpos_x_;
              MenhirLib.EngineTypes.next = _menhir_stack;
            };
          };
        } = _menhir_stack in
        let x_inlined1 : 'tv_int_expr = Obj.magic x_inlined1 in
        let _1 : unit = Obj.magic _1 in
        let x : 'tv_int_expr = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_inlined1_ in
        let _v : 'tv_int_expr = let e2 =
          let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2594 "frontend/parser.ml"
          
        in
        let o = 
# 168 "frontend/parser.mly"
                     ( AST_DIVIDE )
# 2600 "frontend/parser.ml"
         in
        let e1 =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2608 "frontend/parser.ml"
          
        in
        
# 139 "frontend/parser.mly"
    ( AST_int_binary (o,e1,e2) )
# 2614 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x_inlined1;
          MenhirLib.EngineTypes.startp = _startpos_x_inlined1_;
          MenhirLib.EngineTypes.endp = _endpos_x_inlined1_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _1;
            MenhirLib.EngineTypes.startp = _startpos__1_;
            MenhirLib.EngineTypes.endp = _endpos__1_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _menhir_s;
              MenhirLib.EngineTypes.semv = x;
              MenhirLib.EngineTypes.startp = _startpos_x_;
              MenhirLib.EngineTypes.endp = _endpos_x_;
              MenhirLib.EngineTypes.next = _menhir_stack;
            };
          };
        } = _menhir_stack in
        let x_inlined1 : 'tv_int_expr = Obj.magic x_inlined1 in
        let _1 : unit = Obj.magic _1 in
        let x : 'tv_int_expr = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_inlined1_ in
        let _v : 'tv_int_expr = let e2 =
          let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2657 "frontend/parser.ml"
          
        in
        let o = 
# 169 "frontend/parser.mly"
                     ( AST_MODULO )
# 2663 "frontend/parser.ml"
         in
        let e1 =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2671 "frontend/parser.ml"
          
        in
        
# 139 "frontend/parser.mly"
    ( AST_int_binary (o,e1,e2) )
# 2677 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x_inlined1;
          MenhirLib.EngineTypes.startp = _startpos_x_inlined1_;
          MenhirLib.EngineTypes.endp = _endpos_x_inlined1_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _1;
            MenhirLib.EngineTypes.startp = _startpos__1_;
            MenhirLib.EngineTypes.endp = _endpos__1_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _menhir_s;
              MenhirLib.EngineTypes.semv = x;
              MenhirLib.EngineTypes.startp = _startpos_x_;
              MenhirLib.EngineTypes.endp = _endpos_x_;
              MenhirLib.EngineTypes.next = _menhir_stack;
            };
          };
        } = _menhir_stack in
        let x_inlined1 : 'tv_int_expr = Obj.magic x_inlined1 in
        let _1 : unit = Obj.magic _1 in
        let x : 'tv_int_expr = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_inlined1_ in
        let _v : 'tv_int_expr = let e2 =
          let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2720 "frontend/parser.ml"
          
        in
        let o = 
# 170 "frontend/parser.mly"
                     ( AST_PLUS )
# 2726 "frontend/parser.ml"
         in
        let e1 =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2734 "frontend/parser.ml"
          
        in
        
# 139 "frontend/parser.mly"
    ( AST_int_binary (o,e1,e2) )
# 2740 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x_inlined1;
          MenhirLib.EngineTypes.startp = _startpos_x_inlined1_;
          MenhirLib.EngineTypes.endp = _endpos_x_inlined1_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _1;
            MenhirLib.EngineTypes.startp = _startpos__1_;
            MenhirLib.EngineTypes.endp = _endpos__1_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _menhir_s;
              MenhirLib.EngineTypes.semv = x;
              MenhirLib.EngineTypes.startp = _startpos_x_;
              MenhirLib.EngineTypes.endp = _endpos_x_;
              MenhirLib.EngineTypes.next = _menhir_stack;
            };
          };
        } = _menhir_stack in
        let x_inlined1 : 'tv_int_expr = Obj.magic x_inlined1 in
        let _1 : unit = Obj.magic _1 in
        let x : 'tv_int_expr = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_inlined1_ in
        let _v : 'tv_int_expr = let e2 =
          let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2783 "frontend/parser.ml"
          
        in
        let o = 
# 171 "frontend/parser.mly"
                     ( AST_MINUS )
# 2789 "frontend/parser.ml"
         in
        let e1 =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2797 "frontend/parser.ml"
          
        in
        
# 139 "frontend/parser.mly"
    ( AST_int_binary (o,e1,e2) )
# 2803 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = _6;
          MenhirLib.EngineTypes.startp = _startpos__6_;
          MenhirLib.EngineTypes.endp = _endpos__6_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = x_inlined1;
            MenhirLib.EngineTypes.startp = _startpos_x_inlined1_;
            MenhirLib.EngineTypes.endp = _endpos_x_inlined1_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _;
              MenhirLib.EngineTypes.semv = _4;
              MenhirLib.EngineTypes.startp = _startpos__4_;
              MenhirLib.EngineTypes.endp = _endpos__4_;
              MenhirLib.EngineTypes.next = {
                MenhirLib.EngineTypes.state = _;
                MenhirLib.EngineTypes.semv = x;
                MenhirLib.EngineTypes.startp = _startpos_x_;
                MenhirLib.EngineTypes.endp = _endpos_x_;
                MenhirLib.EngineTypes.next = {
                  MenhirLib.EngineTypes.state = _;
                  MenhirLib.EngineTypes.semv = _2;
                  MenhirLib.EngineTypes.startp = _startpos__2_;
                  MenhirLib.EngineTypes.endp = _endpos__2_;
                  MenhirLib.EngineTypes.next = {
                    MenhirLib.EngineTypes.state = _menhir_s;
                    MenhirLib.EngineTypes.semv = _1;
                    MenhirLib.EngineTypes.startp = _startpos__1_;
                    MenhirLib.EngineTypes.endp = _endpos__1_;
                    MenhirLib.EngineTypes.next = _menhir_stack;
                  };
                };
              };
            };
          };
        } = _menhir_stack in
        let _6 : unit = Obj.magic _6 in
        let x_inlined1 : 'tv_sign_int_literal = Obj.magic x_inlined1 in
        let _4 : unit = Obj.magic _4 in
        let x : 'tv_sign_int_literal = Obj.magic x in
        let _2 : unit = Obj.magic _2 in
        let _1 : unit = Obj.magic _1 in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__6_ in
        let _v : 'tv_int_expr = let e2 =
          let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2867 "frontend/parser.ml"
          
        in
        let e1 =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2876 "frontend/parser.ml"
          
        in
        
# 143 "frontend/parser.mly"
    ( AST_int_rand (e1, e2) )
# 2882 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = _4;
          MenhirLib.EngineTypes.startp = _startpos__4_;
          MenhirLib.EngineTypes.endp = _endpos__4_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = l;
            MenhirLib.EngineTypes.startp = _startpos_l_;
            MenhirLib.EngineTypes.endp = _endpos_l_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _;
              MenhirLib.EngineTypes.semv = _2;
              MenhirLib.EngineTypes.startp = _startpos__2_;
              MenhirLib.EngineTypes.endp = _endpos__2_;
              MenhirLib.EngineTypes.next = {
                MenhirLib.EngineTypes.state = _menhir_s;
                MenhirLib.EngineTypes.semv = x;
                MenhirLib.EngineTypes.startp = _startpos_x_;
                MenhirLib.EngineTypes.endp = _endpos_x_;
                MenhirLib.EngineTypes.next = _menhir_stack;
              };
            };
          };
        } = _menhir_stack in
        let _4 : unit = Obj.magic _4 in
        let l : 'tv_int_expr_list = Obj.magic l in
        let _2 : unit = Obj.magic _2 in
        let x : (
# 66 "frontend/parser.mly"
       (string)
# 2924 "frontend/parser.ml"
        ) = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos__4_ in
        let _v : 'tv_int_expr = let e =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2935 "frontend/parser.ml"
          
        in
        
# 146 "frontend/parser.mly"
    ( AST_expr_call (e, l) )
# 2941 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = xs;
          MenhirLib.EngineTypes.startp = _startpos_xs_;
          MenhirLib.EngineTypes.endp = _endpos_xs_;
          MenhirLib.EngineTypes.next = _menhir_stack;
        } = _menhir_stack in
        let xs : 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_int_expr___ = Obj.magic xs in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_xs_ in
        let _endpos = _endpos_xs_ in
        let _v : 'tv_int_expr_list = let l = 
# 232 "<standard.mly>"
    ( xs )
# 2966 "frontend/parser.ml"
         in
        
# 150 "frontend/parser.mly"
                                               ( l )
# 2971 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let _menhir_s = _menhir_env.MenhirLib.EngineTypes.current in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _endpos = _startpos in
        let _v : 'tv_list_ext_stat__ = 
# 211 "<standard.mly>"
    ( [] )
# 2989 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = xs;
          MenhirLib.EngineTypes.startp = _startpos_xs_;
          MenhirLib.EngineTypes.endp = _endpos_xs_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _menhir_s;
            MenhirLib.EngineTypes.semv = x;
            MenhirLib.EngineTypes.startp = _startpos_x_;
            MenhirLib.EngineTypes.endp = _endpos_x_;
            MenhirLib.EngineTypes.next = _menhir_stack;
          };
        } = _menhir_stack in
        let xs : 'tv_list_ext_stat__ = Obj.magic xs in
        let x : 'tv_stat = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_xs_ in
        let _v : 'tv_list_ext_stat__ = let x =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 3024 "frontend/parser.ml"
          
        in
        
# 213 "<standard.mly>"
    ( x :: xs )
# 3030 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let _menhir_s = _menhir_env.MenhirLib.EngineTypes.current in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _endpos = _startpos in
        let _v : 'tv_list_toplevel_ = 
# 211 "<standard.mly>"
    ( [] )
# 3048 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = xs;
          MenhirLib.EngineTypes.startp = _startpos_xs_;
          MenhirLib.EngineTypes.endp = _endpos_xs_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _menhir_s;
            MenhirLib.EngineTypes.semv = x;
            MenhirLib.EngineTypes.startp = _startpos_x_;
            MenhirLib.EngineTypes.endp = _endpos_x_;
            MenhirLib.EngineTypes.next = _menhir_stack;
          };
        } = _menhir_stack in
        let xs : 'tv_list_toplevel_ = Obj.magic xs in
        let x : 'tv_toplevel = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_xs_ in
        let _v : 'tv_list_toplevel_ = 
# 213 "<standard.mly>"
    ( x :: xs )
# 3080 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let _menhir_s = _menhir_env.MenhirLib.EngineTypes.current in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _endpos = _startpos in
        let _v : 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_assign___ = 
# 142 "<standard.mly>"
    ( [] )
# 3098 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = x;
          MenhirLib.EngineTypes.startp = _startpos_x_;
          MenhirLib.EngineTypes.endp = _endpos_x_;
          MenhirLib.EngineTypes.next = _menhir_stack;
        } = _menhir_stack in
        let x : 'tv_separated_nonempty_list_TOK_COMMA_ext_assign__ = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_ in
        let _v : 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_assign___ = 
# 144 "<standard.mly>"
    ( x )
# 3123 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let _menhir_s = _menhir_env.MenhirLib.EngineTypes.current in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _endpos = _startpos in
        let _v : 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_int_expr___ = 
# 142 "<standard.mly>"
    ( [] )
# 3141 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = x;
          MenhirLib.EngineTypes.startp = _startpos_x_;
          MenhirLib.EngineTypes.endp = _endpos_x_;
          MenhirLib.EngineTypes.next = _menhir_stack;
        } = _menhir_stack in
        let x : 'tv_separated_nonempty_list_TOK_COMMA_ext_int_expr__ = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_ in
        let _v : 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_int_expr___ = 
# 144 "<standard.mly>"
    ( x )
# 3166 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let _menhir_s = _menhir_env.MenhirLib.EngineTypes.current in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _endpos = _startpos in
        let _v : 'tv_loption_separated_nonempty_list_TOK_COMMA_init_declarator__ = 
# 142 "<standard.mly>"
    ( [] )
# 3184 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = x;
          MenhirLib.EngineTypes.startp = _startpos_x_;
          MenhirLib.EngineTypes.endp = _endpos_x_;
          MenhirLib.EngineTypes.next = _menhir_stack;
        } = _menhir_stack in
        let x : 'tv_separated_nonempty_list_TOK_COMMA_init_declarator_ = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_ in
        let _v : 'tv_loption_separated_nonempty_list_TOK_COMMA_init_declarator__ = 
# 144 "<standard.mly>"
    ( x )
# 3209 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let _menhir_s = _menhir_env.MenhirLib.EngineTypes.current in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _endpos = _startpos in
        let _v : 'tv_loption_separated_nonempty_list_TOK_COMMA_param_decl__ = 
# 142 "<standard.mly>"
    ( [] )
# 3227 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = x;
          MenhirLib.EngineTypes.startp = _startpos_x_;
          MenhirLib.EngineTypes.endp = _endpos_x_;
          MenhirLib.EngineTypes.next = _menhir_stack;
        } = _menhir_stack in
        let x : 'tv_separated_nonempty_list_TOK_COMMA_param_decl_ = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_ in
        let _v : 'tv_loption_separated_nonempty_list_TOK_COMMA_param_decl__ = 
# 144 "<standard.mly>"
    ( x )
# 3252 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let _menhir_s = _menhir_env.MenhirLib.EngineTypes.current in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _endpos = _startpos in
        let _v : 'tv_option_ext_bool_expr__ = 
# 114 "<standard.mly>"
    ( None )
# 3270 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = x;
          MenhirLib.EngineTypes.startp = _startpos_x_;
          MenhirLib.EngineTypes.endp = _endpos_x_;
          MenhirLib.EngineTypes.next = _menhir_stack;
        } = _menhir_stack in
        let x : 'tv_bool_expr = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_ in
        let _v : 'tv_option_ext_bool_expr__ = let x =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 3298 "frontend/parser.ml"
          
        in
        
# 116 "<standard.mly>"
    ( Some x )
# 3304 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let _menhir_s = _menhir_env.MenhirLib.EngineTypes.current in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _endpos = _startpos in
        let _v : 'tv_option_ext_int_expr__ = 
# 114 "<standard.mly>"
    ( None )
# 3322 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = x;
          MenhirLib.EngineTypes.startp = _startpos_x_;
          MenhirLib.EngineTypes.endp = _endpos_x_;
          MenhirLib.EngineTypes.next = _menhir_stack;
        } = _menhir_stack in
        let x : 'tv_int_expr = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_ in
        let _v : 'tv_option_ext_int_expr__ = let x =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 3350 "frontend/parser.ml"
          
        in
        
# 116 "<standard.mly>"
    ( Some x )
# 3356 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x_inlined1;
          MenhirLib.EngineTypes.startp = _startpos_x_inlined1_;
          MenhirLib.EngineTypes.endp = _endpos_x_inlined1_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _menhir_s;
            MenhirLib.EngineTypes.semv = x;
            MenhirLib.EngineTypes.startp = _startpos_x_;
            MenhirLib.EngineTypes.endp = _endpos_x_;
            MenhirLib.EngineTypes.next = _menhir_stack;
          };
        } = _menhir_stack in
        let x_inlined1 : (
# 66 "frontend/parser.mly"
       (string)
# 3383 "frontend/parser.ml"
        ) = Obj.magic x_inlined1 in
        let x : 'tv_typ = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_inlined1_ in
        let _v : 'tv_param_decl = let v =
          let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 3396 "frontend/parser.ml"
          
        in
        let s =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 3405 "frontend/parser.ml"
          
        in
        
# 217 "frontend/parser.mly"
                           ( s, v )
# 3411 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = x;
          MenhirLib.EngineTypes.startp = _startpos_x_;
          MenhirLib.EngineTypes.endp = _endpos_x_;
          MenhirLib.EngineTypes.next = _menhir_stack;
        } = _menhir_stack in
        let x : 'tv_assign = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_ in
        let _v : 'tv_separated_nonempty_list_TOK_COMMA_ext_assign__ = let x =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 3439 "frontend/parser.ml"
          
        in
        
# 241 "<standard.mly>"
    ( [ x ] )
# 3445 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = xs;
          MenhirLib.EngineTypes.startp = _startpos_xs_;
          MenhirLib.EngineTypes.endp = _endpos_xs_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _2;
            MenhirLib.EngineTypes.startp = _startpos__2_;
            MenhirLib.EngineTypes.endp = _endpos__2_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _menhir_s;
              MenhirLib.EngineTypes.semv = x;
              MenhirLib.EngineTypes.startp = _startpos_x_;
              MenhirLib.EngineTypes.endp = _endpos_x_;
              MenhirLib.EngineTypes.next = _menhir_stack;
            };
          };
        } = _menhir_stack in
        let xs : 'tv_separated_nonempty_list_TOK_COMMA_ext_assign__ = Obj.magic xs in
        let _2 : unit = Obj.magic _2 in
        let x : 'tv_assign = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_xs_ in
        let _v : 'tv_separated_nonempty_list_TOK_COMMA_ext_assign__ = let x =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 3487 "frontend/parser.ml"
          
        in
        
# 243 "<standard.mly>"
    ( x :: xs )
# 3493 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = x;
          MenhirLib.EngineTypes.startp = _startpos_x_;
          MenhirLib.EngineTypes.endp = _endpos_x_;
          MenhirLib.EngineTypes.next = _menhir_stack;
        } = _menhir_stack in
        let x : 'tv_int_expr = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_ in
        let _v : 'tv_separated_nonempty_list_TOK_COMMA_ext_int_expr__ = let x =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 3521 "frontend/parser.ml"
          
        in
        
# 241 "<standard.mly>"
    ( [ x ] )
# 3527 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = xs;
          MenhirLib.EngineTypes.startp = _startpos_xs_;
          MenhirLib.EngineTypes.endp = _endpos_xs_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _2;
            MenhirLib.EngineTypes.startp = _startpos__2_;
            MenhirLib.EngineTypes.endp = _endpos__2_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _menhir_s;
              MenhirLib.EngineTypes.semv = x;
              MenhirLib.EngineTypes.startp = _startpos_x_;
              MenhirLib.EngineTypes.endp = _endpos_x_;
              MenhirLib.EngineTypes.next = _menhir_stack;
            };
          };
        } = _menhir_stack in
        let xs : 'tv_separated_nonempty_list_TOK_COMMA_ext_int_expr__ = Obj.magic xs in
        let _2 : unit = Obj.magic _2 in
        let x : 'tv_int_expr = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_xs_ in
        let _v : 'tv_separated_nonempty_list_TOK_COMMA_ext_int_expr__ = let x =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 3569 "frontend/parser.ml"
          
        in
        
# 243 "<standard.mly>"
    ( x :: xs )
# 3575 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = x;
          MenhirLib.EngineTypes.startp = _startpos_x_;
          MenhirLib.EngineTypes.endp = _endpos_x_;
          MenhirLib.EngineTypes.next = _menhir_stack;
        } = _menhir_stack in
        let x : 'tv_init_declarator = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_ in
        let _v : 'tv_separated_nonempty_list_TOK_COMMA_init_declarator_ = 
# 241 "<standard.mly>"
    ( [ x ] )
# 3600 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = xs;
          MenhirLib.EngineTypes.startp = _startpos_xs_;
          MenhirLib.EngineTypes.endp = _endpos_xs_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _2;
            MenhirLib.EngineTypes.startp = _startpos__2_;
            MenhirLib.EngineTypes.endp = _endpos__2_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _menhir_s;
              MenhirLib.EngineTypes.semv = x;
              MenhirLib.EngineTypes.startp = _startpos_x_;
              MenhirLib.EngineTypes.endp = _endpos_x_;
              MenhirLib.EngineTypes.next = _menhir_stack;
            };
          };
        } = _menhir_stack in
        let xs : 'tv_separated_nonempty_list_TOK_COMMA_init_declarator_ = Obj.magic xs in
        let _2 : unit = Obj.magic _2 in
        let x : 'tv_init_declarator = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_xs_ in
        let _v : 'tv_separated_nonempty_list_TOK_COMMA_init_declarator_ = 
# 243 "<standard.mly>"
    ( x :: xs )
# 3639 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = x;
          MenhirLib.EngineTypes.startp = _startpos_x_;
          MenhirLib.EngineTypes.endp = _endpos_x_;
          MenhirLib.EngineTypes.next = _menhir_stack;
        } = _menhir_stack in
        let x : 'tv_param_decl = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_ in
        let _v : 'tv_separated_nonempty_list_TOK_COMMA_param_decl_ = 
# 241 "<standard.mly>"
    ( [ x ] )
# 3664 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = xs;
          MenhirLib.EngineTypes.startp = _startpos_xs_;
          MenhirLib.EngineTypes.endp = _endpos_xs_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _2;
            MenhirLib.EngineTypes.startp = _startpos__2_;
            MenhirLib.EngineTypes.endp = _endpos__2_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _menhir_s;
              MenhirLib.EngineTypes.semv = x;
              MenhirLib.EngineTypes.startp = _startpos_x_;
              MenhirLib.EngineTypes.endp = _endpos_x_;
              MenhirLib.EngineTypes.next = _menhir_stack;
            };
          };
        } = _menhir_stack in
        let xs : 'tv_separated_nonempty_list_TOK_COMMA_param_decl_ = Obj.magic xs in
        let _2 : unit = Obj.magic _2 in
        let x : 'tv_param_decl = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_xs_ in
        let _v : 'tv_separated_nonempty_list_TOK_COMMA_param_decl_ = 
# 243 "<standard.mly>"
    ( x :: xs )
# 3703 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = i;
          MenhirLib.EngineTypes.startp = _startpos_i_;
          MenhirLib.EngineTypes.endp = _endpos_i_;
          MenhirLib.EngineTypes.next = _menhir_stack;
        } = _menhir_stack in
        let i : (
# 67 "frontend/parser.mly"
       (string)
# 3724 "frontend/parser.ml"
        ) = Obj.magic i in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_i_ in
        let _endpos = _endpos_i_ in
        let _v : 'tv_sign_int_literal = 
# 155 "frontend/parser.mly"
                       ( i )
# 3732 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = i;
          MenhirLib.EngineTypes.startp = _startpos_i_;
          MenhirLib.EngineTypes.endp = _endpos_i_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _menhir_s;
            MenhirLib.EngineTypes.semv = _1;
            MenhirLib.EngineTypes.startp = _startpos__1_;
            MenhirLib.EngineTypes.endp = _endpos__1_;
            MenhirLib.EngineTypes.next = _menhir_stack;
          };
        } = _menhir_stack in
        let i : (
# 67 "frontend/parser.mly"
       (string)
# 3759 "frontend/parser.ml"
        ) = Obj.magic i in
        let _1 : unit = Obj.magic _1 in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_i_ in
        let _v : 'tv_sign_int_literal = 
# 156 "frontend/parser.mly"
                       ( i )
# 3768 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = i;
          MenhirLib.EngineTypes.startp = _startpos_i_;
          MenhirLib.EngineTypes.endp = _endpos_i_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _menhir_s;
            MenhirLib.EngineTypes.semv = _1;
            MenhirLib.EngineTypes.startp = _startpos__1_;
            MenhirLib.EngineTypes.endp = _endpos__1_;
            MenhirLib.EngineTypes.next = _menhir_stack;
          };
        } = _menhir_stack in
        let i : (
# 67 "frontend/parser.mly"
       (string)
# 3795 "frontend/parser.ml"
        ) = Obj.magic i in
        let _1 : unit = Obj.magic _1 in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_i_ in
        let _v : 'tv_sign_int_literal = 
# 157 "frontend/parser.mly"
                       ( "-"^i )
# 3804 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = s;
          MenhirLib.EngineTypes.startp = _startpos_s_;
          MenhirLib.EngineTypes.endp = _endpos_s_;
          MenhirLib.EngineTypes.next = _menhir_stack;
        } = _menhir_stack in
        let s : 'tv_common_stat = Obj.magic s in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_s_ in
        let _endpos = _endpos_s_ in
        let _v : 'tv_stat = 
# 269 "frontend/parser.mly"
                ( s )
# 3829 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x_inlined1;
          MenhirLib.EngineTypes.startp = _startpos_x_inlined1_;
          MenhirLib.EngineTypes.endp = _endpos_x_inlined1_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _4;
            MenhirLib.EngineTypes.startp = _startpos__4_;
            MenhirLib.EngineTypes.endp = _endpos__4_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _;
              MenhirLib.EngineTypes.semv = x;
              MenhirLib.EngineTypes.startp = _startpos_x_;
              MenhirLib.EngineTypes.endp = _endpos_x_;
              MenhirLib.EngineTypes.next = {
                MenhirLib.EngineTypes.state = _;
                MenhirLib.EngineTypes.semv = _2;
                MenhirLib.EngineTypes.startp = _startpos__2_;
                MenhirLib.EngineTypes.endp = _endpos__2_;
                MenhirLib.EngineTypes.next = {
                  MenhirLib.EngineTypes.state = _menhir_s;
                  MenhirLib.EngineTypes.semv = _1;
                  MenhirLib.EngineTypes.startp = _startpos__1_;
                  MenhirLib.EngineTypes.endp = _endpos__1_;
                  MenhirLib.EngineTypes.next = _menhir_stack;
                };
              };
            };
          };
        } = _menhir_stack in
        let x_inlined1 : 'tv_stat = Obj.magic x_inlined1 in
        let _4 : unit = Obj.magic _4 in
        let x : 'tv_bool_expr = Obj.magic x in
        let _2 : unit = Obj.magic _2 in
        let _1 : unit = Obj.magic _1 in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_x_inlined1_ in
        let _v : 'tv_stat = let s =
          let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 3886 "frontend/parser.ml"
          
        in
        let e =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 3895 "frontend/parser.ml"
          
        in
        
# 270 "frontend/parser.mly"
                                                            ( AST_if (e, s, None) )
# 3901 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x_inlined2;
          MenhirLib.EngineTypes.startp = _startpos_x_inlined2_;
          MenhirLib.EngineTypes.endp = _endpos_x_inlined2_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _6;
            MenhirLib.EngineTypes.startp = _startpos__6_;
            MenhirLib.EngineTypes.endp = _endpos__6_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _;
              MenhirLib.EngineTypes.semv = x_inlined1;
              MenhirLib.EngineTypes.startp = _startpos_x_inlined1_;
              MenhirLib.EngineTypes.endp = _endpos_x_inlined1_;
              MenhirLib.EngineTypes.next = {
                MenhirLib.EngineTypes.state = _;
                MenhirLib.EngineTypes.semv = _4;
                MenhirLib.EngineTypes.startp = _startpos__4_;
                MenhirLib.EngineTypes.endp = _endpos__4_;
                MenhirLib.EngineTypes.next = {
                  MenhirLib.EngineTypes.state = _;
                  MenhirLib.EngineTypes.semv = x;
                  MenhirLib.EngineTypes.startp = _startpos_x_;
                  MenhirLib.EngineTypes.endp = _endpos_x_;
                  MenhirLib.EngineTypes.next = {
                    MenhirLib.EngineTypes.state = _;
                    MenhirLib.EngineTypes.semv = _2;
                    MenhirLib.EngineTypes.startp = _startpos__2_;
                    MenhirLib.EngineTypes.endp = _endpos__2_;
                    MenhirLib.EngineTypes.next = {
                      MenhirLib.EngineTypes.state = _menhir_s;
                      MenhirLib.EngineTypes.semv = _1;
                      MenhirLib.EngineTypes.startp = _startpos__1_;
                      MenhirLib.EngineTypes.endp = _endpos__1_;
                      MenhirLib.EngineTypes.next = _menhir_stack;
                    };
                  };
                };
              };
            };
          };
        } = _menhir_stack in
        let x_inlined2 : 'tv_stat = Obj.magic x_inlined2 in
        let _6 : unit = Obj.magic _6 in
        let x_inlined1 : 'tv_stat_with_else = Obj.magic x_inlined1 in
        let _4 : unit = Obj.magic _4 in
        let x : 'tv_bool_expr = Obj.magic x in
        let _2 : unit = Obj.magic _2 in
        let _1 : unit = Obj.magic _1 in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_x_inlined2_ in
        let _v : 'tv_stat = let t =
          let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined2_, _startpos_x_inlined2_, x_inlined2) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 3972 "frontend/parser.ml"
          
        in
        let s =
          let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 3982 "frontend/parser.ml"
          
        in
        let e =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 3991 "frontend/parser.ml"
          
        in
        
# 271 "frontend/parser.mly"
                                                                                           ( AST_if (e, s, Some t) )
# 3997 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x_inlined1;
          MenhirLib.EngineTypes.startp = _startpos_x_inlined1_;
          MenhirLib.EngineTypes.endp = _endpos_x_inlined1_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _4;
            MenhirLib.EngineTypes.startp = _startpos__4_;
            MenhirLib.EngineTypes.endp = _endpos__4_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _;
              MenhirLib.EngineTypes.semv = x;
              MenhirLib.EngineTypes.startp = _startpos_x_;
              MenhirLib.EngineTypes.endp = _endpos_x_;
              MenhirLib.EngineTypes.next = {
                MenhirLib.EngineTypes.state = _;
                MenhirLib.EngineTypes.semv = _2;
                MenhirLib.EngineTypes.startp = _startpos__2_;
                MenhirLib.EngineTypes.endp = _endpos__2_;
                MenhirLib.EngineTypes.next = {
                  MenhirLib.EngineTypes.state = _menhir_s;
                  MenhirLib.EngineTypes.semv = _1;
                  MenhirLib.EngineTypes.startp = _startpos__1_;
                  MenhirLib.EngineTypes.endp = _endpos__1_;
                  MenhirLib.EngineTypes.next = _menhir_stack;
                };
              };
            };
          };
        } = _menhir_stack in
        let x_inlined1 : 'tv_stat = Obj.magic x_inlined1 in
        let _4 : unit = Obj.magic _4 in
        let x : 'tv_bool_expr = Obj.magic x in
        let _2 : unit = Obj.magic _2 in
        let _1 : unit = Obj.magic _1 in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_x_inlined1_ in
        let _v : 'tv_stat = let s =
          let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 4054 "frontend/parser.ml"
          
        in
        let e =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 4063 "frontend/parser.ml"
          
        in
        
# 272 "frontend/parser.mly"
                                                               ( AST_while (e, s) )
# 4069 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x;
          MenhirLib.EngineTypes.startp = _startpos_x_;
          MenhirLib.EngineTypes.endp = _endpos_x_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _8;
            MenhirLib.EngineTypes.startp = _startpos__8_;
            MenhirLib.EngineTypes.endp = _endpos__8_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _;
              MenhirLib.EngineTypes.semv = c;
              MenhirLib.EngineTypes.startp = _startpos_c_;
              MenhirLib.EngineTypes.endp = _endpos_c_;
              MenhirLib.EngineTypes.next = {
                MenhirLib.EngineTypes.state = _;
                MenhirLib.EngineTypes.semv = _6;
                MenhirLib.EngineTypes.startp = _startpos__6_;
                MenhirLib.EngineTypes.endp = _endpos__6_;
                MenhirLib.EngineTypes.next = {
                  MenhirLib.EngineTypes.state = _;
                  MenhirLib.EngineTypes.semv = b;
                  MenhirLib.EngineTypes.startp = _startpos_b_;
                  MenhirLib.EngineTypes.endp = _endpos_b_;
                  MenhirLib.EngineTypes.next = {
                    MenhirLib.EngineTypes.state = _;
                    MenhirLib.EngineTypes.semv = _4;
                    MenhirLib.EngineTypes.startp = _startpos__4_;
                    MenhirLib.EngineTypes.endp = _endpos__4_;
                    MenhirLib.EngineTypes.next = {
                      MenhirLib.EngineTypes.state = _;
                      MenhirLib.EngineTypes.semv = a;
                      MenhirLib.EngineTypes.startp = _startpos_a_;
                      MenhirLib.EngineTypes.endp = _endpos_a_;
                      MenhirLib.EngineTypes.next = {
                        MenhirLib.EngineTypes.state = _;
                        MenhirLib.EngineTypes.semv = _2;
                        MenhirLib.EngineTypes.startp = _startpos__2_;
                        MenhirLib.EngineTypes.endp = _endpos__2_;
                        MenhirLib.EngineTypes.next = {
                          MenhirLib.EngineTypes.state = _menhir_s;
                          MenhirLib.EngineTypes.semv = _1;
                          MenhirLib.EngineTypes.startp = _startpos__1_;
                          MenhirLib.EngineTypes.endp = _endpos__1_;
                          MenhirLib.EngineTypes.next = _menhir_stack;
                        };
                      };
                    };
                  };
                };
              };
            };
          };
        } = _menhir_stack in
        let x : 'tv_stat = Obj.magic x in
        let _8 : unit = Obj.magic _8 in
        let c : 'tv_assign_list = Obj.magic c in
        let _6 : unit = Obj.magic _6 in
        let b : 'tv_option_ext_bool_expr__ = Obj.magic b in
        let _4 : unit = Obj.magic _4 in
        let a : 'tv_assign_list = Obj.magic a in
        let _2 : unit = Obj.magic _2 in
        let _1 : unit = Obj.magic _1 in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_x_ in
        let _v : 'tv_stat = let s =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 4153 "frontend/parser.ml"
          
        in
        
# 273 "frontend/parser.mly"
                                                                                                                             ( AST_for (a,b,c,s) )
# 4159 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = s;
          MenhirLib.EngineTypes.startp = _startpos_s_;
          MenhirLib.EngineTypes.endp = _endpos_s_;
          MenhirLib.EngineTypes.next = _menhir_stack;
        } = _menhir_stack in
        let s : 'tv_common_stat = Obj.magic s in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_s_ in
        let _endpos = _endpos_s_ in
        let _v : 'tv_stat_with_else = 
# 263 "frontend/parser.mly"
                ( s )
# 4184 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x_inlined2;
          MenhirLib.EngineTypes.startp = _startpos_x_inlined2_;
          MenhirLib.EngineTypes.endp = _endpos_x_inlined2_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _6;
            MenhirLib.EngineTypes.startp = _startpos__6_;
            MenhirLib.EngineTypes.endp = _endpos__6_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _;
              MenhirLib.EngineTypes.semv = x_inlined1;
              MenhirLib.EngineTypes.startp = _startpos_x_inlined1_;
              MenhirLib.EngineTypes.endp = _endpos_x_inlined1_;
              MenhirLib.EngineTypes.next = {
                MenhirLib.EngineTypes.state = _;
                MenhirLib.EngineTypes.semv = _4;
                MenhirLib.EngineTypes.startp = _startpos__4_;
                MenhirLib.EngineTypes.endp = _endpos__4_;
                MenhirLib.EngineTypes.next = {
                  MenhirLib.EngineTypes.state = _;
                  MenhirLib.EngineTypes.semv = x;
                  MenhirLib.EngineTypes.startp = _startpos_x_;
                  MenhirLib.EngineTypes.endp = _endpos_x_;
                  MenhirLib.EngineTypes.next = {
                    MenhirLib.EngineTypes.state = _;
                    MenhirLib.EngineTypes.semv = _2;
                    MenhirLib.EngineTypes.startp = _startpos__2_;
                    MenhirLib.EngineTypes.endp = _endpos__2_;
                    MenhirLib.EngineTypes.next = {
                      MenhirLib.EngineTypes.state = _menhir_s;
                      MenhirLib.EngineTypes.semv = _1;
                      MenhirLib.EngineTypes.startp = _startpos__1_;
                      MenhirLib.EngineTypes.endp = _endpos__1_;
                      MenhirLib.EngineTypes.next = _menhir_stack;
                    };
                  };
                };
              };
            };
          };
        } = _menhir_stack in
        let x_inlined2 : 'tv_stat_with_else = Obj.magic x_inlined2 in
        let _6 : unit = Obj.magic _6 in
        let x_inlined1 : 'tv_stat_with_else = Obj.magic x_inlined1 in
        let _4 : unit = Obj.magic _4 in
        let x : 'tv_bool_expr = Obj.magic x in
        let _2 : unit = Obj.magic _2 in
        let _1 : unit = Obj.magic _1 in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_x_inlined2_ in
        let _v : 'tv_stat_with_else = let t =
          let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined2_, _startpos_x_inlined2_, x_inlined2) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 4255 "frontend/parser.ml"
          
        in
        let s =
          let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 4265 "frontend/parser.ml"
          
        in
        let e =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 4274 "frontend/parser.ml"
          
        in
        
# 264 "frontend/parser.mly"
                                                                                                     ( AST_if (e, s, Some t) )
# 4280 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x_inlined1;
          MenhirLib.EngineTypes.startp = _startpos_x_inlined1_;
          MenhirLib.EngineTypes.endp = _endpos_x_inlined1_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _4;
            MenhirLib.EngineTypes.startp = _startpos__4_;
            MenhirLib.EngineTypes.endp = _endpos__4_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _;
              MenhirLib.EngineTypes.semv = x;
              MenhirLib.EngineTypes.startp = _startpos_x_;
              MenhirLib.EngineTypes.endp = _endpos_x_;
              MenhirLib.EngineTypes.next = {
                MenhirLib.EngineTypes.state = _;
                MenhirLib.EngineTypes.semv = _2;
                MenhirLib.EngineTypes.startp = _startpos__2_;
                MenhirLib.EngineTypes.endp = _endpos__2_;
                MenhirLib.EngineTypes.next = {
                  MenhirLib.EngineTypes.state = _menhir_s;
                  MenhirLib.EngineTypes.semv = _1;
                  MenhirLib.EngineTypes.startp = _startpos__1_;
                  MenhirLib.EngineTypes.endp = _endpos__1_;
                  MenhirLib.EngineTypes.next = _menhir_stack;
                };
              };
            };
          };
        } = _menhir_stack in
        let x_inlined1 : 'tv_stat_with_else = Obj.magic x_inlined1 in
        let _4 : unit = Obj.magic _4 in
        let x : 'tv_bool_expr = Obj.magic x in
        let _2 : unit = Obj.magic _2 in
        let _1 : unit = Obj.magic _1 in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_x_inlined1_ in
        let _v : 'tv_stat_with_else = let s =
          let (_endpos_x_, _startpos_x_, x) = (_endpos_x_inlined1_, _startpos_x_inlined1_, x_inlined1) in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 4337 "frontend/parser.ml"
          
        in
        let e =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 4346 "frontend/parser.ml"
          
        in
        
# 265 "frontend/parser.mly"
                                                                         ( AST_while (e, s) )
# 4352 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = x;
          MenhirLib.EngineTypes.startp = _startpos_x_;
          MenhirLib.EngineTypes.endp = _endpos_x_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = _8;
            MenhirLib.EngineTypes.startp = _startpos__8_;
            MenhirLib.EngineTypes.endp = _endpos__8_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _;
              MenhirLib.EngineTypes.semv = c;
              MenhirLib.EngineTypes.startp = _startpos_c_;
              MenhirLib.EngineTypes.endp = _endpos_c_;
              MenhirLib.EngineTypes.next = {
                MenhirLib.EngineTypes.state = _;
                MenhirLib.EngineTypes.semv = _6;
                MenhirLib.EngineTypes.startp = _startpos__6_;
                MenhirLib.EngineTypes.endp = _endpos__6_;
                MenhirLib.EngineTypes.next = {
                  MenhirLib.EngineTypes.state = _;
                  MenhirLib.EngineTypes.semv = b;
                  MenhirLib.EngineTypes.startp = _startpos_b_;
                  MenhirLib.EngineTypes.endp = _endpos_b_;
                  MenhirLib.EngineTypes.next = {
                    MenhirLib.EngineTypes.state = _;
                    MenhirLib.EngineTypes.semv = _4;
                    MenhirLib.EngineTypes.startp = _startpos__4_;
                    MenhirLib.EngineTypes.endp = _endpos__4_;
                    MenhirLib.EngineTypes.next = {
                      MenhirLib.EngineTypes.state = _;
                      MenhirLib.EngineTypes.semv = a;
                      MenhirLib.EngineTypes.startp = _startpos_a_;
                      MenhirLib.EngineTypes.endp = _endpos_a_;
                      MenhirLib.EngineTypes.next = {
                        MenhirLib.EngineTypes.state = _;
                        MenhirLib.EngineTypes.semv = _2;
                        MenhirLib.EngineTypes.startp = _startpos__2_;
                        MenhirLib.EngineTypes.endp = _endpos__2_;
                        MenhirLib.EngineTypes.next = {
                          MenhirLib.EngineTypes.state = _menhir_s;
                          MenhirLib.EngineTypes.semv = _1;
                          MenhirLib.EngineTypes.startp = _startpos__1_;
                          MenhirLib.EngineTypes.endp = _endpos__1_;
                          MenhirLib.EngineTypes.next = _menhir_stack;
                        };
                      };
                    };
                  };
                };
              };
            };
          };
        } = _menhir_stack in
        let x : 'tv_stat_with_else = Obj.magic x in
        let _8 : unit = Obj.magic _8 in
        let c : 'tv_assign_list = Obj.magic c in
        let _6 : unit = Obj.magic _6 in
        let b : 'tv_option_ext_bool_expr__ = Obj.magic b in
        let _4 : unit = Obj.magic _4 in
        let a : 'tv_assign_list = Obj.magic a in
        let _2 : unit = Obj.magic _2 in
        let _1 : unit = Obj.magic _1 in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_x_ in
        let _v : 'tv_stat_with_else = let s =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 4436 "frontend/parser.ml"
          
        in
        
# 266 "frontend/parser.mly"
                                                                                                                                       ( AST_for (a,b,c,s) )
# 4442 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = x;
          MenhirLib.EngineTypes.startp = _startpos_x_;
          MenhirLib.EngineTypes.endp = _endpos_x_;
          MenhirLib.EngineTypes.next = _menhir_stack;
        } = _menhir_stack in
        let x : 'tv_var_decl = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_ in
        let _v : 'tv_toplevel = let d =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 4470 "frontend/parser.ml"
          
        in
        
# 94 "frontend/parser.mly"
                            ( AST_global_decl d )
# 4476 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = x;
          MenhirLib.EngineTypes.startp = _startpos_x_;
          MenhirLib.EngineTypes.endp = _endpos_x_;
          MenhirLib.EngineTypes.next = _menhir_stack;
        } = _menhir_stack in
        let x : 'tv_fun_decl = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_ in
        let _v : 'tv_toplevel = let d =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 4504 "frontend/parser.ml"
          
        in
        
# 95 "frontend/parser.mly"
                            ( AST_fun_decl d )
# 4510 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = _1;
          MenhirLib.EngineTypes.startp = _startpos__1_;
          MenhirLib.EngineTypes.endp = _endpos__1_;
          MenhirLib.EngineTypes.next = _menhir_stack;
        } = _menhir_stack in
        let _1 : unit = Obj.magic _1 in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__1_ in
        let _v : 'tv_typ = 
# 220 "frontend/parser.mly"
             ( AST_TYP_INT )
# 4535 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
      (fun _menhir_env ->
        let _menhir_stack = _menhir_env.MenhirLib.EngineTypes.stack in
        let {
          MenhirLib.EngineTypes.state = _;
          MenhirLib.EngineTypes.semv = _3;
          MenhirLib.EngineTypes.startp = _startpos__3_;
          MenhirLib.EngineTypes.endp = _endpos__3_;
          MenhirLib.EngineTypes.next = {
            MenhirLib.EngineTypes.state = _;
            MenhirLib.EngineTypes.semv = xs;
            MenhirLib.EngineTypes.startp = _startpos_xs_;
            MenhirLib.EngineTypes.endp = _endpos_xs_;
            MenhirLib.EngineTypes.next = {
              MenhirLib.EngineTypes.state = _menhir_s;
              MenhirLib.EngineTypes.semv = x;
              MenhirLib.EngineTypes.startp = _startpos_x_;
              MenhirLib.EngineTypes.endp = _endpos_x_;
              MenhirLib.EngineTypes.next = _menhir_stack;
            };
          };
        } = _menhir_stack in
        let _3 : unit = Obj.magic _3 in
        let xs : 'tv_loption_separated_nonempty_list_TOK_COMMA_init_declarator__ = Obj.magic xs in
        let x : 'tv_typ = Obj.magic x in
        let _endpos__0_ = _menhir_stack.MenhirLib.EngineTypes.endp in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos__3_ in
        let _v : 'tv_var_decl = let i = 
# 232 "<standard.mly>"
    ( xs )
# 4574 "frontend/parser.ml"
         in
        let s =
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 281 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 4582 "frontend/parser.ml"
          
        in
        
# 199 "frontend/parser.mly"
  ( s, i )
# 4588 "frontend/parser.ml"
         in
        {
          MenhirLib.EngineTypes.state = _menhir_s;
          MenhirLib.EngineTypes.semv = Obj.repr _v;
          MenhirLib.EngineTypes.startp = _startpos;
          MenhirLib.EngineTypes.endp = _endpos;
          MenhirLib.EngineTypes.next = _menhir_stack;
        });
    |]
  
  and trace =
    None
  
end

module MenhirInterpreter = struct
  
  module ET = MenhirLib.TableInterpreter.MakeEngineTable (Tables)
  
  module TI = MenhirLib.Engine.Make (ET)
  
  include TI
  
end

let file =
  fun lexer lexbuf ->
    (Obj.magic (MenhirInterpreter.entry `Legacy 0 lexer lexbuf) : (
# 82 "frontend/parser.mly"
      (Abstract_syntax_tree.toplevel list Abstract_syntax_tree.ext)
# 4619 "frontend/parser.ml"
    ))

module Incremental = struct
  
  let file =
    fun initial_position ->
      (Obj.magic (MenhirInterpreter.start 0 initial_position) : (
# 82 "frontend/parser.mly"
      (Abstract_syntax_tree.toplevel list Abstract_syntax_tree.ext)
# 4629 "frontend/parser.ml"
      ) MenhirInterpreter.checkpoint)
  
end

# 284 "frontend/parser.mly"
  

# 4637 "frontend/parser.ml"

# 269 "<standard.mly>"
  

# 4642 "frontend/parser.ml"
