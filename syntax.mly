%{

(* INTUITIONISTIC TYPE THEORY PROGRAMMING LANGUAGE                            *)
(*                                                                            *)
(* Copyright (c) 2006-2013 Johan G. Granstroem.                               *)
(*                                                                            *)
(* Licensed under the Apache License, Version 2.0 (the "License");            *)
(* you may not use this file except in compliance with the License.           *)
(* You may obtain a copy of the License at                                    *)
(*                                                                            *)
(*     http://www.apache.org/licenses/LICENSE-2.0                             *)
(*                                                                            *)
(* Unless required by applicable law or agreed to in writing, software        *)
(* distributed under the License is distributed on an "AS IS" BASIS,          *)
(* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.   *)
(* See the License for the specific language governing permissions and        *)
(* limitations under the License.                                             *)

open Base
open Expr

let pos_of_lexpos (p:Lexing.position) :Base.pos =
  (p.Lexing.pos_lnum, p.Lexing.pos_cnum - p.Lexing.pos_bol)

let filename () = (Parsing.symbol_start_pos ()).Lexing.pos_fname

let dummy_of_range range = Base.dummy_of_file_and_range (filename ()) range

let symbol_range () = (
  pos_of_lexpos (Parsing.symbol_start_pos ()),
  pos_of_lexpos (Parsing.symbol_end_pos ()))

let range (a:int) (b:int):range =
  (pos_of_lexpos (Parsing.rhs_start_pos a),
   pos_of_lexpos (Parsing.rhs_end_pos b))

let pos (a:int):range =
  (pos_of_lexpos (Parsing.rhs_start_pos a),
   pos_of_lexpos (Parsing.rhs_end_pos a))

let end_pos (a:int):range =
  (pos_of_lexpos (Parsing.rhs_end_pos a),
   pos_of_lexpos (Parsing.rhs_end_pos a))

let unit_lit_of_pos p =
  Decl(Enum_cst(p, unit_lit), Enum(p, unit_enum))

let mk_enum_and_dtor enum_range labels =
  let enum = Enum(enum_range, enum_make (List.map fst labels)) in
  let dtor = Enum_d(enum_range, labels) in
  enum, dtor

let mk_struct_or_union enum_range var_range labels =
  let enum, dtor = mk_enum_and_dtor enum_range labels in
  let v = dummy_of_range var_range in
  let vv = Var (var_range, v) in
  let ap = App(dtor, vv) in
  let patt = P_var(var_range, v) in
  enum, patt, ap

let mk_struct enum_range var_range labels =
  let enum, patt, ap = mk_struct_or_union enum_range var_range labels in
  Pi(enum, (patt, ap))

let mk_union enum_range var_range labels =
  let enum, patt, ap = mk_struct_or_union enum_range var_range labels in
  Sigma(enum, (patt, ap))

%}

%token EOF                 /* <end of file> */
%token <string> LITERAL    /* string literal */
%token <string> IDENT      /* identifier */
%token <Value.imm> IMM     /* numeric literal */
%token BLANK               /* _ */

/* Keyword tokens - parser name same as keyword, but in upper case. */
%token AEQ
%token ASSERT
%token BLOCK
%token CALL
%token CASE
%token COMPILE
%token DEP
%token DO
%token ELSE
%token ENUM
%token FOR
%token FST
%token FUN
%token GET
%token IF
%token IN
%token INTERPRET
%token IS
%token INTERFACE
%token METH
%token NEW
%token OPAQUE
%token PURIFY
%token REFL
%token SND
%token STRUCT
%token SUBST
%token SWITCH
%token TEST
%token TUPLE
%token TYPE
%token UNION
%token VAL
%token YIELD

/* Infix tokens - special */
%token AND_AND
%token AT

%token BANG
%token BANG_EQ
%token BAR_BAR

%token CARET_CARET
%token COLON
%token COLON_COLON
%token COLON_EQ
%token COMMA

%token DOT
%token DOT_DOT

%token EQ
%token EQ_EQ
%token EQ_EQ_EQ
%token EQ_GREATER

%token GREATER
%token GREATER_EQ

%token LESS
%token LESS_EQ

%token MINUS
%token MINUS_GREATER

%token PLUS
%token PLUS_PLUS

%token QUESTION
%token QUESTION_QUESTION
%token QUOTE

%token SEMI
%token STAR
%token STAR_STAR

%token TILDE

/* Delimiter tokens */
%token LBRACE
%token LBRACKET
%token LPAREN
%token RBRACE
%token RBRACKET
%token RPAREN

%start file
%type <Expr.toplevel> file

%start expr
%type <Expr.expr> expr

%%


file:
| { Eof }
| ASSERT expr IS expr SEMI file { Assert($2, $4, $6) }
| ASSERT expr EQ expr IS expr SEMI file { AssertEq($2, $4, $6, $8) }
| VAL variable EQ expr SEMI file { Val($2, $4, $6) }
| VAL variable expr EQ expr SEMI file { Val($2, Expr.Decl($5, $3), $7) }
| VAL FUN fun_arglist EQ expr SEMI file {
  let (f, _), (x, _A) = $3 in
  Val(f, Pattern(Some _A, (x, $5)), $7)
}
| VAL FUN fun_arglist expr EQ expr SEMI file {
  let (f, _), (x, _A) = $3 in
  Val(f, Pattern(Some _A, (x, Decl($6, $4))), $8)
}
| COMPILE variable LPAREN compile_arglist RPAREN expr EQ expr SEMI file {
  Compile($2, $4, $6, $8, $10)
}
| TEST variable LPAREN test_arglist RPAREN EQ expr SEMI file {
  Test($2, $4, $7, $9)
}
;

compile_arglist:
| variable expr2 { [$1, $2] }
| variable expr2 COMMA compile_arglist { ($1, $2) :: $4 }
;

test_arglist:
| expr2 { [$1] }
| expr2 COMMA test_arglist { $1 :: $3 }
;

fun_arglist:
| variable LPAREN arglist RPAREN { ($1, pos 1), $3 }
| prefix LPAREN binder expr2 RPAREN { (Variable $1, pos 1), ($3, $4) }
| LPAREN binder expr2 RPAREN infix LPAREN binder expr2 RPAREN {
  (Variable $5, pos 5), (P_tuple($2, $7, dummy_of_range (pos 4), false),
                         Sigma($3, ($2, $8)))
}
;

ident:
| IDENT { $1 }
| LPAREN infix RPAREN { $2 }
| LPAREN prefix DOT RPAREN { $2 }
;
enum_lit: ident { Enum_lit $1 };
variable: ident { Variable $1 };

binder:
| variable { P_var(pos 1, $1) }
| BLANK { P_blank(pos 1, dummy_of_range (pos 1)) }
;

binders:
| pattern { $1 }
| pattern COMMA binders { P_tuple($1, $3, dummy_of_range (pos 2), false) }
;

pattern:
| binder { $1 }
| LPAREN binders RPAREN { $2 }
;

arglist:
| binder expr2 { $1, $2 }
| binder expr2 COMMA arglist {
    let p2, t2 = $4 in
    P_tuple($1, p2, dummy_of_range (pos 3), false),
    Sigma($2, ($1, t2))
};

labels1:
| enum_lit COLON expr2 { [$1, $3] }
| enum_lit COLON expr2 COMMA labels1 { ($1, $3) :: $5 }
;

labels:
| { [] }
| labels1 { $1 }
;

bpattern:
| enum_lit AT COLON expr2 { ($1, $4) }
| enum_lit AT pattern COLON expr2 { ($1, Pattern(None, ($3, $5))) }
;

blabels:
| bpattern { [$1] }
| bpattern COMMA blabels { $1 :: $3 }
;

enum_labels1:
| enum_lit { [$1] }
| enum_lit COMMA enum_labels1 { $1 :: $3 }
;

enum_labels:
| { [] }
| enum_labels1 { $1 }
;

cases:
| { [] }
| CASE enum_lit COLON stmts cases { ($2, $4) :: $5 }
;

bcases:
| CASE enum_lit AT pattern COLON stmts {
  [$2, Pattern(None, ($4, $6))]
}
| CASE enum_lit AT pattern COLON stmts bcases{
  ($2, Pattern(None, ($4, $6))) :: $7
}
;

estmt:
| DO expr { $2 }
| GET ident {
  Call(range 1 2, Pair(Enum_cst(pos 2, Enum_lit $2),
                       Pattern(None, (P_var(pos 2, Variable $2),
                                      Var(pos 2, Variable $2)))))
}
;

cstmt:
| IF expr LBRACE stmts RBRACE {
  Switch(range 1 5, $2,
         [bool_true_lit, $4;
	  bool_false_lit, Ret(pos 5, unit_lit_of_pos (pos 5))])
}
| IF expr LBRACE stmts RBRACE ELSE LBRACE stmts RBRACE {
  Switch(range 1 9, $2, [bool_true_lit, $4; bool_false_lit, $8])
}
| FOR pattern IN expr LBRACE stmts RBRACE { For($4, ($2, $6)) }
| SWITCH expr LBRACE cases RBRACE { Switch(range 1 5, $2, $4) }
| SWITCH expr LBRACE bcases RBRACE { Switch2(range 1 5, $2, $4) }
;

stmt:
| cstmt { $1 }
| estmt SEMI { $1 }
;

opaque_opt:
| { true }
| OPAQUE { false }
;

vstmt:
| VAL pattern EQ stmt {
  fun x -> Bind($4, None, ($2, x))
}
| VAL pattern expr EQ stmt {
  fun x -> Bind($5, Some $3, ($2, x))
}
| VAL pattern EQ opaque_opt expr SEMI {
  fun x -> Let($4, $5, ($2, x))
}
| VAL pattern expr EQ opaque_opt expr SEMI {
  fun x -> Let($5, Decl($6, $3), ($2, x))
}
| VAL LPAREN arglist RPAREN EQ opaque_opt expr SEMI {
  fun x -> Let($6, Decl($7, snd $3), (fst $3, x))
}
| VAL FUN fun_arglist EQ opaque_opt expr SEMI {
  let (f, frange), (x, _A) = $3 in
  fun y -> Let($5, Pattern(Some _A, (x, $6)), (P_var(frange, f), y))
}
| VAL FUN fun_arglist expr EQ opaque_opt expr SEMI {
  let (f, frange), (x, _A) = $3 in
  fun y -> Let($6, Pattern(Some _A, (x, Decl($7, $4))), (P_var(frange, f), y))
}
;

stmts:
| { let r = symbol_range () in Ret(r, unit_lit_of_pos r) }
| stmt stmts {
  let p = end_pos 1 in
  Bind($1, Some(Enum(p, unit_enum)), (P_blank(p, dummy_of_range p), $2))
}
| YIELD LPAREN expr RPAREN SEMI { Ret(range 1 5, $3) }
| YIELD LPAREN estmt RPAREN SEMI { $3 }
| YIELD LPAREN cstmt RPAREN SEMI { $3 }
| NEW enum_lit EQ expr SEMI stmts {
  New(range 1 6, $2, pos 2, $4, $6)
}
| vstmt stmts { $1($2) }
| ident COLON_EQ expr SEMI stmts {
  let a = Call(range 1 3, Pair(Enum_cst(pos 1, Enum_lit $1),
                               Pattern(None, (P_var(pos 1, Variable $1), $3))))
  in
  let p = pos 4 in
  Bind(a, None, (P_blank(p, dummy_of_range p), $5))
}
;

cexpr:
| vstmt cexpr { $1($2) }
| expr { $1 }
;

prefix:
| BANG  { "(!.)" }
| TILDE { "(~.)" }
| MINUS { "(-.)" }
| STAR { "(*.)" }
;

gen_prefix:
| prefix { Var(pos 1, Variable $1) }
;

multiplication:
| STAR { "(*)" }
| STAR_STAR { "(**)" }
;

gen_multiplication:
| multiplication { Var(pos 1, Variable $1) }
;

addition:
| PLUS { "(+)" }
| PLUS_PLUS { "(++)" }
| MINUS { "(-)" }
;

gen_addition:
| addition { Var(pos 1, Variable $1) }
;

relation:
| EQ_EQ { "(==)" }
| EQ_EQ_EQ { "(===)" }
| BANG_EQ { "(!=)" }
| LESS { "(<)" }
| GREATER { "(>)" }
| LESS_EQ { "(<=)" }
| GREATER_EQ { "(>=)" }
;

gen_relation:
| relation { Var(pos 1, Variable $1) }
;

connective:
| AND_AND { "(&&)" }
| BAR_BAR { "(||)" }
| CARET_CARET { "(^^)" }
;

gen_connective:
| connective { Var(pos 1, Variable $1) }
;

infix:
| multiplication { $1 }
| addition { $1 }
| relation { $1 }
| connective { $1 }
;

expr10:
| IMM { Imm(pos 1, $1) }
| variable { Var(pos 1, $1) }
| QUOTE enum_lit { Enum_cst (range 1 2, $2) }
| REFL { Imm(pos 1, Value.Refl) }
| TYPE { Type(pos 1) }
| INTERFACE { Interface(range 1 2) }
| LPAREN RPAREN { unit_lit_of_pos (range 1 2) }
| FST LPAREN expr RPAREN { First (range 1 4, $3) }
| SND LPAREN expr RPAREN { Second (range 1 4, $3) }
| CALL LPAREN expr RPAREN { Call(range 1 4, $3) }
| CALL LPAREN RPAREN { Call(range 1 3, unit_lit_of_pos (range 2 3)) }
| expr10 LPAREN expr RPAREN { App($1, $3) }
| expr10 LPAREN RPAREN { App($1, unit_lit_of_pos (range 2 3)) }
| expr10 COLON_COLON enum_lit { App($1, Enum_cst(pos 3, $3)) }
| expr10 COLON_COLON infix { App($1, Enum_cst(pos 3, Enum_lit $3)) }
| ENUM LBRACE enum_labels RBRACE { Enum(range 1 4, enum_make $3) }
| STRUCT LBRACE labels RBRACE { mk_struct (pos 1) (pos 3) $3 }
| FUN LBRACE labels RBRACE { Enum_d(range 1 4, $3) }
| FUN LBRACE blabels RBRACE { Enum_d2(range 1 4, $3) }
| UNION LBRACE labels RBRACE { mk_union (pos 1) (pos 3) $3 }
| TUPLE LPAREN arglist RPAREN { snd $3 }
| METH LBRACE labels RBRACE { Complex_interface(range 1 4, $3) }
| INTERPRET expr LBRACE expr RBRACE { Interpret($2, $4) }
| BLOCK expr4 EQ_GREATER expr3 LBRACE stmts RBRACE { Decl($6, Tree($2, $4)) }
| BLOCK LBRACE stmts RBRACE { $3 }
| PURIFY expr LBRACE stmts RBRACE { Purify(range 1 5, $2, $4) }
| LPAREN cexpr RPAREN { $2 }
;

expr9:
| expr10 { $1 }
| enum_lit DOT expr9 { Dot(Enum_cst(pos 1, $1), $3) }
| enum_lit AT expr9 { Pair(Enum_cst(pos 1, $1), $3) }
;

expr8:
| expr9 { $1 }
| gen_prefix expr9 { App($1, $2) }
;

expr7:
| expr8 { $1 }
| expr7 gen_multiplication expr8 { App($2, Pair($1, $3)) }
;

expr6:
| expr7 { $1 }
| expr6 gen_addition expr7 { App($2, Pair($1, $3)) }
;

expr5:
| expr6 { $1 }
| expr6 gen_relation expr6 { App($2, Pair($1, $3)) }
| expr6 AEQ LPAREN expr2 RPAREN expr6 { Id(range 1 6, $4, $1, $6) }
;

expr4:
| expr5 { $1 }
| expr5 gen_connective expr5 { App($2, Pair($1, $3)) }
;

expr3:
| expr4 { $1 }
| expr4 DOT_DOT expr4 { Range($1, $3) }
| DEP LPAREN arglist RPAREN MINUS_GREATER expr3 {
  let x, _A = $3 in
  Pi(_A, (x, $6))
}
| expr4 MINUS_GREATER expr3 {
  Pi($1, (P_blank(pos 2, dummy_of_range (pos 2)), $3))
}
| expr4 EQ_GREATER expr3 { Tree($1, $3) }
| expr4 QUESTION expr4 COLON expr4 {
  Switch(range 1 5, $1, [bool_true_lit, $3; bool_false_lit, $5])
}
;

expr2:
| expr3 { $1 }
| METH LPAREN arglist RPAREN expr2 {
  let x, _A = $3 in
  let _B = Expr.Pattern(None, (x, $5)) in
  Expr.Decl(Expr.Pair(_A, _B), Expr.Interface (range 1 1))
}
| FUN LPAREN arglist RPAREN expr2 {
  let x, _A = $3 in
  Pattern(Some _A, (x, $5))
}
| FUN LPAREN binders RPAREN expr2 {
  Pattern(None, ($3, $5))
}
| SUBST LPAREN expr2 COMMA expr2 RPAREN LPAREN binder COMMA binder RPAREN expr2 {
  Subst(range 1 12, $3, ($8, ($10, $12)), $5)
}
;

expr:
| expr2 { $1 }
| expr2 COMMA expr { Pair ($1, $3) }
;

%%
