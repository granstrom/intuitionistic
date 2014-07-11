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

let symbol_range () = (
  pos_of_lexpos (Parsing.symbol_start_pos ()),
  pos_of_lexpos (Parsing.symbol_end_pos ()))

let range (a:int) (b:int):range =
  (pos_of_lexpos (Parsing.rhs_start_pos a),
   pos_of_lexpos (Parsing.rhs_end_pos b))

let end_loc (a:int) :location =
  let p = pos_of_lexpos (Parsing.rhs_end_pos a) in
  (filename (), (p, p))

let loc (a:int) (b:int):location =
  (filename (), range a b)

let symbol_loc ():location =
  (filename (), symbol_range ())

let unit_lit_of_loc l =
  let el = l, unit_lit in
  l, Decl((l, Enum_cst(el)), (l, Enum [el]))

let mk_struct_or_union a b c labels =
  let l1 = loc a b in
  let l2 = loc a c in
  let enum = l1, Enum(List.map fst labels) in
  let dtor = l2, Enum_d(labels) in
  let v = Var.dummy () in
  let vv = l1, Var v in
  let ap = l2, App(dtor, vv) in
  let patt = Pvar(l1, v) in
  l2, enum, patt, ap

let mk_struct a b c labels =
  let l, enum, patt, ap = mk_struct_or_union a b c labels in
  l, Pi(enum, (patt, ap))

let mk_union a b c labels =
  let l, enum, patt, ap = mk_struct_or_union a b c labels in
  l, Sigma(enum, (patt, ap))

let mk_blank loc = Pvar(loc, Var.dummy ())

type maybe_bind =
| No_bind of expr
| Do_bind of expr


let maybe_bind l1 lwhole body = function
  | No_bind e -> lwhole, body e
  | Do_bind e ->
    let x = Var.dummy () in
    lwhole, Bind(e, None, (Pvar(l1, x), (lwhole, body (l1, Var x))))

%}

%token EOF                 /* <end of file> */
%token <string> LITERAL    /* string literal */
%token <string> IDENT      /* identifier */
%token <Base.imm> IMM     /* numeric literal */
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
| { symbol_loc (), Eof }
| ASSERT expr IS expr SEMI file { loc 1 5, Assert($2, $4, $6) }
| ASSERT expr EQ expr IS expr SEMI file { loc 1 7, AssertEq($2, $4, $6, $8) }
| VAL variable EQ expr SEMI file { loc 1 5, Val(loc 2 2, $2, $4, $6) }
| VAL variable expr EQ expr SEMI file {
  loc 1 6,
  Val(loc 2 2, $2, (loc 3 5, Decl($5, $3)), $7)
}
| FUN fun_arglist EQ expr SEMI file {
  let (f, fl), (x, _A) = $2 in
  loc 1 5, Val(fl, f, (fst $4, Pattern(Some _A, (x, $4))), $6)
}
| FUN fun_arglist expr EQ expr SEMI file {
  let (f, fl), (x, _A) = $2 in
  let body = loc 3 5, Decl($5, $3) in
  loc 1 6, Val(fl, f, (fst body, Pattern(Some _A, (x, body))), $7)
}
| COMPILE ident LPAREN compile_arglist RPAREN expr EQ expr SEMI file {
  loc 1 9, Compile($2, $4, $6, $8, $10)
}
| TEST ident LPAREN test_arglist RPAREN EQ expr SEMI file {
  loc 1 8, Test($2, $4, $7, $9)
}
;

compile_arglist:
| ident expr2 { [$1, $2] }
| ident expr2 COMMA compile_arglist { ($1, $2) :: $4 }
;

test_arglist:
| expr2 { [$1] }
| expr2 COMMA test_arglist { $1 :: $3 }
;

fun_arglist:
| variable LPAREN arglist RPAREN { ($1, loc 1 1), $3 }
| prefix LPAREN binder expr2 RPAREN { (Var.of_string $1, loc 1 1), ($3, $4) }
| LPAREN binder expr2 RPAREN infix LPAREN binder expr2 RPAREN {
  (Var.of_string $5, loc 5 5),
  (Ppair($2, $7), (loc 2 8, Sigma($3, ($2, $8))))
}
;

ident:
| IDENT { $1 }
| LPAREN infix RPAREN { $2 }
| LPAREN prefix DOT RPAREN { $2 }
;
enum_lit: ident { loc 1 1, Enum_lit $1 };
variable: ident { Var.of_string $1 };

binder:
| variable { Pvar(loc 1 1, $1) }
| BLANK { mk_blank (loc 1 1) }
;

binders:
| pattern { $1 }
| pattern COMMA binders { Ppair($1, $3) }
;

pattern:
| binder { $1 }
| LPAREN binders RPAREN { $2 }
;

arglist:
| binder expr2 { $1, $2 }
| binder expr2 COMMA arglist {
    let p2, t2 = $4 in
    Ppair($1, p2),
    (loc 1 2, Sigma($2, ($1, t2)))
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
| enum_lit AT pattern COLON expr2 {
  ($1, (loc 3 5, Pattern(None, ($3, $5))))
}
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

bind_cases:
| CASE enum_lit AT pattern COLON stmts {
  [$2, (loc 4 6, Pattern(None, ($4, $6)))]
}
| CASE enum_lit AT pattern COLON stmts bind_cases{
  ($2, (loc 4 6, Pattern(None, ($4, $6)))) :: $7
}
;

expr_stmt:
| DO expr { $2 }
| GET ident {
  let x = Var.dummy () in
  loc 1 2,
  Call(loc 1 2,
       Pair((loc 2 2,
             Enum_cst(loc 2 2, Enum_lit $2)),
            (loc 2 2,
             Pattern(None, (Pvar(loc 1 1, x),
                            (loc 1 1, Var x))))))
}
;

maybe_bind:
| expr_stmt { Do_bind $1 }
| expr { No_bind $1 }
;

simple_stmt:
| IF maybe_bind LBRACE stmts RBRACE {
  maybe_bind (loc 1 1) (loc 1 5) (fun x ->
    Switch(x,
           [(loc 3 3, true_lit), $4;
	    (loc 5 5, false_lit),
            (loc 5 5, Ret(unit_lit_of_loc (loc 5 5)))]))
  $2
}
| IF maybe_bind LBRACE stmts RBRACE ELSE LBRACE stmts RBRACE {
  maybe_bind (loc 1 1) (loc 1 9) (fun x ->
    Switch(x,
           [(loc 3 3, true_lit), $4;
            (loc 7 7, false_lit), $8]))
  $2
}
| FOR pattern IN maybe_bind LBRACE stmts RBRACE {
  maybe_bind (loc 3 3) (loc 1 7) (fun x -> For(x, ($2, $6))) $4
}
| SWITCH maybe_bind LBRACE cases RBRACE {
  maybe_bind (loc 1 1) (loc 1 5) (fun x -> Switch(x, $4)) $2
}
| SWITCH maybe_bind LBRACE bind_cases RBRACE {
  maybe_bind (loc 1 1) (loc 1 5) (fun x -> Switch2(x, $4)) $2
}
;

stmt:
| simple_stmt { $1 }
| expr_stmt SEMI { $1 }
;

opaque_opt:
| { true }
| OPAQUE { false }
;

val_stmt:
| VAL pattern EQ stmt {
  fun x -> loc 1 4, Bind($4, None, ($2, x))
}
| VAL pattern expr EQ stmt {
  fun x -> loc 1 5, Bind($5, Some $3, ($2, x))
}
| VAL pattern EQ opaque_opt expr SEMI {
  fun x -> loc 1 6, Let($4, $5, ($2, x))
}
| VAL pattern expr EQ opaque_opt expr SEMI {
  fun x -> loc 1 7, Let($5, (loc 3 6, Decl($6, $3)), ($2, x))
}
| FUN fun_arglist EQ opaque_opt expr SEMI {
  let (f, frange), (x, _A) = $2 in
  fun y -> loc 1 6,
    Let($4, (loc 5 5, Pattern(Some _A, (x, $5))),
        (Pvar(frange, f), y))
}
| FUN fun_arglist expr EQ opaque_opt expr SEMI {
  let (f, frange), (x, _A) = $2 in
  fun y -> loc 1 7,
    Let($5, (loc 3 6, Pattern(Some _A, (x, (loc 3 6, Decl($6, $3))))),
        (Pvar(frange, f), y))
}
;

non_empty_stmts:
| simple_stmt { $1 }
| simple_stmt non_empty_stmts {
  let l = end_loc 1 in
  loc 1 2,
  Bind($1, Some(l, Enum([l, unit_lit])), (mk_blank l, $2))
}
| DO expr SEMI stmts {
  loc 1 4,
  Bind($2, Some(loc 3 3, Enum([loc 3 3, unit_lit])),
       (mk_blank (loc 3 3), $4))
}
| YIELD LPAREN expr RPAREN SEMI { loc 1 5, Ret($3) }
| YIELD LPAREN expr_stmt RPAREN SEMI { loc 1 5, snd $3 }
| NEW enum_lit EQ expr SEMI stmts {
  loc 1 6, New($2, $4, $6)
}
| val_stmt stmts { loc 1 2, snd ($1 $2) }
| ident COLON_EQ expr SEMI stmts {
  let a = loc 1 4,
    Call(loc 1 3,
         Pair((loc 1 1, Enum_cst(loc 1 1, Enum_lit $1)),
              (loc 1 3,
               Pattern(None, (Pvar(loc 1 1, Var.of_string $1), $3)))))
  in
  loc 1 5,
  Bind(a, None, (mk_blank (loc 4 4), $5))
}
;

stmts:
| { let l = symbol_loc () in l, Ret(unit_lit_of_loc l) }
| non_empty_stmts { $1 }
;

compound_expr:
| val_stmt compound_expr { loc 1 2, snd ($1 $2) }
| expr { $1 }
;

prefix:
| BANG  { "(!.)" }
| TILDE { "(~.)" }
| MINUS { "(-.)" }
| STAR { "(*.)" }
;

gen_prefix:
| prefix { loc 1 1, Var(Var.of_string $1) }
;

multiplication:
| STAR { "(*)" }
| STAR_STAR { "(**)" }
;

gen_multiplication:
| multiplication { loc 1 1, Var(Var.of_string $1) }
;

addition:
| PLUS { "(+)" }
| PLUS_PLUS { "(++)" }
| MINUS { "(-)" }
;

gen_addition:
| addition { loc 1 1, Var(Var.of_string $1) }
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
| relation { loc 1 1, Var(Var.of_string $1) }
;

connective:
| AND_AND { "(&&)" }
| BAR_BAR { "(||)" }
| CARET_CARET { "(^^)" }
;

gen_connective:
| connective { loc 1 1, Var(Var.of_string $1) }
;

infix:
| multiplication { $1 }
| addition { $1 }
| relation { $1 }
| connective { $1 }
;

expr10:
| LBRACKET RBRACKET { loc 1 2, Hole }
| IMM { loc 1 1, Imm($1) }
| variable { loc 1 1, Var($1) }
| QUOTE enum_lit { loc 1 2, Enum_cst ($2) }
| REFL { loc 1 1, Imm(Refl) }
| TYPE { loc 1 1, Type }
| INTERFACE { loc 1 1, Interface }
| LPAREN RPAREN { unit_lit_of_loc (loc 1 2) }
| FST LPAREN expr RPAREN { loc 1 4, First $3 }
| SND LPAREN expr RPAREN { loc 1 4, Second $3 }
| CALL LPAREN expr RPAREN { loc 1 4, Call $3 }
| CALL LPAREN RPAREN { loc 1 4, Call(unit_lit_of_loc (loc 2 3)) }
| expr10 LPAREN expr RPAREN { loc 1 4, App($1, $3) }
| expr10 LPAREN RPAREN { loc 1 3, App($1, unit_lit_of_loc (loc 2 3)) }
| expr10 COLON_COLON enum_lit { loc 1 3, App($1, (loc 3 3, Enum_cst $3)) }
| expr10 COLON_COLON infix { loc 1 3, App($1, (loc 3 3, Enum_cst(loc 3 3, Enum_lit $3))) }
| ENUM LBRACE enum_labels RBRACE { loc 1 4, Enum $3 }
| STRUCT LBRACE labels RBRACE { mk_struct 1 2 4 $3 }
| FUN LBRACE labels RBRACE { loc 1 4, Enum_d $3 }
| FUN LBRACE blabels RBRACE { loc 1 4, Enum_d2 $3 }
| UNION LBRACE labels RBRACE { mk_union 1 2 4 $3 }
| TUPLE LPAREN arglist RPAREN { snd $3 }
| METH LBRACE labels RBRACE { loc 1 4, Complex_interface $3 }
| INTERPRET expr LBRACE expr RBRACE { loc 1 4, Interpret($2, $4) }
| BLOCK expr4 EQ_GREATER expr3 LBRACE stmts RBRACE {
  loc 1 7, Decl($6, (loc 2 4, Tree($2, $4)))
}
| BLOCK LBRACE stmts RBRACE { $3 }
| PURIFY expr LBRACE stmts RBRACE {
  loc 1 5, Purify($2, $4)
}
| LPAREN compound_expr RPAREN { $2 }
;

expr9:
| expr10 { $1 }
| enum_lit DOT expr9 { loc 1 3, Dot((loc 1 1, Enum_cst $1), $3) }
| enum_lit AT expr9 { loc 1 3, Pair((loc 1 1, Enum_cst $1), $3) }
;

expr8:
| expr9 { $1 }
| gen_prefix expr9 { loc 1 2, App($1, $2) }
;

expr7:
| expr8 { $1 }
| expr7 gen_multiplication expr8 { loc 1 3, App($2, (loc 1 3, Pair($1, $3))) }
;

expr6:
| expr7 { $1 }
| expr6 gen_addition expr7 { loc 1 3, App($2, (loc 1 3, Pair($1, $3))) }
;

expr5:
| expr6 { $1 }
| expr6 gen_relation expr6 { loc 1 3, App($2, (loc 1 3, Pair($1, $3))) }
| expr6 AEQ LPAREN expr2 RPAREN expr6 {
  loc 1 6, Id($4, $1, $6)
}
;

expr4:
| expr5 { $1 }
| expr5 gen_connective expr5 { loc 1 3, App($2, (loc 1 3, Pair($1, $3))) }
;

expr3:
| expr4 { $1 }
| expr4 DOT_DOT expr4 { loc 1 3, Range($1, $3) }
| DEP LPAREN arglist RPAREN MINUS_GREATER expr3 {
  let x, _A = $3 in
  loc 1 6, Pi(_A, (x, $6))
}
| expr4 MINUS_GREATER expr3 {
  loc 1 3, Pi($1, (mk_blank (loc 2 2), $3))
}
| expr4 EQ_GREATER expr3 { loc 1 3, Tree($1, $3) }
| expr4 QUESTION expr4 COLON expr4 {
  loc 1 5,
  Switch($1, [(loc 2 2, true_lit), $3; (loc 4 4, false_lit), $5])
}
;

expr2:
| expr3 { $1 }
| METH LPAREN arglist RPAREN expr2 {
  let x, _A = $3 in
  let _B = loc 5 5, Pattern(None, (x, $5)) in
  loc 1 5, Decl((loc 1 5, Pair(_A, _B)), (loc 1 1, Interface))
}
| FUN LPAREN arglist RPAREN expr2 {
  let x, _A = $3 in
  loc 1 5, Pattern(Some _A, (x, $5))
}
| FUN LPAREN binders RPAREN expr2 {
  loc 1 5, Pattern(None, ($3, $5))
}
| SUBST LPAREN expr2 COMMA expr2 RPAREN LPAREN binder COMMA binder RPAREN expr2 {
  loc 1 12, Subst($3, ($8, ($10, $12)), $5)
}
;

expr:
| expr2 { $1 }
| expr2 COMMA expr { loc 1 3, Pair($1, $3) }
;

%%
