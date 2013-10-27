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

let maybe_print str = () (* Printf.printf "%s" str *)

let initial_ctx = Initial.ctx

let verify a __A =
  let ___A = Reify.set __A in
  Check_term.set initial_ctx ___A;
  let ____A = Eval.set (Ctx.assign initial_ctx) ___A in
  let _____A = Reify.set ____A in
  Value.eq_set __A ____A;
  Term.eq_set [] ___A _____A;
  Check_term.poly initial_ctx __A a;
  let aa = Eval.poly (Ctx.assign initial_ctx) a in
  let aaa = Reify.el aa in
  Check_term.poly initial_ctx __A aaa;
  let aaaa = Eval.poly (Ctx.assign initial_ctx) aaa in
  let aaaaa = Reify.el aaaa in
  Value.eq_el aa aaaa;
  Term.eq_poly [] aaa aaaaa

let parse_string' str =
  let lexbuf = Lexing.from_string str in
  try
    Syntax.expr Lex.token lexbuf
  with Parsing.Parse_error ->
    let curr = lexbuf.Lexing.lex_curr_p in
    let line = curr.Lexing.pos_lnum in
    let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
    let tok = Lexing.lexeme lexbuf in
    Printf.printf "Parse: %s\n" str;
    Printf.printf "%d:%d unexpected token: %s\n" line cnum tok;
    raise Parsing.Parse_error

let with_reporting str f a b =
  try f a b
  with
  | Check_expr.Error as e ->
    Format.eprintf "\n\n@?%s" str;
    raise e
  | e ->
    Format.print_string str;
    raise e

let parse_string str =
  let a, b =
    with_reporting (Printf.sprintf "Infer: %s" str)
      Check_expr.infer
      initial_ctx
      (parse_string' str)
  in
  with_reporting "Verify"
    verify
    (Term.Mono b)
    a;
  maybe_print (Printf.sprintf "OK: success '%s'\n" str);
  a, b

let parse_set str =
  with_reporting (Printf.sprintf "Check set: %s" str)
    Check_expr.set
    initial_ctx
    (parse_string' str)
    |> ignore;
  maybe_print (Printf.sprintf "OK: success set '%s'\n" str)

let _ = parse_string "(val x = true; x)"
let _ = parse_string "(val fun f(x i32) i32 = x; f)"
let _ = parse_set "enum {false,true}"
let _ = parse_set "enum {}"
let _ = parse_set "dep(x enum {false,true}) -> dep(y type) -> y"
let _ = parse_set "tuple(x bool, _ bool)"
let _ = parse_set "struct {x: bool}"
let _ = parse_set "struct {x: bool, y: void}"
let _ = parse_set "struct {}"
let _ = parse_set "union {x: bool}"
let _ = parse_set "union {x: bool, y: struct {}}"
let _ = parse_set "union {}"
let _ = parse_string "()"
let _ = parse_string "(val x void = (); x)"
let _ = parse_set "interface"
let _ = parse_string "(val x enum {false,true} = 'true; x)"
let _ = parse_set "struct {a: i32, C: dep(x i32)->i32}"
let _ = parse_set "(meth(x void) bool) => i8"
let _ = parse_set "(meth(x void, y bool) i32) => i8"
let _ = parse_string
  "(
val string = void;
val open = meth(x string) i32;
val close = meth(_ i32) bool;
()
)"
let _ = parse_string "
(val x =
 block meth {} => bool {
     if true { yield(()); } else { }
     yield(true);
 };
 x)"

let _ = parse_string "true ? true : false"

let _ = parse_string "(
val (+) = mod32::(+);
val test_for2 = block (meth(_ i32)bool) => void {
    for x in 0..(1+1) {
      val _ = do call2(meth(_ i32)bool, x);
    }
}; () )"

let _ = parse_string "(
val fun (||)(z bool, y bool) bool = z ? true : y;
val (==) = mod32::(==);
val (+) = mod32::(+);
val srem = mod32::srem;
val fun euler2(x i32) = block meth {} => i32 {
 new c = new_i32(0);
 for z in 0..x {
   if srem(z, 3, refl) == 0 || srem(z, 5, refl) == 0 {
     val _ = do c.call(fun(u) u + z);
   }
 }
 val w i32 = do c.call(fun(u) u);
 yield(w);
};
()
)"

let _ = parse_string "(
val fun (||)(z bool, y bool) bool = z ? true : y;
val (==) = mod32::(==);
val (+) = mod32::(+);
val srem = mod32::srem;
val fun euler2(x i32) = block meth {} => i32 {
 new c = new_i32(0);
 for z in 0..x {
   if srem(z, 3, refl) == 0 || srem(z, 5, refl) == 0 {
     val _ = do call(c@(fun(u) u + z));
   }
 }
 yield(do call(c@(fun(u) u)));
};
()
)"
