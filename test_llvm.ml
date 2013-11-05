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

let parse_string' str =
  let lexbuf = Lexing.from_string str in
  try
    Syntax.expr Lex.token lexbuf
  with Parsing.Parse_error ->
    let curr = lexbuf.Lexing.lex_curr_p in
    let line = curr.Lexing.pos_lnum in
    let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
    let tok = Lexing.lexeme lexbuf in
    Printf.printf "%d:%d unexpected token: %s\n" line cnum tok;
    raise Parsing.Parse_error

let parse_string ctx t str =
  let a_poly = Check_expr.check ctx t (parse_string' str) in
  Check_term.poly ctx t a_poly;
  let a_value = Eval.poly (Ctx.assign ctx) a_poly in
  a_value

let compile name (proto : Ipl_llvm.proto) str =
  let cod, args = proto in
  let codt = Value.Tree(Eval.empty_interface, (Value.Imm_set_u cod)) in
  let ext ctx (v, t) =
    let v' = Var.of_string v in
    Ctx.extend ctx no_location v' (Value.el_of_var v') (Value.Imm_set t) in
  let ctx = List.fold_left ext Initial.ctx args in
  let ct = parse_string ctx codt str in
  let fn = Ipl_llvm.compile_function name proto ct Ipl_compile.no_invoke in
  ct, fn

open Llvm_executionengine

let test name (result:imm) (args:(string * imm) list) str =
  let cod = Ipl_llvm.size_of_imm result in
  let dom = List.map (fun (x, y) -> x, Ipl_llvm.size_of_imm y) args in
  let ct, fn = compile name (cod, dom) str in
  (* Llvm.dump_value fn; *)
  (* Interpret function. *)
  let poly = Reify.el ct in
  let ext ctx (v, t) =
    let v' = Var.of_string v in
    Ctx.extend ctx no_location v' (Value.Imm t)
      (Value.Imm_set (Ipl_llvm.size_of_imm t))
  in
  let ctx = List.fold_left ext Initial.ctx args in
  let rho = Ctx.assign ctx in
  begin
    match Eval.poly rho poly with
    | Value.Ret(Value.Imm m) when m = result -> ()
    | Value.Ret(Value.Imm m) ->
      failwith (Format.sprintf "Expected %s, got %s."
                  (Printing.string_of_imm result)
                  (Printing.string_of_imm m))
    | m ->
      Format.eprintf "Expected %s. Got:\n" (Printing.string_of_imm result);
      Printing.el Format.err_formatter m;
      raise Presupposition_error
  end;
  (* Execute compiled function. *)
  let cargs =
    Array.of_list (List.map (fun (_, x) -> Ipl_llvm.generic_of_imm x) args)
  in
  let r = ExecutionEngine.run_function fn cargs Ipl_llvm.main_engine in
  if not (Ipl_llvm.generic_eq_imm r result) then
    failwith (Format.sprintf "Expected %s." (Printing.string_of_imm result))

let i32 x = Imm32 (Int32.of_int x)

let _ = test "test1" (i32 10) ["x", i32 5]
"block {
val fun dup(z i32) tuple(_ i32, _ i32) = z, z;
val (+) = mod32::(+);
yield((+)(dup(x)));
}"


let _ = test "test2" (i32 20) ["x", i32 10; "y", i32 11]
"block {
val (+) = mod32::(+);
val (<) = mod32::(<);
val fun dup(z i32) tuple(_ i32, _ i32) = z, z;
val tmp tuple(_ i32, _ i32) = x < y ? dup(x) : dup(y);
val tmp2 = fst(tmp) + snd(tmp);
yield(tmp2);
}"

let _ = test "test3" (i32 8) ["x", i32 3; "y", i32 5]
"block {
for z in x..y { }
val (+) = mod32::(+);
yield(x+y);
}"

let _ = test "test4" (i32 20) ["x", i32 10]
"block {
val (+) = mod32::(+);
new c = new_i32(x);
val w i32 = do c.call(fun(u) u + x);
yield(w);
}"


(* Initial value of counter 99. Increase 3 (=x) times 33 gives 198. *)
let _ = test "test5" (i32 198) ["x", i32 3]
"block {
val (+) = mod32::(+);
new c = new_i32(99);
for z in 0..x {
  val _ i32 = do c.call(fun(i) i + 33);
}
yield(do c.call(fun(i)i));
}"

let _ = test "euler3" (i32 233168) ["x", i32 1000]
"block {
val fun (z bool) || (y bool) = z ? true : y;
val (==) = mod32::(==);
val (+) = mod32::(+);
val srem = mod32::srem;
new c = new_i32(0);
for z in 0..x {
 if srem(z, 3, refl) == 0 || srem(z, 5, refl) == 0 {
   c := c + z;
 }
}
yield(get c);
}"
