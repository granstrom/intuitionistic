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

let extend_context ctx ident expr =
  let _AAA, a = Check_expr.infer ctx expr in
  assert(let _BBB = Check_term.mono ctx a in
         Value.eq_set _AAA _BBB;
         true);
  let aa = Eval.mono (Ctx.assign ctx) a in
  Ctx.extend_el_value ctx ident aa _AAA

let rec toplevel ctx = function
  | Expr.Eof -> ()
  | Expr.Assert (a, _A, rest) ->
    let _AA = Check_expr.set ctx _A in
    assert(Check_term.set ctx _AA; true);
    let _AAA = Eval.set (Ctx.assign ctx) _AA in
    let _ = Check_expr.check ctx _AAA a in
    toplevel ctx rest
  | Expr.AssertEq(a, b, _A, rest) ->
    let _AA = Check_expr.set ctx _A in
    assert(Check_term.set ctx _AA; true);
    let rho = Ctx.assign ctx in
    let _AAA = Eval.set rho _AA in
    let aa = Check_expr.check ctx _AAA a in
    assert(Check_term.poly ctx _AAA aa; true);
    let bb = Check_expr.check ctx _AAA b in
    assert(Check_term.poly ctx _AAA bb; true);
    let aaa = Eval.poly rho aa in
    let bbb = Eval.poly rho bb in
    begin
      try Value.eq_el aaa bbb
      with Value.Not_equal ->
        Check_expr.report (Expr.range_of_expr a)
          "assertion failed: %a"
          Printing.el aaa;
        Check_expr.report (Expr.range_of_expr b)
          "not equal to %a"
          Printing.el bbb;
        raise Check_expr.Error
    end;
    toplevel ctx rest
  | Expr.Val (v, a, rest) -> toplevel (extend_context ctx v a) rest
  | Expr.Compile(Variable f, args, cod, def, rest) ->
    let imm_set ctx s =
      match Eval.set (Ctx.assign ctx) (Check_expr.set ctx s) with
      | Value.Imm_set sz -> sz
      | _ ->
        Check_expr.report (Expr.range_of_expr s)
          "expected set of immediate values (e.g., i32)";
        raise Check_expr.Error
    in
    let argvals = List.map (fun (x, y) -> x, imm_set ctx y) args in
    let codval = imm_set ctx cod in
    let ext ctx (v, t) = Ctx.extend_value ctx v (Value.Imm_set t) in
    let ctx' = List.fold_left ext ctx argvals in
    let codt = Value.Tree(Eval.empty_interface, (Value.Imm_set_u codval)) in
    let defv, _ = Check_expr.check_eval ctx' codt def in
    let _ = Ipl_llvm.compile_function f (codval, argvals) defv Ipl_compile.no_invoke in
    toplevel ctx rest
  | Expr.Test(Variable f, args, expect, rest) ->
    let mapper ctx x =
      let _AA, a = Check_expr.infer ctx x in
      let rho = Ctx.assign ctx in
      let aa = Eval.mono rho a in
      match match aa with
      | Value.Imm (Value.Enum_cst _) -> None
      | Value.Imm (Value.Refl) -> None
      | Value.Imm i -> Some i
      | _ -> None
      with
      | Some i -> i
      | None ->
        Check_expr.report (Expr.range_of_expr x)
          "expected integer constant";
        raise Check_expr.Error
    in
    let args' = Array.of_list (
      List.map Ipl_llvm.generic_of_imm (
        List.map (mapper ctx) args)) in
    let expect' = mapper ctx expect in
    let fn = match Llvm_executionengine.ExecutionEngine.find_function
        f Ipl_llvm.main_engine
      with
      | Some g -> g
      | None ->
        Format.eprintf "undefined function '%s'\n" f;
        raise Check_expr.Error
    in
    let r = Llvm_executionengine.ExecutionEngine.run_function
      fn args' Ipl_llvm.main_engine
    in
    if not (Ipl_llvm.generic_eq_imm r expect') then begin
      Check_expr.report (Expr.range_of_expr expect)
        "expected %s, got %Ld"
        (Printing.string_of_imm expect')
        (Llvm_executionengine.GenericValue.as_int64 r);
      raise Check_expr.Error
    end;
    toplevel ctx rest

let run lexbuf =
  try
    let top = Syntax.file Lex.token lexbuf in
    toplevel Initial.ctx top
  with
  | Parsing.Parse_error ->
    let curr = lexbuf.Lexing.lex_curr_p in
    let line = curr.Lexing.pos_lnum in
    let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
    let file = curr.Lexing.pos_fname in
    let tok = Lexing.lexeme lexbuf in
    Format.eprintf "%s:%d.%d: unexpected token: %s\n@?" file line cnum tok;
  | Lex.Error(d, e) ->
    Format.eprintf "%a\n@?" Lex.format_error (d, e);
  | Ctx.Rebound_error(_, v) ->
    Format.eprintf "variable %a is already abound\n@?" Base.format_var v;
  | Check_expr.Error ->
    (* Error message already printed, including newline. *)
    Format.eprintf "@?"
  | Base.Duplicate_key k ->
    Format.eprintf "duplicate enum literal %a\n@?"
      Base.format_enum_lit k
  | e ->
    Format.eprintf "internal compiler error\n@?";
    raise e

let run_file file =
  try
    let ch = open_in file in
    let lb = Lexing.from_channel ch in
    lb.Lexing.lex_curr_p <- {lb.Lexing.lex_curr_p with Lexing.pos_fname = file};
    Check_expr.filename := file;
    run lb
  with
  | Sys_error s -> Format.eprintf "%s\n@?" s

let main () =
  let len = Array.length Sys.argv in
  if len <> 2 then
    Printf.eprintf "usage: %s <filename>\n@?" Sys.argv.(0)
  else begin
    let fname = Sys.argv.(1) in
    run_file fname;
    let outname =
      (try
         let ri = String.rindex fname '.' in
         String.sub fname 0 ri
       with Not_found -> fname) ^ ".bc"
    in
    if not(Llvm_bitwriter.write_bitcode_file Ipl_llvm.main_module outname) then
      Printf.eprintf "Could not write to file '%s'\n@?" outname
  end

let _ = if not !Sys.interactive then main ()
