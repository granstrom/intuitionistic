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
open Value
open Format

let reset_counter fmt fn x =
  Var.reset_print ();
  let boxes = Format.pp_get_max_boxes fmt () in
  pp_set_max_boxes fmt 20;
  fprintf fmt "%a" fn x;
  pp_set_max_boxes fmt boxes

let string_of_imm =
  function
  | Imm8 i8 -> Printf.sprintf "%dc" (Char.code i8)
  | Imm16 i16 -> Printf.sprintf "%ds" i16
  | Imm32 i32 -> Printf.sprintf "%ld" i32
  | Imm64 i64 -> Printf.sprintf "%Ldq" i64
  | Enum_imm(_, Enum_lit "()") -> "()"
  | Enum_imm(_, Enum_lit x) -> "'" ^ x
  | Refl -> "refl"

let string_of_size =
  function
  | I8 -> "i8"
  | I16 -> "i16"
  | I32 -> "i32"
  | I64 -> "i64"

(* Print atomic constructs. *)
let rec set_atom (fmt:formatter) = function
  | Enum r when r = Base.unit_enum -> fprintf fmt "void"
  | Enum e -> fprintf fmt "enum { %a }" format_enum e
  | Imm_set s -> fprintf fmt "%s" (string_of_size s)
  | Type -> fprintf fmt "type"
  | Sigma(_, _) as s ->
    fprintf fmt "tuple(";
    let _ = sigma fmt s in
    fprintf fmt ")"
  | T x -> neut_atom fmt x
  | a -> fprintf fmt "(%a)" set_open a

and neut_atom (fmt:formatter) = function
  | Var x -> Var.format fmt x
  | App(f, a) -> fprintf fmt "%a(%a)" neut_atom f el_open a
  | Fst p -> fprintf fmt "fst(%a)" neut_open p
  | Snd p -> fprintf fmt "snd(%a)" neut_open p
  | Enum_d (n, _, els) ->
    fprintf fmt "fun {@\n  @[<v>";
    begin
      match Enum_map.bindings els with
      | [] -> ()
      | (Enum_lit x, y) :: bs ->
        fprintf fmt "%s: %a" x el_atom (Lazy.force y);
        List.iter (function (Enum_lit x, y) ->
          fprintf fmt ",@\n%s: %a" x el_atom (Lazy.force y)) bs
    end;
    fprintf fmt "@]@\n}(%a)" neut_open n;
  | Builtin(bin, a, b, c) ->
    let open Value in
    begin
      match List.map (fun x -> Imm x) a @ (Neut b) :: c with
      | x :: xs ->
        fprintf fmt "%a(%a" builtin bin el_atom x;
        List.iter (fun x -> fprintf fmt ", %a" el_atom x) xs;
        fprintf fmt ")"
      | _ -> ()
    end
  | For(_, _, _, _)
  | Bind(_, _, _) as x ->
    fprintf fmt "block {@\n  @[%a@]@\n}" prog (Neut x)
  | Local(_, _, _, n, p) -> local fmt n  p
  | Catch(_, _, _, f, p) -> catch fmt f  p
  | Purify(s, b) -> fprintf fmt "purify %a {@\n  @[<v>%a@]@\n}" el_open s prog (Neut b)
  | a -> fprintf fmt "(%a)" neut_open a

and el_atom (fmt:formatter) = function
  | Imm i -> fprintf fmt "%s" (string_of_imm i)
  | Pi_u(_, _)
  | Sigma_u(_, _)
  | Tree_u(_, _)
  | Id_u(_, _, _)
  | Enum_u(_)
  | Imm_set_u(_) as x -> set_atom fmt (Eval.univ x)
  | Neut n -> neut_atom fmt n
  | Invk(_, _)
  | Ret _ as x -> fprintf fmt "block {@\n  @[%a@]@\n}" prog x
  | a -> fprintf fmt "(%a)" el_open a

and sigma (fmt:formatter) = function
  | Sigma(a, b) ->
    let x = Var.print_dummy () in
    fprintf fmt "%a %a, " Var.format x set_open a;
    let open Value in
    let xx = Neut(Var x) in
    let bb = sigma fmt (apv b xx) in
    Pair(xx, bb)
  | a ->
    let x = Var.print_dummy () in
    fprintf fmt "%a %a" Var.format x set_open a;
    let open Value in
    Neut(Var x)

(* Print non-atomic constructs. *)
and set_open (fmt:formatter) = function
  | Pi(a, Cst b) -> fprintf fmt "%a -> %a" set_atom a set_open b
  | Pi(a, b) ->
    fprintf fmt "dep(";
    let x = sigma fmt a in
    fprintf fmt ") -> %a" set_open (Value.apv b x)
  | Tree(a, b) -> fprintf fmt "%a => %a" el_atom a el_open b
  | Id(a, b, c) -> fprintf fmt "%a eq(%a) %a" el_atom b set_open a el_atom c
  | T x -> neut_open fmt x
  | a -> set_atom fmt a

and neut_open (fmt:formatter) = function
  | Subst(n, c, p) ->
    let x = Var.print_dummy () in
    let y = Var.print_dummy () in
    let open Value in
    let xx = Neut(Var x) in
    let yy = Neut(Var y) in
    let cc = apv (apv c xx) yy in
    fprintf fmt "subst(%a, %a)(%a, %a) %a"
      neut_atom n el_atom p Var.format x Var.format y set_open cc
  | Range1(a, b) -> fprintf fmt "%a .. %a" neut_atom a el_atom b
  | Range2(a, b) -> fprintf fmt "%ld .. %a" a neut_atom b
  | a ->  neut_atom fmt a

and el_open (fmt:formatter) = function
  | Pi_u(_, _)
  | Sigma_u(_, _)
  | Tree_u(_, _)
  | Id_u(_, _, _)
  | Enum_u(_)
  | Imm_set_u(_) as x -> set_open fmt (Eval.univ x)
  | Neut n -> neut_open fmt n
  | Lambda f ->
    let x = Var.print_dummy () in
    let open Value in
    let xx = Neut(Var x) in
    fprintf fmt "fun(%a) %a" Var.format x el_open (apv f xx)
  | Pair(p, q) -> fprintf fmt "%a, %a" el_atom p el_open q
  | a -> el_atom fmt a

and prog (fmt:formatter) = function
  | Invk(c, t) ->
    let x = Var.print_dummy () in
    let open Value in
    let xx = Neut(Var x) in
    fprintf fmt "val %a = call(%a);@\n%a" Var.format x el_open c prog (apv t xx)
  | Ret r when r = Value.unit_cst -> ()
  | Ret r -> fprintf fmt "yield(%a);" el_open r
  | Neut(Bind(c, _, t)) ->
    let x = Var.print_dummy () in
    let open Value in
    let xx = Neut(Var x) in
    fprintf fmt "val %a = do %a;@\n%a" Var.format x neut_open c prog (apv t xx)
  | Neut(For(n, _, _, body)) ->
    let x = Var.print_dummy () in
    let open Value in
    let xx = Neut(Var x) in
    fprintf fmt "for %a in %a {@\n  @[%a@]@\n}"
      Var.format x neut_open n prog (apv body xx)
  | Neut(Local(_, _, _, n, p)) -> local fmt n p
  | Neut(Catch(_, _, _, f, p)) -> catch fmt f  p
  | e -> fprintf fmt "yield(do %a);" el_open e

and local (fmt:formatter) (n:Value.el) (p:component) =
  fprintf fmt "local %a {@\n  @[%a@]@\n}" el_open n component p

and catch (fmt:formatter) (n:Value.el) (p:component) =
  fprintf fmt "catch %a {@\n  @[%a@]@\n}" el_open n component p

and component (fmt:formatter) :Value.component->unit =
  function
  | Component1(a) -> prog fmt (Neut a)
  | Component2(a, f) -> prog fmt (Invk(Neut a, f))
  | Component3(a, b, f) -> prog fmt (Invk(Pair(Neut a, b), f))


and builtin (fmt:formatter) =
  let sz fmt x =
    pp_print_string fmt
      (match x with
      | I8 -> "8"
      | I16 -> "16"
      | I32 -> "32"
      | I64 -> "64")
  in
  function
  | Aeq s -> fprintf fmt "mod%a::==" sz s
  | Less s -> fprintf fmt "mod%a::<" sz s
  | Add s -> fprintf fmt "mod%a::+" sz s
  | Sub s -> fprintf fmt "mod%a::-" sz s
  | Neg s -> fprintf fmt "mod%a::(-.)" sz s
  | Mul s -> fprintf fmt "mod%a::*" sz s
  | Xor s -> fprintf fmt "mod%a::xor" sz s
  | Or s -> fprintf fmt "mod%a::ior" sz s
  | And s -> fprintf fmt "mod%a::and" sz s
  | Not s -> fprintf fmt "mod%a::not" sz s
  | Lsl s -> fprintf fmt "mod%a::lsl" sz s
  | Lsr s -> fprintf fmt "mod%a::lsr" sz s
  | Asr s -> fprintf fmt "mod%a::asr" sz s
  | Sdiv s -> fprintf fmt "mod%a::sdiv" sz s
  | Srem s -> fprintf fmt "mod%a::srem" sz s
  | Cast(s, t) -> fprintf fmt "mod%a::to_i%a" sz s sz t
  | Less_trans s -> fprintf fmt "mod%a::less_trans" sz s
  | Less_antisym s -> fprintf fmt "mod%a::less_antisym" sz s
  | Aeq_prop s -> fprintf fmt "mod%a::eq_prop" sz s
  | Aeq_refl s -> fprintf fmt "mod%a::eq_refl" sz s
  | Add_commutative s -> fprintf fmt "mod%a::add_comm" sz s
  | Add_associative s -> fprintf fmt "mod%a::add_assoc" sz s
  | Add_unit s -> fprintf fmt "mod%a::add_unit" sz s
  | Add_inverse s -> fprintf fmt "mod%a::add_inv" sz s
  | Mul_commutative s -> fprintf fmt "mod%a::mul_comm" sz s
  | Mul_associative s -> fprintf fmt "mod%a::mul_assoc" sz s
  | Mul_unit s -> fprintf fmt "mod%a::mul_unit" sz s
  | Distributive s -> fprintf fmt "mod%a::dist" sz s
  | Sub_axiom s -> fprintf fmt "mod%a::sub_axiom" sz s

let set fmt x = reset_counter fmt set_open x
let neut fmt x = reset_counter fmt neut_open x
let el fmt x = reset_counter fmt el_open x
