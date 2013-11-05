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

let ulift (f : 'a -> 'b) : 'a Value.fn -> 'b Term.fn =
  function
  | Value.Cst c -> no_pattern, f c
  | Value.Fn(g) ->
    let x = Var.dummy () in
    Pvar(no_location, x), f (g (Value.el_of_var x))

let rec set : Value.set -> Term.set =
  let open Value in
  function
    | Pi(a, b) -> Term.Pi(set a, set_fam b)
    | Sigma(a, b) -> Term.Sigma(set a, set_fam b)
    | Tree(i, a) -> Term.Tree(el i, el a)
    | Id(a, b, c) -> Term.Id(set a, el b, el c)
    | Enum a -> Term.Enum a
    | Imm_set a -> Term.Imm_set a
    | Type -> Term.Type
    | Hole_set -> Term.Hole_set
    | T n -> Term.T(Term.Mono(neut n))

and neut : Value.neut -> Term.mono =
  let open Value in
  function
  | Var x -> Term.Var x
  | App(n, v) -> Term.App (neut n, el v)
  | Fst(n) -> Term.Fst(neut n)
  | Snd(n) -> Term.Snd(neut n)
  | Enum_d(n, _C, a) ->
    Term.Enum_d(neut n, set_fam _C, Enum_map.map (fun x -> el (Lazy.force x)) a)
  | Subst(r, _C, d) -> Term.Subst(neut r, ulift set_fam _C, el d)
  | Builtin(p, cs, n, rs) ->
    Term.Builtin(p, List.map (fun x -> Term.Mono(Term.Imm x)) cs
      @ Term.Mono (neut n) :: List.map el rs)
  | For(n, _U, _I, f) ->
    Term.For(neut n, el_fam _U, el _I, el_fam f)
  | Bind(n, _B, f) -> Term.Bind(neut n, el _B, el_fam f)
  | Range1(n, e) -> Term.Range(Term.Mono(neut n), el e)
  | Range2(i, n) ->
    Term.Range(Term.Mono(Term.Imm (Imm32 i)), Term.Mono(neut n))
  | Local(st, i, a, n, p) ->
    Term.Local(st, el i, el a, el n, component p)
  | Catch(b, i, a, f, p) ->
    Term.Catch(el b, el i, el a, el f, component p)
  | Purify(c, m) -> Term.Purify(el c, Term.Mono(neut m))

and el : Value.el -> Term.poly =
  let open Value in
  function
  | Imm a -> Term.Mono(Term.Imm a)
  | Pi_u(a, b) -> Term.Mono(Term.Pi_u(el a, el_fam b))
  | Sigma_u(a, b) -> Term.Mono(Term.Sigma_u(el a, el_fam b))
  | Tree_u(i, a) -> Term.Mono(Term.Tree_u(el i, el a))
  | Id_u(a, b, c) -> Term.Mono(Term.Id_u(el a, el b, el c))
  | Enum_u a -> Term.Mono(Term.Enum_u a)
  | Imm_set_u a -> Term.Mono(Term.Imm_set_u a)
  | Lambda(f) -> Term.Lambda(el_fam f)
  | Pair(a, b) -> Term.Pair(el a, el b)
  | Ret(a) -> Term.Ret(el a)
  | Invk(c, t) -> Term.Invk(el c, el_fam t)
  | Neut(n) -> Term.Mono(neut n)
  | Hole -> Term.Hole

and component : Value.component -> Term.poly =
  let open Value in
  function
  | Component1 n -> Term.Mono(neut n)
  | Component2(p, f) -> Term.Invk(Term.Mono(neut p), el_fam f)
  | Component3(n, b, f) ->
    Term.Invk(Term.Pair(Term.Mono(neut n), el b), el_fam f)


and set_fam x = ulift set x
and el_fam x = ulift el x
