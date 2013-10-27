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

type 'a fn = pattern * 'a

and expr  =
| Var of range * var

| Imm of range * Value.imm

| App of expr * expr
| Enum_d of range * (enum_lit * expr) list
| Enum_d2 of range * (enum_lit * expr) list
| Switch of range * expr * (enum_lit * expr) list
| Switch2 of range * expr * (enum_lit * expr) list
| First of range * expr
| Second of range * expr
| Call of range * expr
| Purify of range * expr * expr

| Complex_interface of range * (enum_lit * expr) list

| Dot of expr * expr

| New of range * enum_lit * range * expr * expr

| Enum_cst of range * enum_lit
| Pair of expr * expr
| Ret of range * expr
| Range of expr * expr
| Id of range * expr * expr * expr
| Enum of range * enum
| Type of range
| Interface of range

| Pi of expr * expr fn
| Sigma of expr * expr fn
| Tree of expr * expr
| Let of bool * expr * expr fn

| For of expr * expr fn
| Interpret of expr * expr

| Subst of range * expr * expr fn fn * expr
| Bind of expr * expr option * expr fn
| Pattern of expr option * expr fn

| Decl of expr * expr

and pattern =
  (* Normal abstraction. *)
| P_var of range * var
  (* Makes for constant functions. *)
| P_blank of range * var
  (* As if the parts of the tuple were accessed using fst and snd.
     The final var is for "as" patterns if the final bool is true,
     otherwise it is just a dummy variable. *)
| P_tuple of pattern * pattern * var * bool
| P_enum_d of range * bool * (enum_lit * pattern) list * var * bool


let rec merge : expr list -> range =
  function
  | [] -> raise Presupposition_error
  | [a] -> range_of_expr a
  | a :: bs -> merge_ranges (range_of_expr a) (merge bs)

and range_of_expr : expr -> range =
  function
  | Imm (p, _)
  | Var (p, _)
  | Enum_cst (p, _)
  | Switch (p, _, _)
  | Switch2 (p, _, _)
  | Purify (p, _, _)
  | Enum_d (p, _)
  | Enum_d2 (p, _)
  | Complex_interface(p, _)
  | Ret (p, _)
  | Call (p, _)
  | First (p, _)
  | Second (p, _)
  | Enum (p, _)
  | New (p, _, _, _, _)
  | Type p
  | Interface p
  | Subst (p, _, _, _)
  | Id (p, _, _, _) -> p

  | Interpret (p, q)
  | Tree (p, q)
  | Decl (p, q)
  | Range (p, q)
  | Pair (p, q)
  | Dot (p, q)
  | App (p, q) -> merge [p; q]

  | Pattern (None, p) -> range_of_expr_fn p

  | Pattern (Some e, d)
  | Bind (e, None, d)
  | Let (_, e, d)
  | For (e, d)
  | Pi (e, d)
  | Sigma (e, d) -> merge_ranges (range_of_expr e) (range_of_expr_fn d)

  | Bind (a, Some b, d) ->
    merge_ranges (range_of_expr a)
      (merge_ranges (range_of_expr b) (range_of_expr_fn d))

and range_of_expr_fn (p, d) =
  merge_ranges (range_of_pattern p) (range_of_expr d)

and range_of_expr_fn_fn (p, d) =
  merge_ranges (range_of_pattern p) (range_of_expr_fn d)

and range_of_pattern : pattern -> range =
  function
  | P_var (p, _)
  | P_enum_d (p, _, _, _, _)
  | P_blank (p, _) -> p
  | P_tuple (p, q, _, _) ->
    merge_ranges (range_of_pattern p) (range_of_pattern q)

type toplevel =
| Assert of expr * expr * toplevel
| AssertEq of expr * expr * expr * toplevel
| Val of Base.var * expr * toplevel
| Compile of Base.var * (Base.var * expr) list * expr * expr * toplevel
| Test of Base.var * expr list * expr * toplevel
| Eof
