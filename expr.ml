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

type enum_loc_lit = location * enum_lit

type expr'  =
| Hole

| Var of var

| Imm of imm

| App of expr * expr
| Enum_d of (enum_loc_lit * expr) list
| Enum_d2 of (enum_loc_lit * expr) list
| Switch of expr * (enum_loc_lit * expr) list
| Switch2 of expr * (enum_loc_lit * expr) list
| First of expr
| Second of expr
| Call of expr
| Purify of expr * expr

| Complex_interface of (enum_loc_lit * expr) list

| Dot of expr * expr

| New of enum_loc_lit * expr * expr

| Enum_cst of enum_loc_lit
| Pair of expr * expr
| Ret of expr
| Range of expr * expr
| Id of expr * expr * expr
| Enum of enum_loc_lit list
| Type
| Interface

| Pi of expr * expr fn
| Sigma of expr * expr fn
| Tree of expr * expr
| Let of bool * expr * expr fn

| For of expr * expr fn
| Interpret of expr * expr

| Subst of expr * expr fn fn * expr

(* Optional type declaration being the type of the variable introduced. *)
| Bind of expr * expr option * expr fn

(* Optional type declaration being the type of the variable introduced. *)
| Pattern of expr option * expr fn

| Decl of expr * expr

and expr = location * expr'

type toplevel' =
| Assert of expr * expr * toplevel
| AssertEq of expr * expr * expr * toplevel
| Val of location * Base.var * expr * toplevel
| Compile of string * (string * expr) list * expr * expr * toplevel
| Test of string * expr list * expr * toplevel
| Eof

and toplevel = location * toplevel'
