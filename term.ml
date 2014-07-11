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

(*

  The output of the type checker are terms, and terms can be evaluated
  to values.

  Expr ---Check_expr---> Term ---Eval---> Value.

  Terms can also be checked for correctness.
*)

open Base

(* The type of term-level functions from el to 'cod.  As term-level
   functions are abstractions, this is is simply a pair of a pattern
   and an element of 'cod. *)
type 'cod fn = pattern * 'cod

(* A monomorphic term is a term whose type can be inferred. For a
   detailed desciption of the constructors, see the corresponding
   value type.  *)
type mono =
(* Monomorphic constructors. *)
| Imm of imm  (* A special case is Refl, which is not monomorphic. *)
(* Universe sets. *)
| Pi_u of poly * poly fn
| Sigma_u of poly * poly fn
| Id_u of poly * poly * poly
| Array_u of poly * poly
| Tree_u of poly * poly
| Enum_u of enum
| Imm_set_u of size
  (* Application. *)
| App of mono * poly
| Var of var
  (* Type declaration. *)
| Poly of poly * set
  (* Destructors *)
| Fst of mono
| Snd of mono
| Enum_d of mono * set fn * poly enum_map
| Aref of mono * poly * poly
| Range of poly * poly
| Subst of mono * set fn fn * poly
| For of mono * poly fn * poly * poly fn
| Bind of mono * poly * poly fn
| Local of size * poly * poly * poly * poly
| Purify of poly * poly
| Catch of poly * poly * poly * poly * poly
| Builtin of builtin * poly list
  (* Extra construct for let binding/beta redex. *)
| Beta_mono of mono * mono fn

(* A polymorphic term can type check against many different sets, even
   in the same context. *)
and poly =
  (* A monomorphic term is vacuously polymorphic. *)
| Mono of mono
  (* Constructors *)
| Lambda of poly fn
| Pair of poly * poly
| Array_cst of poly array
| Ret of poly
| Invk of poly * poly fn
(* Extra construct for let binding/beta redex. *)
| Beta_poly of mono * poly fn
(* TODO: location for holes? *)
| Hole

(* A term-level set is just a set on the term-level. *)
and set =
| Pi of set * set fn
| Sigma of set * set fn
| Id of set * poly * poly
| Array of set * poly
| Tree of poly * poly
| Enum of enum
| Imm_set of size
| Type
| T of poly
| Hole_set

let poly_of_var x = Mono(Var x)
let mono_of_var x = Var x

let true_cst = Imm(true_imm)
let false_cst = Imm(false_imm)
let bool_set = Enum bool_enum
let bool_u = Enum_u bool_enum

let unit_cst = Imm(unit_imm)
let unit_set = Enum unit_enum
let unit_u = Enum_u unit_enum

let empty_set = Enum empty_enum
let empty_u = Enum_u empty_enum
