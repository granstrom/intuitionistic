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

(* Function composition a la F#. *)
let comp f g a = f (g a)

(* Similar to F-#sharp's List.tryFind. *)
let rec try_find pred =
  function
  | [] -> None
  | a :: rest when pred a -> Some a
  | _ :: rest -> try_find pred rest

type var = Var.t

(* A variable map is a mapping from strings to things. *)
module Var_map = Map.Make(struct
  type t = var
  let compare = compare
end)
type 'a var_map = 'a Var_map.t

(* An enum literal. *)
type enum_lit = Enum_lit of string

let format_enum_lit : Format.formatter -> enum_lit -> unit =
  fun f -> function Enum_lit s -> Format.fprintf f "%s" s

(* An enumeration map is a mapping from strings to things. *)
module Enum_map = Map.Make(struct
  type t = enum_lit
  let compare = compare
end)
type 'a enum_map = 'a Enum_map.t

(* An enumeration is a set of strings. *)
module Enum_set = Set.Make(
  struct
    type t = enum_lit
    let compare = compare
  end)
type enum = Enum_set.t

let format_enum (fmt:Format.formatter) (enum:enum) :unit =
  let open Format in
  match Enum_set.elements enum with
  | [] -> ()
  | Enum_lit a :: ys ->
    fprintf fmt "%s" a;
    List.iter (function Enum_lit a -> fprintf fmt ", %s" a) ys;

exception Duplicate_key of enum_lit

(* Make an enum map from an association list. *)
let rec enum_map_make : (enum_lit * 'a) list -> 'a enum_map =
  function
  | [] -> Enum_map.empty
  | (a, b) :: c ->
    let cc = enum_map_make c in
    if Enum_map.mem a cc then raise (Duplicate_key(a))
    else Enum_map.add a b cc

(* Make an enum from a list of strings. *)
let rec enum_make : enum_lit list -> enum =
  function
  | [] -> Enum_set.empty
  | a :: b ->
    let bb = enum_make b in
    if Enum_set.mem a bb then raise (Duplicate_key(a))
    else Enum_set.add a bb

let enum_of_enum_map mp =
  Enum_map.fold (fun k _ b -> Enum_set.add k b) mp Enum_set.empty

let true_lit = Enum_lit "true"
let false_lit = Enum_lit "false"
let bool_enum = enum_make [true_lit; false_lit]

let unit_lit = Enum_lit "()"
let unit_enum = enum_make [unit_lit]

let empty_enum = Enum_set.empty

(* Raised when an explicit presupposition for the invocation of a *)
(* method has beed violated. *)
exception Presupposition_error

(* The type of positions (line, col). *)
type pos = int * int

let no_pos = -1, -1

(* The type of ranges, i.e., two position: from, to. *)
type range = pos * pos

let no_range = no_pos, no_pos

(* The type of source file locations. *)
type location = string * range

let no_location = "", no_range

(* Type of variable binding patterns. *)
type pattern =
| Pvar of location * var
| Ppair of pattern * pattern

let no_pattern = Pvar(no_location, Var.no)

let format_range(fmt:Format.formatter) (((p, q), (r, s)):range) =
  if p = r then
    if q = s then
      Format.fprintf fmt "%d.%d" p q
    else
      Format.fprintf fmt "%d.%d-%d" p q s
  else
    Format.fprintf fmt "%d.%d-%d.%d" p q r s

let format_location(fmt:Format.formatter) ((l,r):location) =
  Format.fprintf fmt "%s:%a" l format_range r

let no_loc_pattern (x:var) = Pvar(no_location, x)

(* Raised when an equality check between values fails. *)
exception Not_equal

type i8 = char
type i16 = int
type i32 = int32
type i64 = int64

type size =
| I8
| I16
| I32
| I64

type builtin =
| Aeq of size
| Less of size
(* TODO: add Greater, Below, Above, Less_eq, Greater_eq, Below_eq, Above_eq. *)
| Add of size
| Sub of size
| Neg of size
| Mul of size
| Xor of size
| Or of size
| And of size
| Not of size
| Lsl of size
| Lsr of size
| Asr of size
| Sdiv of size
| Srem of size
| Cast of size * size
| Less_trans of size
| Less_antisym of size
| Aeq_prop of size
| Aeq_refl of size
| Add_commutative of size
| Add_associative of size
| Add_unit of size
| Add_inverse of size
| Mul_commutative of size
| Mul_associative of size
| Mul_unit of size
| Distributive of size
| Sub_axiom of size

type imm =
| Imm8 of i8
| Imm16 of i16
| Imm32 of i32
| Imm64 of i64
| Enum_imm of enum * enum_lit
| Refl

let true_imm = Enum_imm (bool_enum, true_lit)
let false_imm = Enum_imm (bool_enum, false_lit)
let unit_imm = Enum_imm (unit_enum, unit_lit)

let bool_of_bool x = if x then true_imm else false_imm
