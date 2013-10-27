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

(* Variables are represented by strings. The empty string represents *)
(* a special variable which can be mentioned as '_' (binding *)
(* occurences), but which cannot be used (no bound occurences). *)
(* Variables can normally not be rebound; though, the special variable *)
(* '_', which is represented by the empty string, can be rebound any *)
(* number of times. This is harmless as it can never be used. *)
type var = Variable of string

let format_var : Format.formatter -> var -> unit =
  fun f -> function Variable s -> Format.fprintf f "%s" s

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

(* A variable map is a mapping from strings to things. *)
module Var_map = Map.Make(struct
  type t = var
  let compare = compare
end)
type 'a var_map = 'a Var_map.t

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

let enum_equal = Enum_set.equal
let enum_subset = Enum_set.subset
let enum_is_empty = Enum_set.is_empty

let enum_of_enum_map mp = enum_make (List.map fst (Enum_map.bindings mp))

(* Define the reverse application operator, in case we are using a
   version of OCaml older than 4.01. *)
let (|>) a b = b a

(* Returns true if the two maps have the same sets of keys, and the *)
(* respective mappings of the keys are equal in sense of the supplied *)
(* function. *)
let enum_map_equal (a : 'a enum_map) (b : 'b enum_map) (fn : 'a -> 'b -> bool)
    : bool =
  let fn _ x y =
    match x, y with
    | Some u, Some v when fn u v -> None
    | _ -> raise Not_found in
  try Enum_map.merge fn a b |> ignore; true
  with Not_found -> false

(* Returns true if the two maps have equal sets of keys *)
(* (ignoring their values). *)
let enum_map_equal_keys a b = enum_map_equal a b (fun _ _ -> true)

let bool_true_lit = Enum_lit "true"
let bool_false_lit = Enum_lit "false"
let bool_enum = enum_make [bool_true_lit; bool_false_lit]

let unit_lit = Enum_lit "()"
let unit_enum = enum_make [unit_lit]

let empty_enum = Enum_set.empty

let left_lit = Enum_lit "left"
let right_lit = Enum_lit "right"
let plus_enum = enum_make [ left_lit; right_lit ]

(* Raised when an explicit presupposition for the invocation of a *)
(* method has beed violated. *)
exception Presupposition_error

(* The type of positions (line, col). *)
type pos = int * int

(* The type of ranges, i.e., two position: from, to. *)
type range = pos * pos

(* The type of source file locations. *)
type location = string * range

(* Extend a range with a position. *)
let merge_range_with_pos (p, q) r = min p r, max q r

(* Merge two ranges. *)
let merge_ranges (p, q) (r, s) = min p r, max q s

(* Create a dummy variable from a description (maybe empty) and a position. *)
let dummy_of_pos (form:string) ((p, q):pos) =
  Variable (Printf.sprintf "#%s:%d.%d:" form p q)


let format_range(fmt:Format.formatter) (((p, q), (r, s)):range) =
  if p = r then
    if q = s then
      Format.fprintf fmt "%d.%d" p q
    else
      Format.fprintf fmt "%d.%d-%d" p q s
  else
    Format.fprintf fmt "%d.%d-%d.%d" p q r s

let file_and_range (form:string) (((p, q), (r, s)):range) =
  if p = r then
    if q = s then
      Printf.sprintf "%s:%d.%d" form p q
    else
      Printf.sprintf "%s:%d.%d-%d" form p q s
  else
    Printf.sprintf "%s:%d.%d-%d.%d" form p q r s

(* Create a dummy variable from a description (maybe empty) and a range. *)
let dummy_of_file_and_range (form:string) (r:range) =
  Variable (file_and_range form r)

(* Create a new dummy variable. *)
let newdummy : unit -> var =
  let counter = ref 1 in
  fun () ->
    let result = Variable (Format.sprintf "#d%d" !counter) in
    counter := !counter + 1;
    result
