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
 TODO: record the (original) binding position of the variables to
 improve error messages, e.g., for Rebound_error.
*)
type ctx_types = (Base.var * Value.set Lazy.t) list

type ctx =
  | Ctx of ctx_types * Eval.assign

(* The variable is already bound in the context when trying to bind it. *)
exception Rebound_error of ctx * Base.var

let empty = Ctx([], Eval.Nil)

let assign : ctx -> Eval.assign = function Ctx (_, e) -> e

let extend_el (ctx : ctx) (x : Base.var) (a : Value.el) (_A : Value.set Lazy.t) : ctx =
  assert (x <> Base.Variable "");
  match ctx with
  | Ctx(vs, es) ->
    begin
      match vs |> Base.try_find (fun (y, _) -> x = y) with
      | Some (_, _) -> raise (Rebound_error(ctx, x))
      | None -> ()
    end;
    Ctx((x, _A) :: vs, Eval.Assign(es, x, a))

let extend (ctx : ctx) (x : Base.var) (_A : Value.set Lazy.t) : ctx =
  extend_el ctx x (Value.el_of_var x) _A

let extend_term (ctx : ctx) (x : Base.var) (_A : Term.set) : ctx =
  extend ctx x (lazy (Eval.set (assign ctx) _A))

let extend_value (ctx : ctx) (x : Base.var) (_A : Value.set) : ctx =
  extend ctx x (lazy _A)

let extend_el_value (ctx : ctx) (x : Base.var) (a : Value.el) (_A : Value.set) : ctx =
  extend_el ctx x a (lazy _A)

let lookup x =
  assert (x <> Base.Variable "");
  function Ctx(vs, _) ->
    match vs |> Base.try_find (fun (y, _) -> x = y) with
    | Some (_, _A) -> Lazy.force _A
    | None -> raise Not_found
