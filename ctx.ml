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

type types = (bool ref * location * Value.set) var_map

(* The two maps and the set *must* have the same set of keys. *)
type ctx =
  | Internal_ctx_ctor of types * Eval.assign

(* The variable is already bound in the context when trying to bind it. *)
exception Rebound_error of location * location * var

let empty = Internal_ctx_ctor(Var_map.empty, Var_map.empty)

let assign : ctx -> Eval.assign = function Internal_ctx_ctor (_, e) -> e

let find_type x = function
  | Internal_ctx_ctor (ts, _) ->
    let r, _, t = Var_map.find x ts in
    r := true;
    t

let extend (ctx:ctx) (loc:location) (x:var) (a:Value.el) (_A:Value.set) :ctx =
  if x = Var.no then ctx
  else match ctx with
  | Internal_ctx_ctor(ts, es) ->
    begin
      try
        let _, bloc, _ = Var_map.find x ts in
        raise (Rebound_error(bloc, loc, x))
      with Not_found ->
        Internal_ctx_ctor(Var_map.add x (ref false, loc, _A) ts,
                          Var_map.add x a es)
    end

let rec extend_with_pattern (ctx:ctx) :pattern -> Value.set -> Value.el * ctx =
  function
  | Pvar(loc, x) ->
    let a = Value.el_of_var x in
    fun _A -> a, extend ctx loc x a _A
  | Ppair(p, q) ->
    function
    | Value.Sigma(_P, _Q) ->
      let x, ctx' = extend_with_pattern ctx p _P in
      let y, ctx'' = extend_with_pattern ctx' q (Value.apv _Q x) in
      Value.Pair(x, y), ctx''
    | _ -> raise Presupposition_error
