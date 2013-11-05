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

let verify_type ctx t = Check_term.set ctx (Reify.set t)

let verify ctx a t = Check_term.poly ctx t (Reify.el a)

let rec mkctx =
  function
  | [] -> Ctx.empty
  | (x, a, _A) :: cs ->
    (* Format.printf "adding %s\n" x; *)
    let ctx = mkctx cs in
    verify_type ctx _A;
    verify ctx a _A;
    Ctx.extend ctx no_location (Var.of_string x) a _A

let mkstruct lst =
  let open Value in
  let lit x = Enum_lit x in
  let types = enum_map_make (List.map (fun (x, _, z) -> lit x, z) lst) in
  let values = enum_map_make (List.map (fun (x, y, _) -> lit x, y) lst) in
  let cod = Fn(fun x -> Eval.univ (Eval.mkEnum_d x (Cst Type) types)) in
  let enum = Enum (enum_of_enum_map values) in
  Eval.lambda(fun x -> Eval.mkEnum_d x cod values), Pi(enum, cod)

let builtin_struct lst =
  mkstruct (
    List.map (fun (x, y) ->
      let v, t = Eval.builtin_val_type y in x, lazy v, lazy t)
      lst)

let mod_i name x =
  let open Value in
  let a, _A =
  builtin_struct [
      "(+)"   , Add x;
      "(-)"   , Sub x;
      "(-.)"  , Neg x;
      "(*)"   , Mul x;
      "srem"  , Srem x;
      "sdiv"  , Sdiv x;
      "xor"   , Xor x;
      "ior"   , Or x;
      "and"   , And x;
      "not"   , Not x;

      "lsl"   , Lsl x;
      "lsr"   , Lsr x;
      "asr"   , Asr x;

      "(<)"   , Less x;
      "(==)"  , Aeq x;

      "to_i8" , Cast (x, I8);
      "to_i16" , Cast (x, I16);
      "to_i32" , Cast (x, I32);
      "to_i64" , Cast (x, I64);

      "less_trans", Less_trans x;
      "less_antisym", Less_antisym x;
      "eq_prop", Aeq_prop x;
      "eq_refl", Aeq_refl x;
      "add_comm", Add_commutative x;
      "add_assoc", Add_associative x;
      "add_unit", Add_unit x;
      "add_inv", Add_inverse x;
      "mul_comm", Mul_commutative x;
      "mul_assoc", Mul_associative x;
      "mul_unit", Mul_unit x;
      "dist", Distributive x;
      "sub_axiom", Sub_axiom x;
    ] in
  name, a, _A

let tree p = Value.Tree_u(Eval.mkFst p, Eval.mkSnd p)
let split f = Eval.lambda(fun x -> f (Eval.mkFst x) (Eval.mkSnd x))
let res = split (fun y z -> Eval.mkApp (Eval.mkSnd y) z)
let res_type =
  let open Value in
  Pi(Sigma(Eval.interface, Fn(fun x -> Eval.univ (Eval.mkFst x))),
     Cst Type)

let call_type =
  let open Value in
  Pi(Sigma(Eval.interface, Fn(fun x -> (Eval.univ(Eval.mkFst x)))),
           Fn(fun p -> Tree(Eval.mkFst p, Eval.mkApp res p)))
let call = split (fun _ y -> Value.Invk(y, Value.Fn(fun z -> Value.Ret z)))

let mk_ref name i = name, Eval.new_ref i, Eval.new_ref_type i

let ctx =
  let open Value in
  mkctx [
    "void"  , unit_u             , Type;
    "bool"  , bool_u             , Type;
    "true"  , true_cst           , bool_set;
    "false" , false_cst          , bool_set;
    "i64"   , i64_u              , Type;
    "i32"   , i32_u              , Type;
    "i16"   , i16_u              , Type;
    "i8"    , i8_u               , Type;
    "cmd"   , Eval.lambda(Eval.mkFst) , Pi(Eval.interface, (Cst Type));
    "res"   , res                , res_type;
    "call2" , call               , call_type;
    "(=>)"  , Eval.lambda(tree)  , Pi(Sigma(Eval.interface, Cst Type), (Cst Type));
    "catch" , Eval.catch_val     , Eval.catch_type;
    mod_i "mod8" I8;
    mod_i "mod16" I16;
    mod_i "mod32" I32;
    mod_i "mod64" I64;
    mk_ref "new_i8" I8;
    mk_ref "new_i16" I16;
    mk_ref "new_i32" I32;
    mk_ref "new_i64" I64;
]
