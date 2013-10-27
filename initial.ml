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

let verify_type ctx t = Check_term.set ctx (Reify.set t)

let verify ctx a t = Check_term.poly ctx t (Reify.el a)

let rec mkctx =
  function
  | [] -> Ctx.empty
  | (x, a, _A) :: cs ->
    let ctx = mkctx cs in
    verify_type ctx _A;
    verify ctx a _A;
    Ctx.extend_el_value ctx (Base.Variable x) a _A

let mkstruct lst =
  let open Value in
  let lit x = Base.Enum_lit x in
  let types = lst |> List.map (fun (x, _, z) -> lit x, z) |> Base.enum_map_make in
  let values = lst |> List.map (fun (x, y, _) -> lit x, y) |> Base.enum_map_make in
  let cod = Fn(fun x -> Eval.univ (Eval.mkEnum_d x (Cst Type) types)) in
  let enum = Enum (Base.enum_of_enum_map values) in
  lambda(fun x -> Eval.mkEnum_d x cod values), Pi(enum, cod)

let builtin_struct lst =
  lst |> List.map (fun (x, y) -> let v, t = Eval.builtin_val_type y in x, v, t) |> mkstruct

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
      "ior"   , Ior x;
      "and"   , And x;
      "not"   , Not x;

      "lsl"   , Lsl x;
      "lsr"   , Lsr x;
      "asr"   , Asr x;

      "(<)"   , Less x;
      "(==)"  , Aeq x;

      "to_i8" , Sext (x, I8);
      "to_i16" , Sext (x, I16);
      "to_i32" , Sext (x, I32);
      "to_i64" , Sext (x, I64);

      "less_trans", LessTrans x;
      "less_antisym", LessAntisym x;
      "eq_prop", AeqProp x;
      "eq_refl", AeqRefl x;
      "add_comm", AddCommutative x;
      "add_assoc", AddAssociative x;
      "add_unit", AddUnit x;
      "add_inv", AddInverse x;
      "mul_comm", MulCommutative x;
      "mul_assoc", MulAssociative x;
      "mul_unit", MulUnit x;
      "dist", Distributive x;
      "sub_axiom", SubAxiom x;
    ] in
  name, a, _A

let tree p = Value.Tree_u(Eval.mkFst p, Eval.mkSnd p)
let split f = Value.lambda(fun x -> f (Eval.mkFst x) (Eval.mkSnd x))
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
    "cmd"   , lambda(Eval.mkFst) , Pi(Eval.interface, (Cst Type));
    "res"   , res                , res_type;
    "call2" , call               , call_type;
    "(=>)"  , lambda(tree)       , Pi(Sigma(Eval.interface, Cst Type), (Cst Type));
    mod_i "mod8" Value.I8;
    mod_i "mod16" Value.I16;
    mod_i "mod32" Value.I32;
    mod_i "mod64" Value.I64;
    mk_ref "new_i8" Value.I8;
    mk_ref "new_i16" Value.I16;
    mk_ref "new_i32" Value.I32;
    mk_ref "new_i64" Value.I64;
]
