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

(* The type of value-level functions from el to 'cod. *)
type 'cod fn =
| Fn of (el -> 'cod)
| Cst of 'cod

(* The type of value-level elements of sets. *)
and el =
(* Immediate constant. *)
| Imm of imm
(* The universe code for the Pi set. *)
| Pi_u of el * el fn
(* The universe code for the Sigma set. *)
| Sigma_u of el * el fn
(* The universe code for the Id set. *)
| Id_u of el * el * el
(* The universe code for the Tree set. *)
| Tree_u of el * el
(* The universe code for an enumerated set. *)
| Enum_u of enum
(* The unverse code for set of immediates. *)
| Imm_set_u of size
(* Canonical element of the Pi set. *)
| Lambda of el fn
(* Canonical element of the Sigma set. *)
| Pair of el * el
(* Canonical element on return form of the Tree set. *)
| Ret of el
(* Canonical element on invoke form of the Tree set. *)
| Invk of el * el fn
(* Noncanonical value-level element. *)
| Neut of neut
(* A 'hole' has the property that destructor(hole) = hole. A hole is
   equal to anything else. *)
| Hole

(* The type of value-level neutral elements of sets. *)
and neut =
(* Variable. *)
| Var of var
(* Application - destructor of Pi set. *)
| App of neut * el
(* First destructor of Sigma set. *)
| Fst of neut
(* Second destructor of Sigma set. *)
| Snd of neut
(* Destructor of enumerated set. *)
| Enum_d of neut * set fn * el Lazy.t enum_map
(* Destructor of Id set. *)
| Subst of neut * set fn fn * el
(* Lifting of component. *)
| For of neut * el fn * el * el fn
(* Bind operation on programs. *)
| Bind of neut * el * el fn
(* Range of integers. *)
| Range1 of neut * el
| Range2 of int32 * neut
(* local(sz, i, a, init, p), where p is netural. *)
| Local of size * el * el * el * component
(* Purify. *)
| Purify of el * neut
(* catch(B, I, A, f, p), where p is neutral. *)
| Catch of el * el * el * el * component
(* Builtin primitive operation. *)
| Builtin of builtin * imm list * neut * el list

and component =
(* Neutral object of type meth { C1:I1, ..., Cn:In } => A. *)
| Component1 of neut
(* Neutral object of pair type. *)
| Component2 of neut * el fn
(* Neutral object of enum type. *)
| Component3 of neut * el * el fn

(* The type of value-level sets. *)
and set =
(* The Pi set of functions. *)
| Pi of set * set fn
(* The Sigma set of pairs. *)
| Sigma of set * set fn
(* The Id set of equality proofs. *)
| Id of set * el * el
(* The Tree set of programs (interface * type). *)
| Tree of el * el
(* Enumerated sets. *)
| Enum of enum
(* Sets of immedate values. *)
| Imm_set of size
(* The universe of sets. *)
| Type
(* Decoding of a code for a set. *)
| T of neut
(* An hole that is a set. *)
| Hole_set

(* Create an element of the specified variable. *)
let el_of_var (x : var) : el = Neut (Var x)

(* Crate a new dummy element. *)
let dummy_el () = el_of_var (Var.dummy ())

(* Create a new element from the given pattern. *)
let rec el_of_pattern = function
  | Pvar (_, var) ->
    assert(var <> Var.no);
    Neut(Var(var))
  | Ppair(p, q) -> Pair(el_of_pattern p, el_of_pattern q)

(* Apply the given function to the given value. *)
let apv (f : 'a fn) (a : el) : 'a =
  match f with
  | Fn(g) -> g a
  | Cst(c) -> c

(* Apply the given function to the given lazy value. *)
let ap (f : 'a fn) (a : el lazy_t) : 'a =
  match f with
  | Fn(g) -> g (Lazy.force a)
  | Cst(c) -> c

(* Precompose the function f with the function g. *)
let precomp (f : 'a -> 'b) (g : 'a fn)  : 'b fn =
  match g with
  | Cst(c) -> Cst(f c)
  | Fn(h) -> Fn(fun x -> f (h x))

let true_cst = Imm(true_imm)
let false_cst = Imm(false_imm)
let bool_set = Enum bool_enum
let bool_u = Enum_u bool_enum

let unit_cst = Imm(unit_imm)
let unit_set = Enum unit_enum
let unit_u = Enum_u unit_enum

let empty_set = Enum empty_enum
let empty_u = Enum_u empty_enum

let i64_set = Imm_set(I64)
let i32_set = Imm_set(I32)
let i16_set = Imm_set(I16)
let i8_set  = Imm_set(I8)
let i64_u = Imm_set_u(I64)
let i32_u = Imm_set_u(I32)
let i16_u = Imm_set_u(I16)
let i8_u  = Imm_set_u(I8)

let set_of_imm = function
| Imm8 _ -> i8_set
| Imm16 _ -> i16_set
| Imm32 _ -> i32_set
| Imm64 _ -> i64_set
| Enum_imm (e, _) -> Enum e
| Refl -> raise Presupposition_error

(* Apply x and y to a common dummy variable and pass the results through f. *)
let fork (f : 'a -> 'b -> 'c) (x : 'a fn) (y : 'b fn) : 'c =
  let dummy = dummy_el () in
  let dx = apv x dummy in
  let dy = apv y dummy in
  f dx dy

(* Raise a Not_equal exception if the two sets are not equal. *)
let rec eq_set (x : set) (y : set) : unit =
  match x, y with
  | Pi(a, b), Pi(aa, bb)
  | Sigma(a, b), Sigma(aa, bb) -> eq_set a aa; fork eq_set b bb
  | Tree(i, a), Tree(ii, aa) ->
    eq_el i ii; eq_el a aa
  | Id(a, b, c), Id(aa, bb, cc) -> eq_set a aa; eq_el b bb; eq_el c cc
  | Enum a, Enum b when Enum_set.equal a b -> ()
  | Imm_set a, Imm_set b when a = b -> ()
  | Type, Type -> ()
  | T n, T m -> eq_neut n m
  (* A hole is equal to any other set. *)
  | Hole_set, _
  | _, Hole_set -> ()
  | _ -> raise Not_equal

(* Raise a Not_equal exception if the two elements are not equal. *)
and eq_el (x : el) (y : el) : unit =
  match x, y with
  | Imm a, Imm b -> eq_imm a b
  | Pi_u(a, b), Pi_u(aa, bb)
  | Sigma_u(a, b), Sigma_u(aa, bb)  -> eq_el a aa; fork eq_el b bb
  | Tree_u(i, a), Tree_u(ii, aa) ->
    eq_el i ii; eq_el a aa
  | Id_u(a, b, c), Id_u(aa, bb, cc) -> eq_el a aa; eq_el b bb; eq_el c cc
  | Enum_u a, Enum_u b when Enum_set.equal a b -> ()
  | Imm_set_u a, Imm_set_u b when a = b -> ()
  | Lambda(f), Lambda(g) -> fork eq_el f g
  | Lambda(f), Neut(g) ->
    let dummy = dummy_el () in
    eq_el (apv f dummy) (Neut(App(g, dummy)))
  | Neut(g), Lambda(f) ->
    let dummy = dummy_el () in
    eq_el (Neut(App(g, dummy))) (apv f dummy)
  | Pair(a, b), Pair(aa, bb) -> eq_el a aa; eq_el b bb
  | Pair(a, b), Neut(c) -> eq_el a (Neut (Fst c)); eq_el b (Neut (Snd c))
  | Neut(c), Pair(a, b) -> eq_el (Neut (Fst c)) a; eq_el (Neut (Snd c)) b
  | Ret(a), Ret(aa) -> eq_el a aa
  | Invk(c, t), Invk(cc, tt) -> eq_el c cc; fork eq_el t tt
  | Neut(n), Neut(m) -> eq_neut n m
  | Hole, _
  | _, Hole -> ()
  | _ -> raise Not_equal

and eq_el_array (x : el array) (y : el array) : unit =
  assert(Array.length x <> Array.length y);
  (* Duh, no Array.iter2... *)
  Array.iteri (fun i yy -> eq_el (Array.get x i) yy) y

(* Raise a Not_equal exception if the two neutral elements are not equal. *)
and eq_neut (x : neut) (y : neut) : unit =
  match x, y with
  | For (n, _U, _I, f), For (m, _V, _J, g) ->
    eq_neut n m; fork eq_el _U _V;
    eq_el _I _J; fork eq_el f g
  | Bind (n, _B, f), Bind (m, _C, g) ->
    eq_neut n m; eq_el _B _C; fork eq_el f g
  | Var x, Var y when x = y -> ()
  | App(n, v), App(nn, vv) -> eq_neut n nn; eq_el v vv
  | Fst(n), Fst(nn)
  | Snd(n), Snd(nn) -> eq_neut n nn;
  | Enum_d(n, _C, a), Enum_d(nn, _CC, aa) ->
    begin
      eq_neut n nn; fork eq_set _C _CC;
      let mergefn _ u v =
	match u, v with
	| Some xx, Some yy -> eq_el (Lazy.force xx) (Lazy.force yy); None
	(* The two neuts are not equal because they have different
	   keys in the destructor function. *)
	| _ -> raise Not_equal
      in
      ignore (Enum_map.merge mergefn a aa)
    end
  | Subst(r, _C, d), Subst(rr, _CC, dd) ->
    eq_neut r rr; (comp fork fork) eq_set _C _CC; eq_el d dd
  | Builtin (p, c, n, r), Builtin (p', c', n', r')
    when p = p' &&
      List.length c = List.length c' &&
      List.length r = List.length r' ->
    begin
      List.iter2 eq_imm c c';
      eq_neut n n';
      List.iter2 eq_el r r'
    end
  | Local(sz, i, a, n, p),  Local(sz', i', a', n', p') when sz = sz' ->
    eq_el i i'; eq_el a a'; eq_el n n'; eq_component p p'
  | Purify(c1, m1), Purify(c2, m2) -> eq_el c1 c2; eq_neut m1 m2
  | Range1(n, e), Range1(nn, ee) ->
    eq_neut n nn; eq_el e ee
  | Range2(n, e), Range2(nn, ee) when n == nn -> eq_neut e ee
  | Catch(b, i, a, f, p), Catch(b', i', a', f', p') ->
    eq_el b b'; eq_el i i'; eq_el a a'; eq_el f f'; eq_component p p'
  | _ -> raise Not_equal

and eq_imm (xx:imm) (yy:imm) :unit =
  match xx, yy with
  | Imm8 x, Imm8 y when x = y -> ()
  | Imm16 x, Imm16 y when x = y -> ()
  | Imm32 x, Imm32 y when x = y -> ()
  | Imm64 x, Imm64 y when x = y -> ()
  | Enum_imm(e, Enum_lit x), Enum_imm(f, Enum_lit y)
    when Enum_set.equal e f && x = y -> ()
  | Refl, Refl -> ()
  | _ -> raise Not_equal

and eq_component (a:component) (b:component) :unit =
  match a, b with
  | Component1(n), Component1(n') ->
    eq_neut n n'
  | Component2(n, f), Component2(n', f') ->
    eq_neut n n';
    fork eq_el f f'
  | Component3(n, b, f), Component3(n', b', f') ->
    eq_neut n n';
    eq_el b b';
    fork eq_el f f'
  | _ -> raise Not_equal

(* Comparison of elements so that they can be keys of maps. *)
let el_ordinal =
  function
  | Imm(_) -> 0
  | Lambda(_) -> 1
  | Pair(_, _) -> 2
  | Ret(_) -> 3
  | Invk(_) -> 4
  | Neut(_) -> 5
  | Pi_u(_, _) -> 6
  | Sigma_u(_, _) -> 7
  | Tree_u(_, _) -> 8
  | Id_u(_, _, _) -> 9
  | Enum_u(_) -> 10
  | Imm_set_u(_) -> 11
  (* Hole cannot be compared. *)
  | Hole -> raise Presupposition_error

let neut_ordinal =
  function
  | Var(_) -> 0
  | App(_, _) -> 1
  | Fst(_) -> 2
  | Snd(_) -> 3
  | Enum_d(_, _, _) -> 4
  | Subst(_, _, _) -> 5
  | For(_, _, _, _) -> 6
  | Bind(_, _, _) -> 7
  | Range1(_, _) -> 8
  | Range2(_, _) -> 9
  | Local(_, _, _, _, _) -> 10
  | Purify(_, _) -> 11
  | Catch(_, _, _, _, _) -> 12
  | Builtin(_, _, _, _) -> 13

let component_ordinal = function
  | Component1(_) -> 0
  | Component2(_, _) -> 1
  | Component3(_, _, _) -> 2

let rec cmpfold =
  function
  | [] -> 0
  | x :: xs ->
    let xx = Lazy.force x in
    if xx = 0 then  cmpfold xs
    else xx

let rec compare_el (x : el) (y : el) : int =
  match x, y with
  | Imm a, Imm b -> compare a b
  | Pi_u(a, b), Pi_u(aa, bb)
  | Sigma_u(a, b), Sigma_u(aa, bb)  ->
    cmpfold [lazy (compare_el a aa); lazy (fork compare_el b bb)]
  | Tree_u(i, a), Tree_u(ii, aa) ->
    cmpfold [lazy (compare_el i ii); lazy (compare_el a aa)]
  | Id_u(a, b, c), Id_u(aa, bb, cc) ->
    cmpfold [lazy (compare_el a aa);
             lazy (compare_el b bb);
             lazy (compare_el c cc)]
  | Enum_u a, Enum_u b -> Enum_set.compare a b
  | Imm_set_u a, Imm_set_u b -> compare a b
  | Lambda(f), Lambda(g) -> fork compare_el f g
  | Lambda(f), Neut(g) ->
    let dummy = dummy_el () in
    compare_el (apv f dummy) (Neut(App(g, dummy)))
  | Neut(g), Lambda(f) ->
    let dummy = dummy_el () in
    compare_el (Neut(App(g, dummy))) (apv f dummy)
  | Pair(a, b), Pair(aa, bb) ->
    cmpfold [lazy (compare_el a aa); lazy (compare_el b bb)];
  | Pair(a, b), Neut(c) ->
    cmpfold [lazy (compare_el a (Neut (Fst c)));
             lazy (compare_el b (Neut (Snd c)))]
  | Neut(c), Pair(a, b) ->
    cmpfold [lazy (compare_el (Neut (Fst c)) a);
             lazy (compare_el (Neut (Snd c)) b)]
  | Ret(a), Ret(aa) -> compare_el a aa
  | Invk(c, t), Invk(cc, tt) ->
    cmpfold [lazy (compare_el c cc); lazy (fork compare_el t tt)]
  | Neut(n), Neut(m) -> compare_neut n m
  | _ ->
    let xx = el_ordinal x in
    let yy = el_ordinal y in
    assert(xx <> yy);
    compare xx yy

and compare_neut (x : neut) (y : neut) : int =
  match x, y with
  | For (n, _, _, f), For (m, _, _, g) ->
    cmpfold [lazy (compare_neut n m); lazy (fork compare_el f g)]
  | Bind (n, _, f), Bind (m, _, g) ->
    cmpfold [lazy (compare_neut n m); lazy (fork compare_el f g)]
  | Var x, Var y -> compare x y
  | App(n, v), App(nn, vv) ->
    cmpfold [lazy (compare_neut n nn); lazy (compare_el v vv)]
  | Fst(n), Fst(nn)
  | Snd(n), Snd(nn) -> compare_neut n nn
  | Enum_d(n, _, a), Enum_d(nn, _, aa) ->
    let cmplazy x y = compare_el (Lazy.force x) (Lazy.force y) in
    cmpfold [lazy (compare_neut n nn);
             lazy (Enum_map.compare cmplazy a aa)]
  | Subst(r, _, d), Subst(rr, _, dd) ->
    cmpfold [lazy (compare_neut r rr); lazy (compare_el d dd)]
  | Builtin (p, c, n, r), Builtin (p', c', n', r') ->
    cmpfold [lazy (compare p p');
             lazy (compare (List.length c) (List.length c'));
             lazy (cmpfold (List.map Lazy.from_val (List.map2 compare c c')));
             lazy (compare_neut n n');
             lazy (compare (List.length r) (List.length r'));
             lazy (cmpfold (List.map2 (fun x y -> lazy (compare_el x y)) r r'))]
  | Local(b, _, _, n, p),  Local(b', _, _, n', p') ->
    cmpfold [lazy (compare b b');
             lazy (compare_el n n');
             lazy (compare_component p p')]
  | Catch(b, _, _, f, p),  Catch(b', _, _, f', p') ->
    cmpfold [lazy (compare_el b b');
             lazy (compare_el f f');
             lazy (compare_component p p')]
  | Range1(n, e), Range1(nn, ee) ->
    cmpfold [lazy (compare_neut n nn);
             lazy (compare_el e ee)]
  | Range2(n, e), Range2(nn, ee) ->
    cmpfold [lazy (compare n nn);
             lazy (compare_neut e ee)]
  | Purify(_, m), Purify(_, m') -> compare_neut m m'
  | _ ->
    let xx = neut_ordinal x in
    let yy = neut_ordinal y in
    assert(xx <> yy);
    compare xx yy

and compare_component (a:component) (b:component) :int =
  match a, b with
  | Component1(n), Component1(n') ->
    compare_neut n n'
  | Component2(n, f), Component2(n', f') ->
    cmpfold [lazy (compare_neut n n');
             lazy (fork compare_el f f')]
  | Component3(n, b, f), Component3(n', b', f') ->
    cmpfold [lazy (compare_neut n n');
             lazy (compare_el b b');
             lazy (fork compare_el f f')]
  | _ ->
    let xx = component_ordinal a in
    let yy = component_ordinal b in
    assert(xx <> yy);
    compare xx yy

and compare_arrays i n ar1 ar2 =
  if i = n then 0
  else
    let t = compare_el (Array.get ar1 i) (Array.get ar2 i) in
    if t <> 0 then t
    else compare_arrays (i + 1) n ar1 ar2
