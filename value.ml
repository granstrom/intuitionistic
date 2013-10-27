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
| Add of size
| Sub of size
| Neg of size
| Mul of size
| Xor of size
| Ior of size
| And of size
| Not of size
| Lsl of size
| Lsr of size
| Asr of size
| Sdiv of size
| Srem of size
| Sext of size * size
| LessTrans of size
| LessAntisym of size
| AeqProp of size
| AeqRefl of size
| AddCommutative of size
| AddAssociative of size
| AddUnit of size
| AddInverse of size
| MulCommutative of size
| MulAssociative of size
| MulUnit of size
| Distributive of size
| SubAxiom of size

type imm =
| Imm8 of i8
| Imm16 of i16
| Imm32 of i32
| Imm64 of i64
| Enum_cst of Base.enum * Base.enum_lit
| Refl

(* The type of value-level functions from el to 'cod. *)
and 'cod fn =
(* Non-constant function. *)
| Fn of (el -> 'cod)
(* Constant function: quite common in dependent type theory. *)
| Cst of 'cod

(* The type of value-level elements of sets. *)
and el =
(* Immediate constant. *)
| Imm of imm
(* The universe code for the Pi set. *)
| Pi_u of el * el fn
(* The universe code for the Sigma set. *)
| Sigma_u of el * el fn
(* The universe code for the Tree set. *)
| Tree_u of el * el
(* The universe code for the Id set. *)
| Id_u of el * el * el
(* The universe code for an enumerated set. *)
| Enum_u of Base.enum
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

(* The type of value-level neutral elements of sets. *)
and neut =
(* Variable. *)
| Var of Base.var
(* Application - destructor of Pi set. *)
| App of neut * el
(* First destructor of Sigma set. *)
| Fst of neut
(* Second destructor of Sigma set. *)
| Snd of neut
(* Destructor of enumerated set. *)
| Enum_d of neut * set fn * el Base.enum_map
(* Destructor of Id set. *)
| Subst of neut * set fn fn * el
(* Lifting of component. *)
| For of neut * el fn * el * el fn
(* Bind operation on programs. *)
| Bind of neut * el * el fn
(* Range of integers. *)
| Range1 of neut * el
| Range2 of int32 * neut
(* TODO: permit enums for local variables.                                    *)
(* Local mutable variable.                                                    *)
(* 	fun(b immediate, i interface, a type, n b,                            *)
(*            p meth { left i, right meth(_ b->b)b } => a)                    *)
(* 	:i => a                                                               *)
(* local1(b, i, a, n, p), where p is netural.                                 *)
| Local1 of size * el * el * el * neut
(* local2(b, i, a, n, c, t), where p = invk(c, t)                             *)
| Local2 of size * el * el * el * neut * el fn
(* local3(b, i, a, n, u, v, t), where p = invk((u, v), t)                     *)
| Local3 of size * el * el * el * neut * el * el fn
(* Purify                                                                     *)
| Purify of el * neut
(* Builtin primitive operation, working on immedaites and reflexivity
   proofs. *)
| Builtin of builtin * imm list * neut * el list

(* The type of value-level sets. *)
and set =
(* The Pi set of functions. *)
| Pi of set * set fn
(* The Sigma set of pairs. *)
| Sigma of set * set fn
(* The Tree set of programs (interface * type). *)
| Tree of el * el
(* The Id set of equality proofs. *)
| Id of set * el * el
(* Enumerated sets. *)
| Enum of Base.enum
(* Sets of immedate values. *)
| Imm_set of size
(* The universe of sets. *)
| Type
(* Decoding of a code for a set. *)
| T of neut

(* Create an element of the specified variable. *)
let el_of_var (x : Base.var) : el = Neut (Var x)

(* Apply the given function to the given value. *)
let apv (f : 'a fn) (a : el) : 'a =
  match f with
  | Fn g -> g a
  | Cst c -> c

(* Apply the given function to the given lazy value. *)
let ap (f : 'a fn) (a : el lazy_t) : 'a =
  match f with
  | Fn g -> g (Lazy.force a)
  | Cst c -> c

(* Precompose the function f with the function g. *)
let precomp (f : 'a -> 'b) (g : 'a fn)  : 'b fn =
  match g with
  | Cst c -> Cst(f c)
  | Fn h -> Fn(fun x -> f (h x))

let true_cst = Imm(Enum_cst (Base.bool_enum, Base.bool_true_lit))
let false_cst = Imm(Enum_cst (Base.bool_enum, Base.bool_false_lit))
let bool_set = Enum Base.bool_enum
let bool_u = Enum_u Base.bool_enum

let unit_cst = Imm(Enum_cst (Base.unit_enum, Base.unit_lit))
let unit_set = Enum Base.unit_enum
let unit_u = Enum_u Base.unit_enum

let empty_set = Enum Base.empty_enum
let empty_u = Enum_u Base.empty_enum

let left_cst = Imm(Enum_cst (Base.plus_enum, Base.left_lit))
let right_cst = Imm(Enum_cst (Base.plus_enum, Base.right_lit))
let plus_set = Enum Base.plus_enum
let plus_u = Enum_u Base.plus_enum

let lambda f = Lambda(Fn f)
let lambdac f = Lambda(Cst f)

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
| Enum_cst (e, _) -> Enum e
| Refl -> raise Base.Presupposition_error

let newdummy () = Neut(Var (Base.newdummy ()))

(* Apply x and y to a common dummy variable and pass the results through f. *)
let fork (f : 'a -> 'b -> 'c) (x : 'a fn) (y : 'b fn) : 'c =
  let dummy = newdummy () in
  let dx = apv x dummy in
  let dy = apv y dummy in
  f dx dy

(* Raised when an equality check between values fails. *)
exception Not_equal

(* Raise a Not_equal exception if the two sets are not equal. *)
let rec eq_set (x : set) (y : set) : unit =
  match x, y with
  | Pi(a, b), Pi(aa, bb)
  | Sigma(a, b), Sigma(aa, bb) -> eq_set a aa; fork eq_set b bb
  | Tree(i, a), Tree(ii, aa) ->
    eq_el i ii; eq_el a aa
  | Id(a, b, c), Id(aa, bb, cc) -> eq_set a aa; eq_el b bb; eq_el c cc
  | Enum a, Enum b when Base.enum_equal a b -> ()
  | Imm_set a, Imm_set b when a = b -> ()
  | Type, Type -> ()
  | T n, T m -> eq_neut n m
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
  | Enum_u a, Enum_u b when Base.enum_equal a b -> ()
  | Imm_set_u a, Imm_set_u b when a = b -> ()
  | Lambda(f), Lambda(g) -> fork eq_el f g
  | Lambda(f), Neut(g) ->
    let dummy = newdummy () in
    eq_el (apv f dummy) (Neut(App(g, dummy)))
  | Neut(g), Lambda(f) ->
    let dummy = newdummy () in
    eq_el (Neut(App(g, dummy))) (apv f dummy)
  | Pair(a, b), Pair(aa, bb) -> eq_el a aa; eq_el b bb
  | Pair(a, b), Neut(c) -> eq_el a (Neut (Fst c)); eq_el b (Neut (Snd c))
  | Neut(c), Pair(a, b) -> eq_el (Neut (Fst c)) a; eq_el (Neut (Snd c)) b
  | Ret(a), Ret(aa) -> eq_el a aa
  | Invk(c, t), Invk(cc, tt) -> eq_el c cc; fork eq_el t tt
  | Neut(n), Neut(m) -> eq_neut n m
  | _ -> raise Not_equal

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
	| Some xx, Some yy -> eq_el xx yy; None
	(* The two neuts are not equal because they have different
	   keys in the destructor function. *)
	| _ -> raise Not_equal
      in
      Base.Enum_map.merge mergefn a aa |> ignore
    end
  | Subst(r, _C, d), Subst(rr, _CC, dd) ->
    eq_neut r rr; (Base.comp fork fork) eq_set _C _CC; eq_el d dd
  | Builtin (p, c, n, r), Builtin (p', c', n', r')
    when p = p' &&
      List.length c = List.length c' &&
      List.length r = List.length r' ->
    begin
      List.iter2 eq_imm c c';
      eq_neut n n';
      List.iter2 eq_el r r'
    end
  | Local1(b, i, a, n, p),  Local1(b', i', a', n', p') when b = b' ->
    eq_el i i'; eq_el a a'; eq_el n n'; eq_neut p p'
  | Local2(b, i, a, n, c, t),  Local2(b', i', a', n', c', t') when b = b' ->
    eq_el i i'; eq_el a a'; eq_el n n'; eq_neut c c'; fork eq_el t t'
  | Local3(b, i, a, n, u, v, t),  Local3(b', i', a', n', u', v', t') when b = b' ->
    eq_el i i'; eq_el a a'; eq_el n n'; eq_neut u u'; eq_el v v'; fork eq_el t t'
  | Purify(c1, m1), Purify(c2, m2) -> eq_el c1 c2; eq_neut m1 m2
  | _ -> raise Not_equal

and eq_imm (xx:imm) (yy:imm) : unit =
  match xx, yy with
  | Imm8 x, Imm8 y when x = y -> ()
  | Imm16 x, Imm16 y when x = y -> ()
  | Imm32 x, Imm32 y when x = y -> ()
  | Imm64 x, Imm64 y when x = y -> ()
  | Enum_cst(e, Base.Enum_lit x), Enum_cst(f, Base.Enum_lit y)
    when Base.enum_equal e f && x = y -> ()
  | Refl, Refl -> ()
  | _ -> raise Not_equal

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
  | Local1(_, _, _, _, _) -> 10
  | Local2(_, _, _, _, _, _) -> 11
  | Local3(_, _, _, _, _, _, _) -> 12
  | Purify(_, _) -> 13
  | Builtin(_, _, _, _) -> 14

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
  | Enum_u a, Enum_u b -> Base.Enum_set.compare a b
  | Imm_set_u a, Imm_set_u b -> compare a b
  | Lambda(f), Lambda(g) -> fork compare_el f g
  | Lambda(f), Neut(g) ->
    let dummy = newdummy () in
    compare_el (apv f dummy) (Neut(App(g, dummy)))
  | Neut(g), Lambda(f) ->
    let dummy = newdummy () in
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
    cmpfold [lazy (compare_neut n nn);
             lazy (Base.Enum_map.compare compare_el a aa)]
  | Subst(r, _, d), Subst(rr, _, dd) ->
    cmpfold [lazy (compare_neut r rr); lazy (compare_el d dd)]
  | Builtin (p, c, n, r), Builtin (p', c', n', r') ->
    cmpfold [lazy (compare p p');
             lazy (compare (List.length c) (List.length c'));
             lazy (cmpfold (List.map Lazy.from_val (List.map2 compare c c')));
             lazy (compare_neut n n');
             lazy (compare (List.length r) (List.length r'));
             lazy (cmpfold (List.map2 (fun x y -> lazy (compare_el x y)) r r'))]
  | Local1(b, _, _, n, p),  Local1(b', _, _, n', p') ->
    cmpfold [lazy (compare b b');
             lazy (compare_el n n');
             lazy (compare_neut p p')]
  | Local2(b, _, _, n, c, t),  Local2(b', _, _, n', c', t') when b = b' ->
    cmpfold [lazy (compare b b');
             lazy (compare_el n n');
             lazy (compare_neut c c');
             lazy (fork compare_el t t')]
  | Local3(b, _, _, n, u, v, t),  Local3(b', _, _, n', u', v', t') when b = b' ->
    cmpfold [lazy (compare b b');
             lazy (compare_el n n');
             lazy (compare_neut u u');
             lazy (compare_el v v');
             lazy (fork compare_el t t')]
  | Purify(_, m), Purify(_, m') -> compare_neut m m'
  | _ ->
    let xx = neut_ordinal x in
    let yy = neut_ordinal y in
    assert(xx <> yy);
    compare xx yy
