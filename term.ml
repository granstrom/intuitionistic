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

(* The type of term-level functions from el to 'a.  As term-level             *)
(* functions are abstractions, this is is simply a pair of a variable         *)
(* and an element of 'a.                                                      *)
type 'a fn = Base.var * 'a

(* A monomorphic term is a term whose type can be inferred. For a detailed    *)
(* desciption of the constructors, see the corresponding value type.          *)
and mono =
(* Monomorphic constructors. *)
| Imm of Value.imm  (* A special case is Refl, which is not monomorphic. *)
| Pi_u of poly * poly fn
| Sigma_u of poly * poly fn
| Tree_u of poly * poly
| Id_u of poly * poly * poly
| Enum_u of Base.enum
| Imm_set_u of Value.size
  (* Application. *)
| App of mono * poly
| Var of Base.var
  (* Type declaration. *)
| Poly of poly * set
  (* Destructors *)
| Fst of mono
| Snd of mono
  (* TODO: why not Enum_map? *)
| Enum_d of mono * set fn * (Base.enum_lit * poly) list
| Range of poly * poly
| Subst of mono * set fn fn * poly
| For of mono * poly fn * poly * poly fn
| Bind of mono * poly * poly fn
| Local1 of Value.size * poly * poly * poly * mono
| Local2 of Value.size * poly * poly * poly * mono * poly fn
| Local3 of Value.size * poly * poly * poly * mono * poly * poly fn
| Purify of poly * mono
| Builtin of Value.builtin * poly list
  (* Extra construct for let binding/beta redex. *)
| BetaMono of mono * mono fn

(* A polymorphic term can type check against many different sets, *)
(* even in the same context. *)
and poly =
  (* A monomorphic term is vacuously polymorphic. *)
| Mono of mono
  (* Constructors *)
| Lambda of poly fn
| Pair of poly * poly
| Ret of poly
| Invk of poly * poly fn
  (* Extra construct for let binding/beta redex. *)
| BetaPoly of mono * poly fn

(* A term-level set is just a set on the term-level. *)
and set =
| Pi of set * set fn
| Sigma of set * set fn
| Tree of poly * poly
| Id of set * poly * poly
| Enum of Base.enum
| Imm_set of Value.size
| Type
| T of poly
  (* Extra construct for let binding/beta redex. *)
| BetaSet of mono * set fn

let true_cst = Imm(Value.Enum_cst(Base.bool_enum, Base.bool_true_lit))
let false_cst = Imm(Value.Enum_cst (Base.bool_enum, Base.bool_false_lit))
let bool_set = Enum Base.bool_enum
let bool_u = Enum_u Base.bool_enum

let unit_cst = Imm(Value.Enum_cst(Base.unit_enum, Base.unit_lit))
let unit_set = Enum Base.unit_enum
let unit_u = Enum_u Base.unit_enum

let empty_set = Enum Base.empty_enum
let empty_u = Enum_u Base.empty_enum

let left_cst = Imm(Value.Enum_cst(Base.plus_enum, Base.left_lit))
let right_cst = Imm(Value.Enum_cst (Base.plus_enum, Base.right_lit))
let plus_set = Enum Base.plus_enum
let plus_u = Enum_u Base.plus_enum

let term_lift f ids (p, a) (q, b) = f ((p, q) :: ids) a b

let rec eq_set ids uu vv =
  match uu, vv with
  | Pi(a, b), Pi(aa, bb)
  | Sigma(a, b), Sigma(aa, bb) -> eq_set ids a aa; term_lift eq_set ids b bb
  | Tree(i, a), Tree(ii, aa) ->
    eq_poly ids i ii; eq_poly ids a aa
  | Id(a, b, c), Id(aa, bb, cc) ->
    eq_set ids a aa; eq_poly ids b bb; eq_poly ids c cc
  | Enum a, Enum b when Base.enum_equal a b -> ()
  | Imm_set a, Imm_set b when a = b -> ()
  | Type, Type -> ()
  | T e, T ee -> eq_poly ids e ee
  | _ -> raise Value.Not_equal

and eq_poly ids uu vv =
  match uu, vv with
  | Mono a, Mono aa -> eq_mono ids a aa
  | Lambda b, Lambda bb -> term_lift eq_poly ids b bb
  | Lambda (x, b), Mono c ->
    let dummy = Base.newdummy () in
    eq_poly ((x, dummy) :: ids) b (Mono(App(c, Mono(Var(dummy)))))
  | Mono c, Lambda (x, b) ->
    let dummy = Base.newdummy () in
    eq_poly ((dummy, x) :: ids) (Mono(App(c, Mono(Var(dummy))))) b
  | Pair(a, b), Pair(aa, bb) -> eq_poly ids a aa; eq_poly ids b bb
  | Pair(a, b), Mono(c) -> eq_poly ids a (Mono (Fst c)); eq_poly ids b (Mono (Snd c))
  | Mono(c), Pair(a, b) -> eq_poly ids (Mono (Fst c)) a; eq_poly ids (Mono (Snd c)) b
  | Ret a, Ret aa -> eq_poly ids a aa
  | Invk(c, t), Invk(cc, tt) -> eq_poly ids c cc; term_lift eq_poly ids t tt
  | BetaPoly(a, b), BetaPoly(a2, b2) ->
    eq_mono ids a a2; term_lift eq_poly ids b b2
  | _ -> raise Value.Not_equal

and eq_mono ids uu vv =
  match uu, vv with
  | Imm a, Imm b -> Value.eq_imm a b
  | Pi_u(a, b), Pi_u(aa, bb)
  | Sigma_u(a, b), Sigma_u(aa, bb) -> eq_poly ids a aa; term_lift eq_poly ids b bb
  | Tree_u(i, a), Tree_u(ii, aa) ->
    eq_poly ids i ii; eq_poly ids a aa
  | Id_u(a, b, c), Id_u(aa, bb, cc) ->
    eq_poly ids a aa; eq_poly ids b bb; eq_poly ids c cc
  | Enum_u a, Enum_u b when Base.enum_equal a b -> ()
  | Imm_set_u a, Imm_set_u b when a = b -> ()
  | Poly(e, _A), Poly(ee, _AA) -> eq_poly ids e ee; eq_set ids _A _AA
  | Var x, Var xx ->
    begin
      ids
      |> Base.try_find (fun (y, yy) -> x = y || xx = yy)
      |> function
        | Some (y, yy) when x = y && xx = yy -> ()
        | None when x = xx -> ()
        | _ -> raise Value.Not_equal
    end
  | App(f, a), App(ff, aa) -> eq_mono ids f ff; eq_poly ids a aa
  | Fst(n), Fst(nn)
  | Snd(n), Snd(nn) -> eq_mono ids n nn
  | Enum_d(n, _C, a), Enum_d(nn, _CC, aa) ->
    begin
      eq_mono ids n nn; term_lift eq_set ids _C _CC;
      let mergefn _ u v =
	match u, v with
	| Some xx, Some yy -> eq_poly ids xx yy; None
	| _ -> raise Value.Not_equal
      in
      Base.Enum_map.merge mergefn (Base.enum_map_make a) (Base.enum_map_make aa) |> ignore
    end
  | Range(n, m), Range(nn, mm) ->
    eq_poly ids n nn; eq_poly ids m mm
  | Subst(r, _C, d), Subst(rr, _CC, dd) ->
    eq_mono ids r rr; (Base.comp term_lift term_lift) eq_set ids _C _CC; eq_poly ids d dd
  | Builtin (p, r), Builtin (p', r')
    when p = p' && List.length r = List.length r' ->
    List.iter2 (eq_poly ids) r r'
  | BetaMono(a, b), BetaMono(a', b') ->
    eq_mono ids a a'; term_lift eq_mono ids b b'
  | Bind (n, _B, f), Bind (m, _C, g) ->
    eq_mono ids n m; eq_poly ids _B _C; term_lift eq_poly ids f g
  | For (n, _U, _I, f), For (m, _V, _J, g) ->
    eq_mono ids n m; term_lift eq_poly ids _U _V;
    eq_poly ids _I _J; term_lift eq_poly ids f g
  | Local1(b, i, a, n, p),  Local1(b', i', a', n', p') when b = b' ->
    eq_poly ids i i'; eq_poly ids a a'; eq_poly ids n n'; eq_mono ids p p'
  | Local2(b, i, a, n, c, t),  Local2(b', i', a', n', c', t') when b = b' ->
    eq_poly ids i i'; eq_poly ids a a'; eq_poly ids n n'; eq_mono ids c c';
    term_lift eq_poly ids t t'
  | Local3(b, i, a, n, u, v, t),  Local3(b', i', a', n', u', v', t') when b = b' ->
    eq_poly ids i i'; eq_poly ids a a'; eq_poly ids n n'; eq_mono ids u u';
    eq_poly ids v v'; term_lift eq_poly ids t t'
  | Purify(c, m), Purify(c', m') -> eq_poly ids c c'; eq_mono ids m m'
  | _ -> raise Value.Not_equal
