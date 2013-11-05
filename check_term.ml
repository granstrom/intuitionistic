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

exception Error

let rec extend (ctx:Ctx.ctx)
    :pattern -> Value.set -> Value.el * Ctx.ctx =
  function
  | Pvar(loc, x) ->
    let a = Value.el_of_var x in
    fun _A -> a, Ctx.extend ctx loc x a _A
  | Ppair(p, q) ->
    function
    | Value.Sigma(_P, _Q) ->
      let x, ctx' = extend ctx p _P in
      let y, ctx'' = extend ctx' q (Value.apv _Q x) in
      Value.Pair(x, y), ctx''
    | _ -> raise Error

let rec extend_with_value (ctx:Ctx.ctx) (a:Value.el)
    :pattern -> Value.set -> Ctx.ctx =
  function
  | Pvar(loc, x) -> Ctx.extend ctx loc x a
  | Ppair(p, q) ->
    function
    | Value.Sigma(_P, _Q) ->
      let a' = Eval.mkFst a in
      let ctx' = extend_with_value ctx a' p _P in
      let _Q' = Value.apv _Q a' in
      let ctx'' = extend_with_value ctx' (Eval.mkSnd a) q _Q' in
      ctx''
    | _ -> raise Error

(* Check that the given set is well formed in the context. *)
let rec set (ctx : Ctx.ctx) : Term.set -> unit =
  function
  | Term.Pi (_A, (x, _B))
  | Term.Sigma (_A, (x, _B)) ->
    set ctx _A;
    let _A' = Eval.set (Ctx.assign ctx) _A in
    let _, ctx' = extend ctx x _A' in
    set ctx' _B
  | Term.Tree (_I, _A) ->
    poly ctx Eval.interface _I;
    poly ctx Value.Type _A
  | Term.Id (_A, a, b) ->
    set ctx _A;
    let __A = Eval.set (Ctx.assign ctx) _A in
    poly ctx __A a;
    poly ctx __A b
  | Term.Enum _
  | Term.Imm_set _
  | Term.Type -> ()
  | Term.Hole_set -> ()
  | Term.T p -> poly ctx Value.Type p

(* Check that the given polymorphic term is an element of the given
   (value) set in the given context. *)
and poly (ctx : Ctx.ctx) (cc : Value.set) (aa : Term.poly) : unit =
  let open Value in
  match cc, aa with
  | Pi(_A, _B), Term.Lambda(x, b) ->
    let x', ctx' = extend ctx x _A in
    poly ctx' (apv _B x') b

  | Sigma(_A, _B), Term.Pair(a, b) ->
    poly ctx _A a;
    let a' = Eval.poly (Ctx.assign ctx) a in
    poly ctx (apv _B a') b

  | Tree(_, _A), Term.Ret(a) -> poly ctx (Eval.univ _A) a

  | ((Tree(_I, _A)) as _Tree), Term.Invk(c, (x, t)) ->
    let _C      = Eval.univ (Eval.mkFst _I) in
    let _R y    = Eval.univ (Eval.mkApp (Eval.mkSnd _I) y) in
    let c'      = Eval.poly (Ctx.assign ctx) c in
    let _, ctx' = extend ctx x (_R c') in
    poly ctx _C c;
    poly ctx' _Tree t

  | Id(_A, a, b), Term.Mono(Term.Imm Refl) ->
    begin
      try
        eq_el a b
      with Not_equal -> raise Error
    end

  | _A, Term.Mono a ->
    let __B = mono ctx a in
    begin
      try
        eq_set _A __B
      with Not_equal -> raise Error
    end

  | _C, Term.Beta_poly(a, (x, b)) ->
    let _A = mono ctx a in
    let a' = Eval.mono (Ctx.assign ctx) a in
    let ctx' = extend_with_value ctx a' x _A in
    poly ctx' _C b

  | _A, Term.Hole -> ()

  | _ -> raise Error

(* Infer the set to which the given monomorphic term belongs in the
   given context. *)
and mono (ctx : Ctx.ctx) (m : Term.mono) : Value.set =
  let open Value in
  match m with
  | Term.Imm Refl -> raise Error

  | Term.Imm v -> set_of_imm v

  | Term.Pi_u (a, (x, b))

  | Term.Sigma_u (a, (x, b)) ->
    poly ctx Type a;
    let _A = Eval.univ (Eval.poly (Ctx.assign ctx) a) in
    let _, ctx' = extend ctx x _A in
    poly ctx' Type b;
    Type

  | Term.Tree_u (i, a) ->
    poly ctx Eval.interface i;
    poly ctx Type a;
    Type

  | Term.Id_u (a, b, c) ->
    poly ctx Type a;
    let _A = Eval.univ (Eval.poly (Ctx.assign ctx) a) in
    poly ctx _A b;
    poly ctx _A c;
    Type

  | Term.Enum_u u -> Type

  | Term.Imm_set_u _ -> Type

  | Term.App (f, a) ->
    begin
      match mono ctx f with
      | Pi(_A, _B) ->
        poly ctx _A a;
        apv _B (Eval.poly (Ctx.assign ctx) a)
      | _ -> raise Error
    end

  | Term.Var x ->
    begin
      try Ctx.find_type x ctx
      with Not_found -> raise Error
    end

  | Term.Poly (a, _A) ->
    set ctx _A;
    let __A = Eval.set (Ctx.assign ctx) _A in
    poly ctx __A a;
    __A

  | Term.Fst (n) ->
    begin
      match mono ctx n with
      | Sigma (_A, _B) -> _A
      | _ -> raise Error
    end

  | Term.Snd (n) ->
    begin
      match mono ctx n with
      | Sigma (_A, _B) ->
        apv _B (Eval.mkFst (Eval.mono (Ctx.assign ctx) n))
      | _ -> raise Error
    end

  | Term.Bind(n, _B, (x, b)) ->
    poly ctx Value.Type _B;
    begin
      match mono ctx n with
      | Tree(_I, _A) ->
        let rho = Ctx.assign ctx in
        let _Tree = Tree(_I, Eval.poly rho _B) in
        let _, ctx' = extend ctx x (Eval.univ _A) in
        poly ctx' _Tree b;
        _Tree
      | _ -> raise Error
    end

  | Term.For(n, (w, _U), _I, (z, b)) ->
    (*
      n |^ J => A
      U : set (w : |J|)
      I : interface
      b : I => J@z (z : |J|)
      U = J@w : type (w : |J|)
      -------------------
      for[^wU, I] (z in n) {
      b
      } |^ I => A
    *)
    begin
      let rho = Ctx.assign ctx in
      poly ctx Eval.interface _I;
      let _I' = Eval.poly rho _I in
      match mono ctx n with
      | Tree(_J, _A) ->
        let _D = Eval.univ (Eval.mkFst _J) in
        let _S x = Eval.mkApp (Eval.mkSnd _J) x in
        begin
          let _, ctx' = extend ctx w _D in
          poly ctx' Value.Type _U
        end;
        let _U' = Eval.lift Eval.poly rho (w, _U) in
        fork eq_el _U' (Fn _S);
        let z', ctx' = extend ctx z _D in
        poly ctx' (Tree (_I', (_S z'))) b;
        Tree (_I', _A)
      | _ -> raise Error
    end

  | Term.Subst(r, (x, (y, _C)), d) ->
    begin
      match mono ctx r with
      | Id(_A, a, b) ->
        let x', ctx' = extend ctx x _A in
        let _, ctx'' = extend ctx' y (Id (_A, a, x')) in
        set ctx'' _C;
        let rho = Ctx.assign ctx in
        let _C' = (comp Eval.lift Eval.lift) Eval.set rho (x, (y, _C)) in
        poly ctx (apv (apv _C' a) (Imm Refl)) d;
        apv (apv _C' b) (Eval.mono rho r)
      | _ -> raise Error
    end

  | Term.Enum_d (n, (x, _C), cs) ->
    begin
      match mono ctx n with
      | Enum c as _Enum ->
        let _, ctx' = extend ctx x _Enum in
        set ctx' _C;
        (* Verify that cs and c agree on the enum. *)
        begin
          if not (Enum_set.equal c (enum_of_enum_map cs))
          then raise Error
        end;
        let rho = Ctx.assign ctx in
        let _C' = Eval.lift Eval.set rho (x, _C) in
        Enum_map.iter
          (fun k v ->
	    poly ctx (apv _C' (Imm(Enum_imm(c, k)))) v)
          cs;
        apv _C' (Eval.mono rho n)
      | _ -> raise Error
    end

  | Term.Range (n, m) ->
    poly ctx i32_set m;
    poly ctx i32_set m;
    Tree(Pair(i32_u, Lambda(Cst unit_u)), unit_u)

  | Term.Builtin (p, rs) ->
    let n, dom, cod = Eval.builtin_dom_cod p in
    let arg = apply_type ctx n (Eval.univ dom) rs in
    Eval.univ (Value.apv cod arg)

  | Term.Beta_mono (a, (x, b)) ->
    let _A = mono ctx a in
    let a' = Eval.mono (Ctx.assign ctx) a in
    let ctx' = extend_with_value ctx a' x _A in
    mono ctx' b

  | Term.Local(st, i, a, n, p) ->
    local ctx st i a n p

  | Term.Catch(b, i, a, f, p) ->
    catch ctx b i a f p

  | Term.Purify(c, m) ->
    poly ctx Value.Type c;
    let cc = Eval.poly (Ctx.assign ctx) c in
    poly ctx (Value.Tree(Eval.empty_interface, cc)) m;
    Eval.univ cc

and local ctx st i a n p =
  let rho = Ctx.assign ctx in
  poly ctx Eval.interface i;
  let ii =  Eval.poly rho i in
  poly ctx Value.Type a;
  let aa = Eval.poly rho a in
  poly ctx (Value.Imm_set st) n;
  let newi = Eval.interface_plus ii (Eval.ref_interface st) in
  poly ctx (Value.Tree(newi, aa)) p;
  Value.Tree(ii, aa)

and catch ctx b i a f p =
  let open Value in
  let rho = Ctx.assign ctx in
  poly ctx Type b;
  let bb = Eval.poly rho b in
  poly ctx Eval.interface i;
  let ii =  Eval.poly rho i in
  poly ctx Type a;
  let aa = Eval.poly rho a in
  poly ctx (Pi(Eval.univ bb, Cst(Tree(ii, aa)))) f;
  let newi = Eval.interface_plus ii (Eval.catch_interface bb) in
  poly ctx (Tree(newi, aa)) p;
  Tree(ii, aa)

and apply_type ctx n dom args =
  match dom, args with
  | Value.Sigma(_A, _B), a :: bs ->
    poly ctx _A a;
    let aa = Eval.poly (Ctx.assign ctx) a in
    let __B = Value.apv _B aa in
    Value.Pair(aa, apply_type ctx (n-1) __B bs)
  | _A, [a] ->
    assert(n = 1);
    poly ctx _A a;
    Eval.poly (Ctx.assign ctx) a
  | _ -> raise Error
