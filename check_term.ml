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

exception Error

(* Check that the given set is well formed in the context. *)
let rec set (ctx : Ctx.ctx) : Term.set -> unit =
  function
  | Term.Pi (_A, (x, _B))
  | Term.Sigma (_A, (x, _B)) ->
    set ctx _A;
    set (Ctx.extend_term ctx x _A) _B
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
  | Term.T p -> poly ctx Value.Type p
  | Term.BetaSet(a, (x, b)) ->
    let _A = mono ctx a in
    let aa = Eval.mono (Ctx.assign ctx) a in
    (* TODO: support lazy evaluation of aa. *)
    set (Ctx.extend_el_value ctx x aa _A) b

(* Check that the given polymorphic term is an element of the given
   (value) set in the given context. *)
and poly (ctx : Ctx.ctx) (cc : Value.set) (aa : Term.poly) : unit =
  let open Value in
  match cc, aa with
  | Pi(_A, _B), Term.Lambda(x, b) ->
    poly (Ctx.extend_value ctx x _A) (apv _B (el_of_var x)) b

  | Sigma(_A, _B), Term.Pair(a, b) ->
    poly ctx _A a;
    poly ctx (ap _B (lazy (Eval.poly (Ctx.assign ctx) a))) b

  | Tree(_, _A), Term.Ret(a) -> poly ctx (Eval.univ _A) a

  | ((Tree(_I, _A)) as _Tree), Term.Invk(c, (x, t)) ->
    let _C = Eval.univ (Eval.mkFst _I) in
    let _R y = Eval.univ (Eval.mkApp (Eval.mkSnd _I) y) in
    poly ctx _C c;
    poly
      (Ctx.extend ctx x (lazy (_R (Eval.poly (Ctx.assign ctx) c))))
      _Tree t

  | Id(_A, a, b), Term.Mono(Term.Imm Value.Refl) ->
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

  | _C, Term.BetaPoly(a, (x, b)) ->
    let _A = mono ctx a in
    let aa = Eval.mono (Ctx.assign ctx) a in
    (* TODO: support lazy evaluatio of aa. *)
    poly (Ctx.extend_el_value ctx x aa _A) _C b

  | _ -> raise Error

(* Infer the set to which the given monomorphic term belongs in the
   given context. *)
and mono (ctx : Ctx.ctx) (m : Term.mono) : Value.set =
  let open Value in
  match m with
  | Term.Imm Value.Refl -> raise Error
  | Term.Imm v -> set_of_imm v
  | Term.Pi_u (a, (x, b))
  | Term.Sigma_u (a, (x, b)) ->
    poly ctx Type a;
    poly (Ctx.extend ctx x (lazy (Eval.univ (Eval.poly (Ctx.assign ctx) a))))
      Type b;
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
        ap _B (lazy (Eval.poly (Ctx.assign ctx) a))
      | _ -> raise Error
    end
  | Term.Var x ->
    begin
      try Ctx.lookup x ctx
      with Not_found -> raise Error
    end
  | Term.Poly (a, _A) ->
    set ctx _A;
    let __A = Eval.set (Ctx.assign ctx) _A in
    poly ctx __A a;
    __A
  (* Destructors *)
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
        ap _B (lazy (Eval.mkFst (Eval.mono (Ctx.assign ctx) n)))
      | _ -> raise Error
    end
  | Term.Bind(n, _B, (x, b)) ->
    poly ctx Value.Type _B;
    begin
      match mono ctx n with
      | Tree(_I, _A) ->
        let rho = Ctx.assign ctx in
        let _Tree = Tree(_I, Eval.poly rho _B) in
        poly (Ctx.extend_value ctx x (Eval.univ _A)) _Tree b;
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
      let __I = Eval.poly rho _I in
      match mono ctx n with
      | Tree(_J, _A) ->
        let _D = Eval.univ (Eval.mkFst _J) in
        let _S x = Eval.mkApp (Eval.mkSnd _J) x in
        poly (Ctx.extend_value ctx w _D) Value.Type _U;
        let __U = Eval.lift Eval.poly rho (w, _U) in
        fork eq_el __U (Fn _S);
        poly
          (Ctx.extend_value ctx z _D)
          (Tree (__I, (_S (el_of_var z))))
          b;
        Tree (__I, _A)
      | _ -> raise Error
    end
  | Term.Subst(r, (x, (y, _C)), d) ->
    begin
      match mono ctx r with
      | Id(__A, aa, bb) ->
        set (Ctx.extend_value (Ctx.extend_value ctx x __A) y
	       (Id (__A, aa, el_of_var x)))
          _C;
        let rho = Ctx.assign ctx in
        let __C = (Base.comp Eval.lift Eval.lift) Eval.set rho (x, (y, _C)) in
        poly ctx (apv (apv __C aa) (Imm(Value.Refl))) d;
        ap (apv __C bb) (lazy (Eval.mono rho r) )
      | _ -> raise Error
    end
  | Term.Enum_d (n, (x, _C), cs) ->
    begin
      match mono ctx n with
      | Enum c as _Enum ->
        set (Ctx.extend_value ctx x _Enum) _C;
        (* Verify that cs and c agree on the enum. *)
        begin
          if not (Base.enum_equal (Base.enum_make (List.map fst cs)) c)
          then raise Error
        end;
        let rho = Ctx.assign ctx in
        let __C = Eval.lift Eval.set rho (x, _C) in
        List.iter
          (fun (k, v) ->
	    poly ctx (apv __C (Imm(Value.Enum_cst (c, k)))) v)
          cs;
        ap __C (lazy (Eval.mono rho n))
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
  | Term.BetaMono (a, (x, b)) ->
    let _A = mono ctx a in
    let aa = Eval.mono (Ctx.assign ctx) a in
    (* TODO: support lazy evaluatio of aa. *)
    mono (Ctx.extend_el_value ctx x aa _A) b
  | Term.Local1(st, i, a, n, p) ->
    let s, t = local ctx st i a n in
    poly ctx s (Term.Mono p);
    t
  | Term.Local2(st, i, a, n, u, v) ->
    let s, t = local ctx st i a n in
    poly ctx s (Term.Invk(Term.Mono u, v));
    t
  | Term.Local3(st, i, a, n, e, d, v) ->
    let s, t = local ctx st i a n in
    poly ctx s (Term.Invk(Term.Pair(Term.Mono e, d), v));
    t
  | Term.Purify(c, m) ->
    poly ctx Value.Type c;
    let cc = Eval.poly (Ctx.assign ctx) c in
    match mono ctx m with
    | Tree(Pair(Sigma_u(Enum_u e, _), _), c') when Base.Enum_set.is_empty e ->
      begin
        try
          eq_el c' cc
        with Not_equal -> raise Error
      end;
      Eval.univ cc
    | _ -> raise Error


and local ctx st i a n =
  let rho = Ctx.assign ctx in
  poly ctx Eval.interface i;
  let ii =  Eval.poly rho i in
  poly ctx Value.Type a;
  let aa = Eval.poly rho a in
  poly ctx (Value.Imm_set st) n;
  let newi = Eval.interface_plus ii (Eval.ref_interface st) in
  Value.Tree(newi, aa), Value.Tree(ii, aa)


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
