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
open Expr

let report location msg =
  Format.eprintf "%a: " format_location location;
  Format.kfprintf (fun x -> Format.pp_print_newline x ())
    Format.err_formatter msg

exception Error

type check_infer =
| Manifest of Value.set * Term.mono
| Polymorph of (Value.set -> Term.poly)

let checked_enum_map_make ls =
  try enum_map_make (List.map (fun ((_, l), e) -> l, e) ls)
  with Duplicate_key k ->
    let rep ((loc, k'), _) =
      if k = k' then
        begin
          report loc "duplicate label %a" format_enum_lit k;
          raise Error
        end
    in
    List.iter rep ls;
    raise Error

let checked_enum_make ls =
  try enum_make (List.map snd ls)
  with Duplicate_key k ->
    let rep (loc, k') =
      if k = k' then
        begin
          report loc "duplicate label %a" format_enum_lit k;
          raise Error
        end
    in
    List.iter rep ls;
    raise Error

let extend = Check_term.extend
let extend_with_value = Check_term.extend_with_value

let value_ret = Value.Fn(fun x -> Value.Ret x)

let rec set (ctx:Ctx.ctx) (_Set:expr) : Term.set =
  match snd _Set with
  | Pi(_A, (x, _B)) ->
    let _A' = set ctx _A in
    let _A'' = Eval.set (Ctx.assign ctx) _A' in
    let _, ctx' = extend ctx x _A'' in
    let _B' = set ctx' _B in
    Term.Pi(_A', (x, _B'))
  | Sigma(_A, (x, _B)) ->
    let _A' = set ctx _A in
    let _A'' = Eval.set (Ctx.assign ctx) _A' in
    let _, ctx' = extend ctx x _A'' in
    let _B' = set ctx' _B in
    Term.Sigma(_A', (x, _B'))
  | Tree(_I, _A) ->
    let _I' = check ctx Eval.interface _I in
    let _A' = check ctx Value.Type _A in
    Term.Tree(_I', _A')
  | Id(_A, a, b) ->
    let _A' = set ctx _A in
    let _A'' = Eval.set (Ctx.assign ctx) _A' in
    let a' = check ctx _A'' a in
    let b' = check ctx _A'' b in
    Term.Id(_A', a', b')
  | Enum ls -> Term.Enum (checked_enum_make ls)
  | Type -> Term.Type
  | Interface -> Reify.set Eval.interface
  | _ ->
    let pp = check ctx Value.Type _Set in
    Term.T pp

and check (ctx:Ctx.ctx) (_A:Value.set) (expr:expr) : Term.poly =
  match check_infer ctx expr with
  | Polymorph fn -> fn _A
  | Manifest (_B, result) ->
    begin
      try
        Value.eq_set _A _B
      with Not_equal ->
        let r = report (fst expr) in
        r "expected %a" Printing.set _A;
        r "actual %a" Printing.set _B;
        raise Error
    end;
    Term.Mono result

and check_eval (ctx:Ctx.ctx) (cc:Value.set) (a:expr) : Value.el * Term.poly  =
  let a' = check ctx cc a in
  let a'' = Eval.poly (Ctx.assign ctx) a' in
  a'', a'

and infer (ctx:Ctx.ctx) (expr:expr) : Value.set * Term.mono =
  match check_infer ctx expr with
  | Manifest(_A, c) -> _A, c
  | Polymorph _ ->
    report (fst expr) "insufficient information";
    raise Error

(* Check an expression of type 'interface => ?' and return the ? and
   the corresponding term. *)
and interface_check (ctx:Ctx.ctx) (interf:Value.el) (in_expr:expr) : Value.el * Term.poly =
  let loc = fst in_expr in
  match snd in_expr with
  | Call (p) ->
    let _P = Eval.univ (Eval.mkFst interf) in
    let p'', p' = check_eval ctx _P p in
    let _A = Eval.mkApp (Eval.mkSnd interf) p'' in
    (* TODO: use reflect. *)
    let cont = Reify.el_fam value_ret in
    _A, Term.Invk(p', cont)

  | Dot (a, p) ->
    let open Value in
    let open Eval in
    begin
      match interf with
      | Pair(Sigma_u(_A, _B), _C) ->
        let _A' = univ _A in
        let a'', a' = check_eval ctx _A' a in
        let _E = Pair(apv _B a'', lambda(fun z -> mkApp _C (Pair (a'', z)))) in
        let _D, pp = interface_check ctx _E p in
        let dot_type = dot_type _A _B _C _D in
        (* TODO: use reflect. *)
        let dot_type_term = Reify.set dot_type in
        assert(Check_term.set ctx dot_type_term; true);
        (* TODO: use reflect. *)
        let dot = dot _A _B _C _D in
        let dot_term = Reify.el dot in
        assert(Check_term.poly ctx dot_type dot_term; true);
        let fn = Term.Poly(dot_term, dot_type_term) in
        _D, Term.Mono(Term.App(Term.App(fn, a'), pp))
      | _ ->
        report loc "required interface must accept pairs as commands";
        report loc "required interface: %a" Printing.el interf;
        raise Error
    end

  | For(n, (z, b)) ->
    begin
      match infer ctx n with
      (*
	n ^| J => A'
	A = A' : set
	b : I => J@z (z : |J|)
	---------------------------
	for(z in n) { b } : I => A
      *)
      | Value.Tree (_J, _A), nn ->
        let _I = interf in
	let z', z_ctx = extend ctx z (Eval.univ (Eval.mkFst _J)) in
	let _Jz = Eval.mkApp (Eval.mkSnd _J) z' in
	let bb = check z_ctx (Value.Tree(_I, _Jz)) b in
        _A, Term.Mono(Term.For(nn, (z, Reify.el _Jz),
                               Reify.el _I, (z, bb)))
      | t, _ ->
        report (fst n) "procedure expected";
        report (fst n) "%a" Printing.set t;
        raise Error
    end

  | _ ->
    let open Value in
    match infer ctx in_expr with
    | Tree(interf', _A), a' ->
      begin
        try
          Value.eq_el interf interf'
        with Not_equal ->
          report loc "expected required interface %a" Printing.el interf;
          report loc "actual required interface %a" Printing.el interf';
          raise Error
      end;
      _A, Term.Mono(a')
    | t, _ ->
      report loc "procedure expected";
      report loc "%a" Printing.set t;
      raise Error

and check_infer (ctx:Ctx.ctx) (a_expr:expr) : check_infer =
  let rho = Ctx.assign ctx in
  let a_loc = fst a_expr in
  (* Use |-> instead of the standard |>, as the latter is defined in
     OCaml 4.01, but not in earlier versions, and I'd like to be sure
     that there are no occurences of |> in the code. *)
  let (|->) a b = b a in
  match snd a_expr with
  | Hole ->
    Polymorph(fun _A ->
      report a_loc "hole: %a" Printing.set _A;
      Term.Hole)

  | Enum_cst (loc, x) ->
    Polymorph(
      function
      | Value.Enum xs ->
        if not (Enum_set.mem x xs) then
          begin
            report a_loc "invalid enum literal";
            report a_loc "expected one of %a" format_enum xs;
            raise Error
          end;
        Term.Mono(Term.Imm(Enum_imm(xs, x)))
      | s ->
        begin
          report a_loc "invalid use of enum literal";
          report a_loc "expected %a" Printing.set s;
          raise Error
        end)

  | Pair(a, b) ->
    Polymorph(
      function
      | Value.Sigma(_A, _B) ->
        let a' = check ctx _A a in
        let bb = check ctx (Value.ap _B (lazy (Eval.poly rho a'))) b in
        Term.Pair(a', bb)
      | t ->
        begin
          report a_loc "can only be used to construct tuples";
          report a_loc "expected %a" Printing.set t;
          raise Error
        end)

  | First (a) ->
    let _S, a' = infer ctx a in
    begin
      match _S with
      | Value.Sigma(_A, _B) -> Manifest(_A, Term.Fst(a'))
      | t ->
        report a_loc "'fst' can only be applied to pairs (tuples)";
        report a_loc "%a" Printing.set t;
        raise Error
    end

  | Second (a) ->
    let _S, a' = infer ctx a in
    begin
      match _S with
      | Value.Sigma(_A, _B) ->
        let _Ba = Value.ap _B (lazy (Eval.mkFst (Eval.mono rho a'))) in
        Manifest(_Ba, Term.Snd(a'))
      | t ->
        report a_loc "'snd' can only be applied to pairs (tuples)";
        report a_loc "%a" Printing.set t;
        raise Error
    end

  | Imm(Refl) ->
    Polymorph(
      function
      | Value.Id(_A, a, b) ->
        begin
          try
            Value.eq_el a b
          with Not_equal ->
            report a_loc "'refl' used but the two sides are not equal";
            report a_loc "left %a" Printing.el a;
            report a_loc "right %a" Printing.el b;
            raise Error
        end;
        Term.Mono(Term.Imm(Refl))
      | t ->
        begin
          report a_loc "'refl' can only be used to prove equalities";
          report a_loc "expected %a" Printing.set t;
          raise Error
        end)

  | Pi(a, (x, b)) ->
    let a' = check ctx Value.Type a in
    let _A = Eval.univ (Eval.poly rho a') in
    let _, ctx' = extend ctx x _A in
    let bb = check ctx' Value.Type b in
    Manifest(Value.Type, Term.Pi_u(a', (x, bb)))

  | Sigma(a, (x, b)) ->
    let a' = check ctx Value.Type a in
    let _A = Eval.univ (Eval.poly rho a') in
    let _, ctx' = extend ctx x _A in
    let bb = check ctx' Value.Type b in
    Manifest(Value.Type, Term.Sigma_u(a', (x, bb)))

  | Id(_A, a, b) ->
    let __A = check ctx Value.Type _A in
    let ___A = Eval.univ (Eval.poly rho __A) in
    let a' = check ctx ___A a in
    let b' = check ctx ___A b in
    Manifest(Value.Type, Term.Id_u(__A, a', b'))

  | Tree(i, a) ->
    let ii = check ctx Eval.interface i in
    let a' = check ctx Value.Type a in
    Manifest(Value.Type, Term.Tree_u(ii, a'))

  | Enum (a) ->
    let a' = checked_enum_make a in
    Manifest(Value.Type, Term.Enum_u a')

  | App(f, a) ->
    begin
      match check_infer ctx f with
      | Manifest(Value.Pi(_A, _B), ff) ->
        let a' = check ctx _A a in
        Manifest(Value.ap _B (lazy (Eval.poly rho a')),
                 Term.App(ff, a'))
      | Manifest(_X, _) ->
        begin
          report (fst f) "cannot be applied (not a function)";
          report (fst f) "%a" Printing.set _X;
          raise Error
        end
      | Polymorph(ftype_fn) ->
        begin
          match check_infer ctx a with
          | Manifest(atype, a') ->
            Polymorph(
              fun btype ->
                let ab_type = Value.Pi(atype, Value.Cst btype) in
                let ff = ftype_fn ab_type in
                Term.Mono(Term.App(Term.Poly(ff, Reify.set ab_type),
                                   Term.Mono a'))
            )
          | Polymorph(_) ->
            begin
              report a_loc "insufficient information in application";
              report a_loc "function or argument must be monomorphic";
              raise Error
            end
        end
    end

  | Var x ->
    let t =
      try Ctx.find_type x ctx
      with Not_found ->
        report a_loc "unbound variable '%a'" Var.format x;
        raise Error
    in
    Manifest(t, Term.Var x)

  | Decl (a, _A) ->
    begin
      let __A = set ctx _A in
      let ___A = Eval.set rho __A in
      (* Not using check here gives the opportunity to improve the error
         reporting, as we have access to the location of A. *)
      match check_infer ctx a with
      | Polymorph fn ->
        Manifest(___A, Term.Poly(fn ___A, __A))
      | Manifest (___B, result) ->
        begin
          try
            Value.eq_set ___A ___B
          with Not_equal ->
            report a_loc "invalid declaration";
            report (fst a) "actual %a" Printing.set ___B;
            report (fst _A) "declared %a" Printing.set ___A;
            raise Error
        end;
        Manifest(___A, result)
    end

  | Let(is_decl, a, (x, b)) ->
    let _A, a' = infer ctx a in
    let a'' = Eval.mono rho a' in
    let ctx' =
      if is_decl then
        extend_with_value ctx a'' x _A
      else
        snd (extend ctx x _A)
    in
    begin
      match check_infer ctx' b with
      | Manifest(_B, bb) ->
        Manifest(_B, Term.Beta_mono(a', (x, bb)))
      | Polymorph(b_fn) ->
        Polymorph(
          fun _B ->
            let bb = b_fn _B in
            Term.Beta_poly(a', (x, bb)))
    end

  | Complex_interface(cs_list) ->
    let cs = checked_enum_map_make cs_list in
    let cs_set = enum_of_enum_map cs in
    let fn = check ctx Eval.interface in
    let ccs = Enum_map.map fn cs in
    let x = Var.dummy () in
    let enum = Term.Mono(Term.Enum_u(cs_set)) in
    let fn = Term.Lambda(no_loc_pattern x,
                         Term.Mono(Term.Enum_d(
                           Term.Var x,
                           (no_pattern, Reify.set Eval.interface), ccs)))
    in
    Manifest(Eval.interface,
             Term.App(Term.App(Term.Poly(
               Reify.el Eval.interface_sum,
               Reify.set Eval.interface_sum_type), enum), fn))

  | Enum_d(cs_list) ->
    let cs = checked_enum_map_make cs_list in
    let cs_set = enum_of_enum_map cs in
    Polymorph(
      function
      | Value.Pi(Value.Enum ds, _C) when Enum_set.equal cs_set ds ->
	let fn k c =
          let _CCC = Value.apv _C (Value.Imm(Enum_imm (ds, k))) in
          check ctx _CCC c
	in
	let bs = Enum_map.mapi fn cs in
	let x1, x2 = Var.dummy (), Var.dummy () in
	let _C_x2 = Reify.set (Value.apv _C (Value.el_of_var x2)) in
	Term.Lambda(no_loc_pattern x1,
                    Term.Mono(Term.Enum_d(Term.Var x1,
                                          (no_loc_pattern x2, _C_x2), bs)))
      | Value.Pi(Value.Enum ds, _) ->
        report a_loc "expected set of labels is %a" format_enum ds;
        raise Error
      | Value.Pi(t, _) ->
        report a_loc "not enum %a" Printing.set t;
        raise Error
      | t ->
        report a_loc "expected %a" Printing.set t;
        raise Error)

  | Enum_d2(cs_list) ->
    let cs = checked_enum_map_make cs_list in
    let cs_set = enum_of_enum_map cs in
    Polymorph(
      let open Value in
      function
      | Pi(Sigma(Enum ds_set, _B), _C) when Enum_set.equal cs_set ds_set ->
	let fn k c =
          let kk = Imm(Enum_imm(ds_set, k)) in
          let _Bkk = apv _B kk in
          let _D x = apv _C (Pair(kk, x)) in
          check ctx (Pi(_Bkk, Fn _D)) c
	in
	let cs_terms = Enum_map.mapi fn cs in
        let cs_vals =
          Enum_map.map (fun x -> lazy (Eval.poly rho x)) cs_terms
        in
        let v x = Eval.mkEnum_d2 x _B _C cs_vals in
        Reify.el (Lambda (Fn v))
      | t ->
        report a_loc "expected %a" Printing.set t;
        raise Error)

  | Interpret(n, body) ->
    begin
      match infer ctx n with
      | Value.Tree (_J, _A'), nn ->
	Polymorph(
	  function
	  | Value.Tree(_I, _A) ->
            let open Value in
            begin
              try
                eq_el _A _A'
              with Not_equal ->
                report (fst n) "loop yields %a" Printing.el _A';
                report a_loc "expected loop yielding %a" Printing.el _A;
                raise Error
            end;
            let resJ z = Eval.mkApp (Eval.mkSnd _J) z in
            let cmdJ = Eval.univ (Eval.mkFst _J) in
            let _Body = Pi(cmdJ, Fn(fun x -> Tree(_I, resJ x))) in
	    let bb = check ctx _Body body in
	    let x1, x2 = Var.dummy (), Var.dummy () in
            let _J_x2 = Reify.el (resJ (el_of_var x2)) in
            let bb_decl = Term.Poly(bb, Reify.set _Body) in
            let bb_x1 = Term.Mono(Term.App(bb_decl, Term.Mono(Term.Var x1))) in
	    Term.Mono(
              Term.For(nn, (no_loc_pattern x2, _J_x2),
                       Reify.el _I, (no_loc_pattern x1, bb_x1)))
          | t ->
            report a_loc "expected %a" Printing.set t;
            raise Error)
      | t, _ ->
        report (fst n) "cannot loop over %a" Printing.set t;
        raise Error
    end

  | Subst(r, (x, (y, _C)), d) ->
    begin
      match infer ctx r with
      | Value.Id(__A, a', bb), rr ->
        let x', ctx' = extend ctx x __A in
        let _, ctx'' = extend ctx' y (Value.Id (__A, a', x')) in
        let __C = set ctx'' _C in
        let xy__C = x, (y, __C) in
        let ___C = (comp Eval.lift Eval.lift) Eval.set rho xy__C in
        let dd = check ctx (Value.apv (Value.apv ___C a') (Value.Imm Refl)) d in
        Manifest(Value.ap (Value.apv ___C bb) (lazy (Eval.mono rho rr)),
                 Term.Subst(rr, xy__C, dd))
      | t, _ ->
        report (fst r) "expected identity proof instead of %a" Printing.set t;
        raise Error
    end

  | Type ->
    report a_loc "invalid use of 'type'";
    raise Error

  | Interface ->
    report a_loc "invalid use of 'interface'";
    raise Error

  | Pattern(None, (x, b)) ->
    Polymorph(
      function
      | Value.Pi(_A, _B) ->
        let x', ctx' = extend ctx x _A in
        let bb = check ctx' (Value.apv _B x') b in
        Term.Lambda(x, bb)
      | t ->
        report a_loc "expected %a" Printing.set t;
        raise Error)

  | Pattern(Some _A, (x, b)) ->
    let __A = set ctx _A in
    let ___A = Eval.set rho __A in
    let x', ctx' = extend ctx x ___A in
    begin
      match check_infer ctx' b with
      | Polymorph(b_fn) ->
	Polymorph(
          function
          | Value.Pi(___A', ___B) ->
            begin
              try Value.eq_set ___A ___A'
              with Not_equal ->
                let r = report a_loc in
                r "expected domain %a" Printing.set ___A';
                r "declared domain %a" Printing.set ___A;
                raise Error
            end;
            let bb = b_fn (Value.apv ___B x') in
            Term.Lambda(x, bb)
          | t ->
            report a_loc "expected %a" Printing.set t;
            raise Error)
      | Manifest(___B, bb) ->
	let __B = Reify.set ___B in
	Manifest(
          Value.Pi(___A, Eval.lift Eval.set (Ctx.assign ctx')
            (x, __B)),
          Term.Poly(
            Term.Lambda(x, Term.Mono(bb)),
            Term.Pi(__A, (x, __B))))
    end

  | Imm(imm) -> Manifest(Value.set_of_imm imm, Term.Imm imm)

  | Purify (_A, p) ->
    let open Value in
    let _A'', _A' = check_eval ctx Type _A in
    let p' = check ctx (Tree(Eval.empty_interface, _A'')) p in
    Manifest(Eval.univ _A'', Term.Purify(_A', p'))

  | For(_, _)
  | Call(_, _)
  | Dot (_, _) ->
    Polymorph(
      function
      | Value.Tree(_I, _A) ->
        let _A', a_term = interface_check ctx _I a_expr in
        begin
          try
            Value.eq_el _A _A'
          with Not_equal ->
            let r = report a_loc in
            r "expected procedure codomain %a" Printing.el _A;
            r "actual procedure codomain %a" Printing.el _A';
            raise Error
        end;
        a_term
      | t ->
        report a_loc "operation requires a procedure context";
        report a_loc "expected %a" Printing.set t;
        raise Error)

  | Ret(a) ->
    Polymorph(
      function
      | Value.Tree(_I, _A) ->
        let a' = check ctx (Eval.univ _A) a in
        Term.Ret a'
      | t ->
        begin
          report a_loc "requires a procedure context";
          report a_loc "expected %a" Printing.set t;
          raise Error
        end)

  | Bind(a, perhaps_A, (x, b)) ->
    (* A bind operation is always polymorphic. *)
    Polymorph(
      function
      | Value.Tree(_I, _B) as _TREE ->
        (* If a type annotation is specified, we can check the type of a. *)
        let _A, a' =
          match perhaps_A with
          | Some ___A ->
            let _A, _ = check_eval ctx Value.Type ___A in
            let _TREE_A = Value.Tree(_I, _A) in
            let a' = check ctx _TREE_A a in
            _A, Term.Poly(a', Reify.set _TREE_A)
          | None ->
            let _A, a' = interface_check ctx _I a in
            let _TREE_A = Value.Tree(_I, _A) in
            _A, Term.Poly(a', Reify.set _TREE_A)
        in
        let _, ctx' = extend ctx x (Eval.univ _A) in
        let bb = check ctx' _TREE b in
        (* On the term-level, the type annotation required on a bind
           operation is B, as the type of a is inferrable. *)
        Term.Mono(Term.Bind(a', Reify.el _B, (x, bb)))
      | t ->
        begin
          report a_loc "requires a procedure context";
          report a_loc "expected %a" Printing.set t;
          raise Error
        end)

  | Range (a, b) ->
    let open Value in
    let a' = check ctx i32_set a in
    let bb = check ctx i32_set b in
    Manifest(Tree(Pair(i32_u, Lambda(Cst unit_u)), unit_u),
             Term.Range(a', bb))

  | New ((lit_pos, lit), v, b) ->
    Polymorph(
      function
      | Value.Tree(Value.Pair(Value.Sigma_u(Value.Enum_u _E, _C), _R) as _I, _A) as _T ->
	if Enum_set.mem lit _E then
	  begin
            report lit_pos "literal %a not new for required interface"
              format_enum_lit lit;
            report lit_pos "already a member of enum { %a }"
	      format_enum _E;
	    raise Error
	  end;
	let vv = check ctx Eval.ref_type v in
        let open Value in
        let open Eval in
        let vvv = poly rho vv in
        let www = mkApp (mkApp vvv _I) _A in
        let _J = mkFst www in
        let mkE x = Imm(Enum_imm(_E, x)) in
        let _Cm = begin Enum_set.elements _E
            |-> List.map (fun x -> (x, lazy (apv _C (mkE x))))
            |-> enum_map_make
            |-> Enum_map.add lit (lazy (mkFst _J))
        end in
        let _C' x = mkEnum_d x (Cst Type) _Cm in
        let _Rm = begin Enum_set.elements _E
            |-> List.map (fun x -> (x, lazy(lambda(fun y ->
              mkApp _R (Pair(mkE x, y))))))
            |-> enum_map_make
            |-> Enum_map.add lit (lazy(lambda (mkApp (mkSnd _J))))
        end in
        let fam _X = Fn(fun x -> univ (_X x)) in
        let _R' z = mkEnum_d2 z (fam _C') (Cst Type) _Rm in
        let _E' = Enum_set.add lit _E in
        let _I' = Pair(Sigma_u(Enum_u _E', Fn _C'), (lambda _R')) in
        assert(Check_term.poly ctx Eval.interface (Reify.el _I'); true);
        let bb = check ctx (Tree(_I', _A)) b in
        let bbb = poly rho bb in
        let _IplusJ = interface_plus _I _J in
        assert(Check_term.poly ctx Eval.interface (Reify.el _IplusJ); true);
        (* ds(c) : fun(y:C'(c)) : I+J => R'(c, y)  *)
        let call a b = Invk(Pair(a, b), value_ret) in
        let ds = begin Enum_set.elements _E
            |-> List.map (fun e -> e, lazy(lambda (fun y -> call false_cst (Pair(mkE e, y)))))
            |-> enum_map_make
            |-> Enum_map.add lit (lazy(lambda (fun y -> call true_cst y)))
        end in
        let _IJR p = Tree(_IplusJ, _R' p) in
        let body x = mkEnum_d2 x (fam _C') (Fn _IJR) ds in
        (* This is bbb lifted to be a suitable argument to (snd www). *)
        let bbb' = mkFor bbb (Fn _R') _IplusJ (Fn body) in
        let result = Reify.el (mkApp (mkSnd www) bbb') in
        assert(Check_term.poly ctx _T result; true);
        result
      | Value.Tree(c, _) ->
        report a_loc "commands of required interface must be a union";
        report a_loc "was %a" Printing.el c;
        raise Error
      | t ->
        report a_loc "expected %a" Printing.set t;
        raise Error)

  | Switch (a, cs_list) ->
    let cs = checked_enum_map_make cs_list in
    let cs_set = enum_of_enum_map cs in
    let _A'' = Value.Enum cs_set in
    let a' = check ctx _A'' a in
    (* Now check_infer on each binding in cs. *)
    let cs_ci = Enum_map.map (check_infer ctx) cs in
    let finish ___REAL_TYPE =
      let __REAL_TYPE = Reify.set ___REAL_TYPE in
      let fn ci =
        match ci with
        | Manifest(_, m) -> Term.Mono(m)
        | Polymorph(f) -> f ___REAL_TYPE
      in
      let bbs = Enum_map.map fn cs_ci in
      Term.Enum_d(Term.Poly(a', Term.Enum cs_set),
                  (no_pattern, __REAL_TYPE), bbs)
    in
    let extract_type = function
      | k, Manifest(___A, _) -> [k, ___A]
      | _, Polymorph(_) -> []
    in
    begin
      match Enum_map.bindings cs_ci
        |-> List.map extract_type
        |-> List.concat
      with
      | [] -> (* All branches are polymorphic. *)
        Polymorph(fun x -> Term.Mono(finish x))
      | (k, main) :: types ->
	List.iter
	  (fun (l, t) ->
            try
              Value.eq_set main t
            with Not_equal ->
              report a_loc "branch mismatch";
              report (fst (Enum_map.find k cs)) "%a" Printing.set main;
              report (fst (Enum_map.find l cs)) "%a" Printing.set t;
              raise Error)
	  types;
        Manifest(main, finish main)
    end

  | Switch2 (a, cs_list) ->
    let cs = checked_enum_map_make cs_list in
    let cs_set = enum_of_enum_map cs in
    begin
      let open Value in
      match infer ctx a with
      | Sigma(Enum ds_set, _B), a_term when Enum_set.equal cs_set ds_set ->
        let a_val = Eval.mono rho a_term in
        Polymorph(fun _A ->
          let mi x y = check ctx (Pi(apv _B (Imm(Enum_imm(ds_set, x))), Cst _A)) y in
          let cs_terms = Enum_map.mapi mi cs in
          let cs_vals = Enum_map.map (fun x -> lazy (Eval.poly rho x)) cs_terms in
          let v = Eval.mkEnum_d2 a_val _B (Cst _A) cs_vals in
          Reify.el v)
      | Sigma(Enum ds_set, _), _ ->
        report (fst a) "expected labels %a" format_enum ds_set;
        raise Error
      | t, _ ->
        report (fst a) "cannot switch on %a" Printing.set t;
        raise Error
    end
