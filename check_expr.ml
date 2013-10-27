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

let filename = ref ""

let report location msg =
  Format.eprintf "%s:%a: " !filename (Base.format_range) location;
  Format.kfprintf (fun x -> Format.pp_print_newline x ())
    Format.err_formatter msg

exception Error

type check_infer =
| Manifest of Value.set * Term.mono
| Polymorph of (Value.set -> Term.poly)

(* Strip off context bindings until x is reached, replacing them with
   applications of fn. *)
let rec mk_beta (fn : Term.mono * (var * 'a) -> 'a) (x : var) (bb : 'a)
    : Ctx.ctx -> 'a =
  function
  | Ctx.Ctx((xx, _) :: _, _) when x = xx -> bb
  | Ctx.Ctx((xx, _A) :: vs, Eval.Assign(es, _, a)) ->
    let body = mk_beta fn x bb (Ctx.Ctx (vs, es)) in
    let aa = Term.Poly (Reify.el a, Reify.set (Lazy.force _A)) in
    fn (aa, (xx, body))
  | Ctx.Ctx([], _)
  | Ctx.Ctx(_, Eval.Nil) -> raise Presupposition_error

let mk_beta_poly = mk_beta (fun (x, y) -> Term.BetaPoly (x, y))
let mk_beta_mono = mk_beta (fun (x, y) -> Term.BetaMono (x, y))
let mk_beta_set  = mk_beta (fun (x, y) -> Term.BetaSet  (x, y))

let rec pattern' ctx _C vvv patt =
  match patt with
  | P_var (_, var) -> Ctx.extend_el ctx var vvv (lazy _C)
  | P_blank _ -> ctx
  | P_tuple (a, b, maybe_as_var, is_as_var) ->
    begin
      match _C with
      | Value.Sigma(_A, _B) ->
        let ctx' =
          if is_as_var then
            Ctx.extend_el ctx maybe_as_var vvv (lazy _C)
          else
            ctx
        in
        let avvv = Eval.mkFst vvv in
        let bvvv = Eval.mkSnd vvv in
        let actx = pattern' ctx' _A avvv a in
        pattern' actx (Value.apv _B avvv) bvvv b
      | _ ->
        report (Expr.range_of_pattern patt)
          "tuple pattern used to match non-tuple";
        raise Error
    end
  | P_enum_d (_, is_open, patterns, maybe_as_var, is_as_var) ->
    begin
      match _C with
      | Value.Pi(Value.Enum enum, _B) ->
        begin
          let enum' = enum_make (List.map fst patterns) in
          if not ((if is_open then enum_subset else enum_equal) enum' enum)
          then
            begin
              report (Expr.range_of_pattern patt) "invalid enum pattern";
              raise Error
            end
        end;
        let ctx' =
          if is_as_var then
            Ctx.extend_el ctx maybe_as_var vvv (lazy _C)
          else
            ctx
        in
        let step ctx'' (cst, p) =
          let cst' = Value.Imm(Value.Enum_cst(enum, cst)) in
          pattern' ctx''
            (Value.apv _B cst')
            (Eval.mkApp vvv cst')
            p
        in
        List.fold_left step ctx' patterns
      | _ ->
        report (Expr.range_of_pattern patt) "invalid enum pattern" ;
        raise Error
    end

let pattern ctx _C patt val_opt =
  let var, patt' =
    match patt with
    | P_var (p, var)
    | P_blank (p, var) -> var, P_var (p, var)
    | P_tuple (a, b, var, _) ->
      var, P_tuple (a, b, var, true)
    | P_enum_d (r, op, patts, var, _) ->
      var, P_enum_d (r, op, patts, var, true)
  in
  let vvv = match val_opt with
    | None -> (Value.el_of_var var)
    | Some x -> x
  in
  var, pattern' ctx _C vvv patt'

let checked_enum_map_make ls range =
  try Base.enum_map_make ls
  with Base.Duplicate_key k ->
    report range "duplicate label %a" Base.format_enum_lit k;
    raise Error

let rec set (ctx:Ctx.ctx) (_Set:expr) : Term.set =
  match _Set with
  | Pi(_A, (patt, _B)) ->
    let __A = set ctx _A in
    let ___A = Eval.set (Ctx.assign ctx) __A in
    let x, ctx' = pattern ctx ___A patt None in
    let __B = set ctx' _B in
    Term.Pi(__A, (x, mk_beta_set x __B ctx'))
  | Sigma(_A, (patt, _B)) ->
    let __A = set ctx _A in
    let ___A = Eval.set (Ctx.assign ctx) __A in
    let x, ctx' = pattern ctx ___A patt None in
    let __B = set ctx' _B in
    Term.Sigma(__A, (x, mk_beta_set x __B ctx'))
  | Tree(_I, _A) ->
    let __I = check ctx Eval.interface _I in
    let __A = check ctx Value.Type _A in
    Term.Tree(__I, __A)
  | Id(range, _A, a, b) ->
    let __A = set ctx _A in
    let ___A = Eval.set (Ctx.assign ctx) __A in
    let aa = check ctx ___A a in
    let bb = check ctx ___A b in
    Term.Id(__A, aa, bb)
  | Enum (_, a) -> Term.Enum a
  | Type _ -> Term.Type
  | Interface _ -> Reify.set Eval.interface
  | _ ->
    let pp = check ctx Value.Type _Set in
    Term.T pp

and check (ctx:Ctx.ctx) (cc:Value.set) (a_expr:expr) : Term.poly =
  match check_infer ctx a_expr with
  | Polymorph fn -> fn cc
  | Manifest (dd, result) ->
    begin
      try
        Value.eq_set cc dd
      with Value.Not_equal ->
        let r = report (range_of_expr a_expr) in
        r "expected %a" Printing.set cc;
        r "actual %a" Printing.set dd;
        raise Error
    end;
    Term.Mono result

and check_eval (ctx:Ctx.ctx) (cc:Value.set) (a:expr) : Value.el * Term.poly  =
  let aa = check ctx cc a in
  let aaa = Eval.poly (Ctx.assign ctx) aa in
  aaa, aa

and infer (ctx:Ctx.ctx) (a_expr:expr) : Value.set * Term.mono =
  match check_infer ctx a_expr with
  | Manifest(cc, aa) -> cc, aa
  | Polymorph _ ->
    report (range_of_expr a_expr) "insufficient information";
    raise Error

(* Check an expression of type 'interface => ?' and return the ? and
   the corresponding term. *)
and interface_check (ctx:Ctx.ctx) (interface:Value.el) (in_expr:expr) : Value.el * Term.poly =
  match in_expr with
  | Call (p_range, p) ->
    let _P = Eval.univ (Eval.mkFst interface) in
    let ppp, pp = check_eval ctx _P p in
    let _A = Eval.mkApp (Eval.mkSnd interface) ppp in
    (* TODO: use reflect. *)
    _A, Term.Invk(pp, Reify.el_fam (Value.Fn(fun x -> Value.Ret x)))
  | Dot (a, p) ->
    let open Value in
    begin
      match interface with
      | Pair(Sigma_u(_A, _B), _C) ->
        let _AA = Eval.univ _A in
        let aaa, aa = check_eval ctx _AA a in
        let _E = Pair(apv _B aaa, lambda(fun z -> Eval.mkApp _C (Pair (aaa, z)))) in
        let _D, pp = interface_check ctx _E p in
        let dot_type = Eval.dot_type _A _B _C _D in
        (* TODO: use reflect. *)
        let dot_type_term = Reify.set dot_type in
        assert(Check_term.set ctx dot_type_term; true);
        (* TODO: use reflect. *)
        let dot = Eval.dot _A _B _C _D in
        let dot_term = Reify.el dot in
        assert(Check_term.poly ctx dot_type dot_term; true);
        let fn = Term.Poly(dot_term, dot_type_term) in
        _D, Term.Mono(Term.App(Term.App(fn, aa), pp))
      | _ ->
        report (range_of_expr in_expr)
          "required interface must accept pairs as commands";
        report (range_of_expr in_expr)
          "required interface: %a" Printing.el interface;
        raise Error
    end
  | _ ->
    let open Value in
    match infer ctx in_expr with
    | Tree(interface2, _A), aa ->
      begin
        try
          Value.eq_el interface interface2
        with Value.Not_equal ->
          let r = report (range_of_expr in_expr) in
          r "expected interface %a" Printing.el interface;
          r "actual interface %a" Printing.el interface2;
          raise Error
      end;
      _A, Term.Mono(aa)
    | t, _ ->
      report (range_of_expr in_expr) "procedure expected";
      report (range_of_expr in_expr) "%a" Printing.set t;
      raise Error

and check_infer (ctx:Ctx.ctx) (a_expr:expr) : check_infer =
  let rho = Ctx.assign ctx in
  let a_range = range_of_expr a_expr in
  let genvar form i =
    dummy_of_pos (Printf.sprintf "%s%d" form i) (fst (range_of_expr a_expr))
  in
  (* Use |-> instead of the standard |>, as the latter is defined in
     4.01, but not in earlier versions, and I'd like to be sure that
     there are no occurences of |> in the code. *)
  let (|->) a b = b a in
  match a_expr with
  | Enum_cst (_, x) ->
    Polymorph(
      function
      | Value.Enum xs ->
        if not (Enum_set.mem x xs) then
          begin
            report a_range "invalid enum literal";
            report a_range "expected one of %a" Base.format_enum xs;
            raise Error
          end;
        Term.Mono(Term.Imm(Value.Enum_cst(xs, x)))
      | s ->
        begin
          report a_range "invalid use of enum literal";
          report a_range "expected %a" Printing.set s;
          raise Error
        end)

  | Pair(a, b) ->
    Polymorph(
      function
      | Value.Sigma(_A, _B) ->
        let aa = check ctx _A a in
        let bb = check ctx (Value.ap _B (lazy (Eval.poly rho aa))) b in
        Term.Pair(aa, bb)
      | t ->
        begin
          report a_range "can only be used to construct tuples";
          report a_range "expected %a" Printing.set t;
          raise Error
        end)

  | Ret(_, a) ->
    Polymorph(
      function
      | Value.Tree(_I, _A) ->
        let aa = check ctx (Eval.univ _A) a in
        Term.Ret aa
      | t ->
        begin
          report a_range "requires a procedure context";
          report a_range "expected %a" Printing.set t;
          raise Error
        end)

  | Bind(a, perhaps_A, (patt, b)) ->
    (* A bind operation is always polymorphic. *)
    Polymorph(
      function
      | Value.Tree(_I, _B) as _TREE ->
        (* If a type annotation is specified, we can check the type of a. *)
        let _A, aa =
          match perhaps_A with
          | Some ___A ->
            let _A, __A = check_eval ctx Value.Type ___A in
            let _TREE_A = Value.Tree(_I, _A) in
            let aa = check ctx _TREE_A a in
            _A, Term.Poly(aa, Reify.set _TREE_A)
          | None ->
            let _A, aa = interface_check ctx _I a in
            let _TREE_A = Value.Tree(_I, _A) in
            _A, Term.Poly(aa, Reify.set _TREE_A)
        in
        let x, ctx' = pattern ctx (Eval.univ _A) patt None in
        let bb = check ctx' _TREE b in
        (* On the term-level, the type annotation required on a bind
           operation is B, as the type of a is inferrable. *)
        Term.Mono(Term.Bind(aa, Reify.el _B, (x, bb)))
      | t ->
        begin
          report a_range "requires a procedure context";
          report a_range "expected %a" Printing.set t;
          raise Error
        end)

  | First (a_range, a) ->
    let _S, aa = infer ctx a in
    begin
      match _S with
      | Value.Sigma(_A, _B) -> Manifest(_A, Term.Fst(aa))
      | t ->
        report a_range "'fst' can only be applied to pairs (tuples)";
        report a_range "%a" Printing.set t;
        raise Error
    end

  | Second (a_range, a) ->
    let _S, aa = infer ctx a in
    begin
      match _S with
      | Value.Sigma(_A, _B) ->
        let _Ba = Value.ap _B (lazy (Eval.mkFst (Eval.mono rho aa))) in
        Manifest(_Ba, Term.Snd(aa))
      | t ->
        report a_range "'snd' can only be applied to pairs (tuples)";
        report a_range "%a" Printing.set t;
        raise Error
    end

  | Imm(a_range, Value.Refl) ->
    Polymorph(
      function
      | Value.Id(_A, a, b) ->
        begin
          try
            Value.eq_el a b
          with Value.Not_equal ->
            report a_range "'refl' used but the two sides are not equal";
            report a_range "left %a" Printing.el a;
            report a_range "right %a" Printing.el b;
            raise Error
        end;
        Term.Mono(Term.Imm(Value.Refl))
      | t ->
        begin
          report a_range "'refl' can only be used to prove equalities";
          report a_range "expected %a" Printing.set t;
          raise Error
        end)

  | Range (a, b) ->
    let open Value in
    let aa = check ctx i32_set a in
    let bb = check ctx i32_set b in
    Manifest(Tree(Pair(i32_u, Lambda(Cst unit_u)),
                  unit_u),
             Term.Range(aa, bb))

  | Pi(a, (patt, b)) ->
    let aa = check ctx Value.Type a in
    let aaa = Eval.univ (Eval.poly rho aa) in
    let x, ctx' = pattern ctx aaa patt None in
    let bb = check ctx' Value.Type b in
    Manifest(Value.Type, Term.Pi_u(aa, (x, mk_beta_poly x bb ctx')))

  | Id(range, _A, a, b) ->
    let __A = check ctx Value.Type _A in
    let ___A = Eval.univ (Eval.poly (Ctx.assign ctx) __A) in
    let aa = check ctx ___A a in
    let bb = check ctx ___A b in
    Manifest(Value.Type, Term.Id_u(__A, aa, bb))

  | Sigma(a, (patt, b)) ->
    let aa = check ctx Value.Type a in
    let aaa = Eval.univ (Eval.poly rho aa) in
    let x, ctx' = pattern ctx aaa patt None in
    let bb = check ctx' Value.Type b in
    Manifest(Value.Type, Term.Sigma_u(aa, (x, mk_beta_poly x bb ctx')))

  | Tree(i, a) ->
    let ii = check ctx Eval.interface i in
    let aa = check ctx Value.Type a in
    Manifest(Value.Type, Term.Tree_u(ii, aa))


  | Enum (_, a) -> Manifest(Value.Type, Term.Enum_u a)

  | App(f, a) ->
    begin
      match check_infer ctx f with
      | Manifest(Value.Pi(_A, _B), ff) ->
        let aa = check ctx _A a in
        Manifest(Value.ap _B (lazy (Eval.poly rho aa)),
                 Term.App(ff, aa))
      | Manifest(_X, _) ->
        begin
          let frange = range_of_expr f in
          report frange "cannot be applied (not a function)";
          report frange "%a" Printing.set _X;
          raise Error
        end

      | Polymorph(ftype_fn) ->
        begin
          match check_infer ctx a with
          | Manifest(atype, aa) ->
            Polymorph(
              fun btype ->
                let ab_type = Value.Pi(atype, Value.Cst btype) in
                let ff = ftype_fn ab_type in
                Term.Mono(Term.App(Term.Poly(ff, Reify.set ab_type),
                                   Term.Mono aa))
            )
          | Polymorph(_) ->
            begin
              report a_range "insufficient information in application";
              report a_range "function or argument must be monomorphic";
              raise Error
            end
        end
    end

  | Var (range, x) ->
    let t =
      try Ctx.lookup x ctx
      with Not_found ->
        report range "unbound variable '%a'" Base.format_var x;
        raise Error
    in
    Manifest(t, Term.Var x)

  | Decl (a, _A) ->
    begin
      let __A = set ctx _A in
      let ___A = Eval.set rho __A in
      (* Not using check here gives the opportunity to improve the error
         reporting, as we have access to the range of A. *)
      match check_infer ctx a with
      | Polymorph fn ->
        Manifest(___A, Term.Poly(fn ___A, __A))
      | Manifest (___B, result) ->
        begin
          try
            Value.eq_set ___A ___B
          with Value.Not_equal ->
            report a_range "invalid declaration";
            report (range_of_expr a) "actual %a" Printing.set ___B;
            report (range_of_expr _A) "declared %a" Printing.set ___A;
            raise Error
        end;
        Manifest(___A, result)
    end

  | Call(_, _)
  | Dot (_, _) ->
    Polymorph(
      function
      | Value.Tree(_I, _A) ->
        let _A', a_term = interface_check ctx _I a_expr in
        begin
          try
            Value.eq_el _A _A'
          with Value.Not_equal ->
            let r = report a_range in
            r "expected codomain %a" Printing.el _A;
            r "actual codomain %a" Printing.el _A';
            raise Error
        end;
        a_term
      | t ->
        report a_range "operation requires a procedure context";
        report a_range "expected %a" Printing.set t;
        raise Error)

  | Purify (_, c, p) ->
    let open Value in
    let cc = check ctx Type c in
    let ccc = Eval.poly rho cc in
    let ttt = Tree(Eval.empty_interface, ccc) in
    (* TODO: use reflect. *)
    let tt = Term.Tree(Reify.el Eval.empty_interface, cc) in
    let pp = check ctx ttt p in
    Manifest(Eval.univ ccc, Term.Purify(cc, Term.Poly(pp, tt)))

  | New (new_range, lit, lit_pos, v, b) ->
    Polymorph(
      function
      | Value.Tree(Value.Pair(Value.Sigma_u(Value.Enum_u _E, _C), _R) as _I, _A) as _T ->
	if Base.Enum_set.mem lit _E then
	  begin
            report lit_pos "literal %a not new for required interface"
              Base.format_enum_lit lit;
            report lit_pos "already a member of enum { %a }"
	      Base.format_enum _E;
	    raise Error
	  end;
	let vv = check ctx Eval.ref_type v in
        let open Value in
        let open Eval in
        let vvv = poly rho vv in
        let www = mkApp (mkApp vvv _I) _A in
        let _J = mkFst www in
        let mkE x = Imm(Value.Enum_cst(_E, x)) in
        let _Cm = begin Base.Enum_set.elements _E
            |-> List.map (fun x -> (x, apv _C (mkE x)))
            |-> Base.enum_map_make
            |-> Base.Enum_map.add lit (mkFst _J)
        end in
        let _C' x = mkEnum_d x (Cst Type) _Cm in
        let _Rm = begin Base.Enum_set.elements _E
            |-> List.map (fun x -> (x, lambda(fun y -> mkApp _R (Pair(mkE x, y)))))
            |-> Base.enum_map_make
            |-> Base.Enum_map.add lit (lambda (mkApp (mkSnd _J)))
        end in
        let fam _X = Fn (fun x -> univ (_X x)) in
        let _R' z = mkEnum_d2 z (fam _C') (Cst Type) _Rm in
        let _E' = Base.Enum_set.add lit _E in
        let _I' = Pair(Sigma_u(Enum_u _E', Fn _C'), (lambda _R')) in
        assert(Check_term.poly ctx Eval.interface (Reify.el _I'); true);
        let bb = check ctx (Tree(_I', _A)) b in
        let bbb = poly rho bb in
        let _IplusJ = interface_plus _I _J in
        assert(Check_term.poly ctx Eval.interface (Reify.el _IplusJ); true);
        (* ds(c) : fun(y:C'(c)) : I+J => R'(c, y)  *)
        let call a b = Invk(Pair(a, b), Fn(fun x -> Ret x)) in
        let ds = begin Base.Enum_set.elements _E
            |-> List.map (fun e -> e, lambda (fun y -> call left_cst (Pair(mkE e, y))))
            |-> Base.enum_map_make
            |-> Base.Enum_map.add lit (lambda (fun y -> call right_cst y))
        end in
        let _IJR p = Tree(_IplusJ, _R' p) in
        let body x = mkEnum_d2 x (fam _C') (Fn _IJR) ds in
        (* This is bbb lifted to be a suitable argument to (snd www). *)
        let bbb' = mkFor bbb (Fn _R') _IplusJ (Fn body) in
        let result = Reify.el (mkApp (mkSnd www) bbb') in
        assert(Check_term.poly ctx _T result; true);
        result
      | Value.Tree(c, _) ->
        report new_range "commands of required interface must be a union";
        report new_range "was %a" Printing.el c;
        raise Error
      | t ->
        report a_range "expected %a" Printing.set t;
        raise Error)

  | Let(is_decl, a, (patt, b)) ->
    let _A, aa = infer ctx a in
    (* TODO: should the evaluation of a be lazy? *)
    let aaa = Eval.mono rho aa in
    let x, ctx' =
      pattern ctx _A patt
        (if is_decl then Some aaa else None)
    in
    begin
      match check_infer ctx' b with
      | Manifest(_B, bb) ->
        Manifest(_B, Term.BetaMono(aa, (x, mk_beta_mono x bb ctx')))
      | Polymorph(b_fn) ->
        Polymorph(
          fun _B ->
            (* Note: the extend call verifies that x is not declared in ctx.*)
            let bb = b_fn _B in
            Term.BetaPoly(aa, (x, mk_beta_poly x bb ctx')))
    end

  | Complex_interface(a_range, cs_list) ->
    let cs = checked_enum_map_make cs_list a_range in
    let cs_set = enum_of_enum_map cs in
    let fn = check ctx Eval.interface in
    let ccs = cs |-> Enum_map.map fn |-> Enum_map.bindings in
    (* TODO: use reflect instead. *)
    let x, unused = genvar "interface" 1, genvar "interface" 2 in
    let enum = Term.Mono(Term.Enum_u(cs_set)) in
    let fn = Term.Lambda(x, Term.Mono(Term.Enum_d(
      Term.Var x,
      (unused, Reify.set Eval.interface), ccs))) in
    Manifest(Eval.interface,
             Term.App(Term.App(Term.Poly(
               Reify.el Eval.interface_sum,
               Reify.set Eval.interface_sum_type), enum), fn))

  | Enum_d(a_range, cs_list) ->
    let cs = checked_enum_map_make cs_list a_range in
    let cs_set = enum_of_enum_map cs in
    Polymorph(
      function
      | Value.Pi(Value.Enum ds, _C) when enum_equal cs_set ds ->
	let fn k c =
          let _CCC = Value.apv _C (Value.Imm(Value.Enum_cst (ds, k))) in
          check ctx _CCC c
	in
	let bs = cs |-> Enum_map.mapi fn |-> Enum_map.bindings in
	let g = genvar "enum_d" in
	let x1, x2 = g 1, g 2 in
	let _C_x2 = Reify.set (Value.apv _C (Value.el_of_var x2)) in
	Term.Lambda(x1, Term.Mono(Term.Enum_d(Term.Var x1, (x2, _C_x2), bs)))
      | Value.Pi(Value.Enum ds, _) ->
        report a_range "expected set of labels is %a" Base.format_enum ds;
        raise Error
      | Value.Pi(t, _) ->
        report a_range "not enum %a" Printing.set t;
        raise Error
      | t ->
        report a_range "expected %a" Printing.set t;
        raise Error)

  | Enum_d2(range, cs_list) ->
    let cs = checked_enum_map_make cs_list range in
    let cs_set = enum_of_enum_map cs in
    Polymorph(
      let open Value in
      function
      | Pi(Sigma(Enum ds_set, _B), _C) when enum_equal cs_set ds_set ->
	let fn k c =
          let kk = Imm(Value.Enum_cst(ds_set, k)) in
          let _Bkk = apv _B kk in
          let _D x = apv _C (Pair(kk, x)) in
          check ctx (Pi(_Bkk, Fn(_D))) c
	in
	let cs_terms = Enum_map.mapi fn cs in
        let cs_vals = Base.Enum_map.map (Eval.poly rho) cs_terms in
        let v x = Eval.mkEnum_d2 x _B _C cs_vals in
        Reify.el (Lambda (Fn v))
      | t ->
        report range "expected %a" Printing.set t;
        raise Error)

  | Switch (switch_range, a, cs_list) ->
    let cs = checked_enum_map_make cs_list switch_range in
    let cs_set = enum_of_enum_map cs in
    let _AAA = Value.Enum cs_set in
    let aa = check ctx _AAA a in
    (* Now check_infer on each binding in cs. *)
    let cs_ci = Enum_map.map (check_infer ctx) cs in
    let bindings = Enum_map.bindings cs_ci in
    let finish ___REAL_TYPE =
      let __REAL_TYPE = Reify.set ___REAL_TYPE in
      let fn (k, ci) =
	k, match ci with
	| Manifest(_, m) -> Term.Mono(m)
	| Polymorph(f) -> f ___REAL_TYPE
      in
      let bbs = List.map fn bindings in
      (* TODO: this variable is a dummy: how to specify this on the term level? *)
      let x = genvar "enum_d" 1 in
      Term.Enum_d(Term.Poly(aa, Term.Enum cs_set), (x, __REAL_TYPE), bbs)
    in
    let extract_type = function
      | k, Manifest(___A, _) -> [k, ___A]
      | _, Polymorph(_) -> []
    in
    begin
      match List.map extract_type bindings |-> List.concat with
      | [] -> (* All branches are polymorphic. *)
        Polymorph(fun x -> Term.Mono(finish x))
      | (k, main) :: types ->
	List.iter
	  (fun (l, t) ->
            try
              Value.eq_set main t
            with Value.Not_equal ->
              report switch_range "branch mismatch";
              report (range_of_expr (Base.Enum_map.find k cs))
                "%a" Printing.set main;
              report (range_of_expr (Base.Enum_map.find l cs))
                "%a" Printing.set t;
              raise Error)
	  types;
        Manifest(main, finish main)
    end

  | Switch2 (switch_range, a, cs_list) ->
    let cs = checked_enum_map_make cs_list switch_range in
    let cs_set = enum_of_enum_map cs in
    begin
      let open Value in
      match infer ctx a with
      | Sigma(Enum ds_set, _B), a_term when Base.enum_equal cs_set ds_set ->
        let a_val = Eval.mono rho a_term in
        Polymorph(fun _A ->
          let mi x y = check ctx (Pi(apv _B (Imm(Value.Enum_cst(ds_set, x))), Cst _A)) y in
          let cs_terms = Base.Enum_map.mapi mi cs in
          let cs_vals = Base.Enum_map.map (Eval.poly rho) cs_terms in
          let v = Eval.mkEnum_d2 a_val _B (Cst _A) cs_vals in
          Reify.el v)
      | Sigma(Enum ds_set, _), _ ->
        report (range_of_expr a) "expected labels %a"
          Base.format_enum ds_set;
        raise Error
      | t, _ ->
        report (range_of_expr a) "cannot switch on %a"
          Printing.set t;
        raise Error
    end

  | For(n, (pattz, b)) ->
    begin
      match infer ctx n with
      (*
	n ^| J => A'
	A = A' : set
	b : I => J@z (z : |J|)
	---------------------------
	for(z in n) { b } : I => A
      *)
      | Value.Tree (_J, _A'), nn ->
	Polymorph(
	  function
	  | Value.Tree(_I, _A) ->
            begin
              try
                Value.eq_el _A _A'
              with Value.Not_equal ->
                report (range_of_expr n) "loop yields %a" Printing.el _A';
                report a_range "expected loop yielding %a" Printing.el _A;
                raise Error
            end;
	    let z, z_ctx = pattern ctx (Eval.univ (Eval.mkFst _J)) pattz None in
	    let _Jz = Eval.mkApp (Eval.mkSnd _J) (Value.el_of_var z) in
	    let bb =
	      check
                z_ctx
                (Value.Tree(_I, _Jz))
                b
	    in
	    Term.Mono(
              Term.For(nn, (z, Reify.el _Jz), Reify.el _I, (z, bb)))
          | t ->
            report a_range "expected %a" Printing.set t;
            raise Error)
      | t, _ ->
        report (range_of_expr n) "cannot loop over %a" Printing.set t;
        raise Error
    end

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
                report (range_of_expr n) "loop yields %a" Printing.el _A';
                report a_range "expected loop yielding %a" Printing.el _A;
                raise Error
            end;
            let resJ z = Eval.mkApp (Eval.mkSnd _J) z in
            let cmdJ = Eval.univ (Eval.mkFst _J) in
            let _Body = Pi(cmdJ, Fn(fun x -> Tree(_I, resJ x))) in
	    let bb = check ctx _Body body in
	    let g = genvar "interface" in
	    let x1, x2 = g 1, g 2 in
            let _J_x2 = Reify.el (resJ (el_of_var x2)) in
            let bb_decl = Term.Poly(bb, Reify.set _Body) in
            let bb_x1 = Term.Mono(Term.App(bb_decl, Term.Mono(Term.Var x1))) in
	    Term.Mono(
              Term.For(nn, (x2, _J_x2), Reify.el _I, (x1, bb_x1)))
          | t ->
            report a_range "expected %a" Printing.set t;
            raise Error)
      | t, _ ->
        report (range_of_expr n) "cannot loop over %a" Printing.set t;
        raise Error
    end

  | Subst(_, r, (pattx, (patty, _C)), d) ->
    begin
      match infer ctx r with
      | Value.Id(__A, aa, bb), rr ->
        let x, ctx' = pattern ctx __A pattx None in
        let y, ctx'' =
          pattern ctx' (Value.Id (__A, aa, Value.el_of_var x)) patty None
        in
        let __C = set ctx'' _C in
        let xy__C = (x, (y, mk_beta_set y __C ctx'')) in
        let ___C = (Base.comp Eval.lift Eval.lift) Eval.set rho xy__C in
        let dd = check ctx (Value.apv (Value.apv ___C aa) (Value.Imm Value.Refl)) d in
        Manifest(Value.ap (Value.apv ___C bb) (lazy (Eval.mono rho rr)),
                 Term.Subst(rr, xy__C, dd))
      | t, _ ->
        report (range_of_expr r) "expected identity proof instead of %a"
          Printing.set t;
        raise Error
    end

  | Type range ->
    report range "invalid use of 'type'";
    raise Error

  | Interface range ->
    report range "invalid use of 'interface'";
    raise Error

  | Pattern(None, (patt, b)) ->
    Polymorph(
      function
      | Value.Pi(_A, _B) ->
        let x, ctx2 = pattern ctx _A patt None in
        let bb = check ctx2 (Value.apv _B (Value.el_of_var x)) b in
        Term.Lambda(x, mk_beta_poly x bb ctx2)
      | t ->
        report a_range "expected %a" Printing.set t;
        raise Error)

  | Pattern(Some _A, (patt, b)) ->
    let __A = set ctx _A in
    let ___A = Eval.set rho __A in
    let x, ctx2 = pattern ctx ___A patt None in
    begin
      match check_infer ctx2 b with
      | Polymorph(b_fn) ->
	Polymorph(
          function
          | Value.Pi(___A', ___B) ->
            begin
              try Value.eq_set ___A ___A'
              with Value.Not_equal ->
                let r = report a_range in
                r "expected domain %a" Printing.set ___A';
                r "declared domain %a" Printing.set ___A;
                raise Error
            end;
            let bb = b_fn (Value.apv ___B (Value.el_of_var x)) in
            Term.Lambda(x, mk_beta_poly x bb ctx2)
          | t ->
            report a_range "expected %a" Printing.set t;
            raise Error)
      | Manifest(___B, bb) ->
	let __B = Reify.set ___B in
	Manifest(
          Value.Pi(___A, Eval.lift Eval.set (Ctx.assign ctx2) (x, __B)),
          Term.Poly(
            Term.Lambda(x, Term.Mono(mk_beta_mono x bb ctx2)),
            Term.Pi(__A, (x, __B))))
    end

  | Imm(_, imm) -> Manifest(Value.set_of_imm imm, Term.Imm imm)
