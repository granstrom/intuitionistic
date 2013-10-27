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

(*
 It is somewhat verbose/complicated to create terms directly in Ocaml
 syntax. The reason for this suite of tests is to test "level 1" of tt
 without involving the parser and the compiler.
*)

let x = Base.Variable "x"
let y = Base.Variable "y"
let z = Base.Variable "z"
let w = Base.Variable "w"

let _Pi a b c = Term.Pi(a, (b, c))
let __Pi a b c = Term.Pi_u(a, (b, c))
let _Sigma a b c = Term.Sigma(a, (b, c))
let _Tree i a = Term.Tree(i, a)
let _Id a b c = Term.Id(a, b, c)
let __Id a b c = Term.Id_u(a, b, c)
let _I32 = Term.Imm_set (Value.I32)
let _Type = Term.Type
let _T x = Term.T x
let lambda a b = Term.Lambda(a, b)
let pair a b = Term.Pair(a, b)
let ret a = Term.Ret(a)
let invk a b c = Term.Invk(a, (b, c))
let refl = Term.Mono(Term.Imm(Value.Refl))
let decl a _A = Term.Poly (a, _A)
let m x = Term.Mono x
let imm a = Term.Imm (Value.Imm32 (Int32.of_int a))
let tr = m (Term.true_cst)
let fl = m (Term.false_cst)
let unt = m (Term.unit_cst)
let pi a b c = Term.Pi_u(a, (b, c))
let sigma a b c = Term.Sigma_u(a, (b, c))
let tree i a = Term.Tree_u(i, a)
let id a b c = Term.Id_u(a, b, c)
let bool = Term.Enum_u(Base.bool_enum)
let ap a b = Term.App(a, b)
let v x = Term.Var (Base.Variable x)
let mv = Base.comp m v
let _if a u _C b c = Term.Enum_d(a, (u, _C), [Base.Enum_lit "true", b; Base.Enum_lit "false", c])
let _subst r u v _C d = Term.Subst(r, (u, (v, _C)), d)
let op o a b = Term.Builtin(o, [a; b])
let dummy = (Base.Variable "unused")
let dummy2 = (Base.Variable "unused2")
let write_interface = Term.Pair(m Term.bool_u, Term.Lambda(dummy, m(Term.Enum_u Base.unit_enum)))
let for2 n w _U _I z b = Term.For(n, (w, _U), _I, (z, b))

(* Function that sends x to x + x. *)
let double =
  decl
    (lambda x (m (op (Value.Add Value.I32) (mv "x") (mv "x"))))
    (_Pi _I32 dummy _I32)

let interface prefix =
  let open Term in
  let nov = Base.Variable (Printf.sprintf "%s_unused" prefix) in
  let x = Base.Variable (Printf.sprintf "%s_X" prefix) in
   (* union(x:type) : x -> type *)
  Sigma(Type, (x, Pi(T(Mono(Var(x))), (nov, Type))))

let interface_sum_type prefix =
  let open Term in
  let nov2 = Base.Variable (Printf.sprintf "%s_unused2" prefix) in
  let nov3 = Base.Variable (Printf.sprintf "%s_unused3" prefix) in
  let _Y = Base.Variable (Printf.sprintf "%s_Y" prefix) in
   (* fun(Y:type) : fun(_:Y->interface) : interface *)
  Pi(Type, (_Y, (Pi(Pi(T(Mono(Var(_Y))), (nov2, interface prefix)), (nov3, interface prefix)))))

let interface_sum prefix =
  let open Term in
  let _A = Base.Variable (Printf.sprintf "%s_A" prefix) in
  let _B = Base.Variable (Printf.sprintf "%s_B" prefix) in
  let x = Base.Variable (Printf.sprintf "%s_x" prefix) in
  let z = Base.Variable (Printf.sprintf "%s_z" prefix) in
  let fstBx = Mono(Fst(App(Var _B, Mono(Var x)))) in
  let sndBfstz = Snd(App(Var _B, Mono(Fst(Var z)))) in
   (*
      lam(A:type) { lam(B:A->interface) {
      (union(x:A):fst(B(x)), lam(z) { snd(B(fst(z)))(snd(z)) })
      }}
   *)
  Poly(
  Lambda(
  (_A, Lambda(
   (_B, Pair(
    Mono(
    Sigma_u(Mono(Var _A), (x, fstBx))),
    (Lambda((z, Mono(App(sndBfstz, Mono(Snd(Var z)))))))))))),
  interface_sum_type prefix)

let bool_fam x = Eval.mkEnum_d x (Value.Cst Value.Type)
  (Base.enum_map_make
     [Base.bool_true_lit, Value.unit_u; Base.bool_false_lit, Value.empty_u])

let dot_type =
  let open Value in
  Eval.dot_type bool_u (Fn bool_fam) (lambda (fun x -> bool_fam (Eval.mkFst x))) empty_u
let dot =
  let open Value in
  Eval.dot bool_u (Fn bool_fam) (lambda (fun x -> bool_fam (Eval.mkFst x))) empty_u

let oks =
  let open Term in [
    Mono(Purify(
      Mono bool_u,
      Poly(Ret(Mono false_cst),
           Tree(Pair(Mono(Sigma_u(Mono empty_u, (Base.Variable "dummy", Mono empty_u))),
                     Lambda(Base.Variable "dummy2", Mono empty_u)),
                Mono bool_u)))),
    bool_set;
    Reify.el dot, Reify.set dot_type;
    Mono(interface_sum "test1"), interface_sum_type "test2";
    Mono(interface_sum "test1"), Reify.set Eval.interface_sum_type;
    (
      let st = Value.I32 in
      let ii = Value.Pair(Value.unit_u, Value.lambdac Value.unit_u) in
      Lambda(
        (x,
         Mono(
           Local1(st,
                       Pair(Mono(unit_u), Lambda((Base.Variable "dummy", Mono(unit_u)))),
                       Mono(bool_u),
                       Mono(Imm(Value.Imm32 (Int32.of_int 10))),
                       Var(x))))),
      Reify.set (Value.Pi(Value.Tree(Eval.interface_plus ii (Eval.ref_interface st), Value.bool_u),
                          Value.Cst(Value.Tree(ii, Value.bool_u)))));
  (* Reflexivity proves true is equal to true. *)
    refl, _Id bool_set tr tr;
  (* Check identity function. *)
    lambda x (mv "x"), _Pi bool_set dummy bool_set;
  (* Prove that (forall x) x = x. *)
    lambda dummy refl, _Pi _Type x (_Id _Type (mv "x") (mv "x"));
  (* Prove that (forall x) x = x, using another proof. *)
    lambda x refl, _Pi _Type x (_Id _Type (mv "x") (mv "x"));
  (* Prove that (forall x) x = x, using a third proof. *)
    lambda y refl, _Pi _Type x (_Id _Type (mv "x") (mv "x"));
  (* x => if(x) { false; } else { true; }  : func(bool) : bool *)
    lambda x (m (_if (v "x") dummy bool_set fl tr)), _Pi bool_set dummy bool_set;
  (* Check double function. *)
    lambda x (m (op (Value.Add Value.I32) (mv "x") (mv "x"))), _Pi _I32 dummy2 _I32;
  (* Check double function. *)
    m double, _Pi _I32 dummy2 _I32;
  (* Check return. *)
    ret tr, _Tree write_interface (Mono bool_u);
  (* Check return. *)
    ret tr, _T (m (tree write_interface (m bool)));
  (* Check invoke. *)
    invk tr dummy (ret tr), _Tree write_interface (Mono bool_u);
  (* Check For. *)
    (lambda x (m(for2 (v "x") z (Mono (Enum_u Base.unit_enum))
                   (write_interface) y (invk (mv "y") dummy (ret unt))))),
    _Pi (_Tree write_interface (Mono empty_u)) dummy2
      (_Tree write_interface (Mono empty_u))
  ]

let ok_eqs = [
  (* Check alpha conversion. *)
  (lambda x (mv "x")), (lambda y (mv "y")), (_Pi _Type dummy _Type);
  (* Check alpha conversion for Pi types. *)
  m (__Pi (m Term.bool_u) x (m (__Id (m Term.bool_u) (mv "x") tr))), m (__Pi (m Term.bool_u) y (m (__Id (m Term.bool_u) (mv "y") tr))), _Type;
  (* Check simple computation, including beta conversion. *)
  (m (ap double (m (imm 15)))), (m (imm 30)), _I32;
  (* if(true) false else true = if(false) true else false. *)
  m (_if (decl tr Term.bool_set) dummy Term.bool_set fl tr), m (_if (decl fl Term.bool_set) dummy Term.bool_set tr fl), Term.bool_set;
  (* Check that definitions of interface_sum are equal. *)
  Term.Mono(interface_sum "test1"), Reify.el Eval.interface_sum, Reify.set Eval.interface_sum_type;
]

let noks = [
  (* True and false are not convertible. *)
  refl, _Id Term.bool_set tr fl;
  (* 0 and 1 are not convertible. *)
  refl, _Id _I32 (m (imm 0)) (m (imm 1));
  (* 0 and -1 are not convertible. *)
  refl, _Id _I32 (m (imm 0)) (m (imm (-1)));
  (* Reflexivity does not prove that x is equal to bool : universe. *)
  lambda x refl, _Pi _Type x (_Id _Type (mv "x") (m bool));
  (* Mistyped value in the return statement. *)
  (lambda x (m(for2 (v "x") z (Term.Mono Term.unit_u )
                 (write_interface) y (invk (mv "y") dummy (ret (mv "y")))))),
  _Pi (_Tree write_interface (Term.Mono Term.bool_u)) dummy2
    (_Tree write_interface (Term.Mono Term.bool_u))
]

(* Check that a is of type _A, and also that eval(reify(a)) is equal to a,    *)
(* and that further reification of both sides give equal results.             *)
let ok_pair (a, _A) =
  Check_term.set Ctx.empty _A;
  let __A = Eval.set Eval.Nil _A in
  let ___A = Reify.set __A in
  Check_term.set Ctx.empty ___A;
  let ____A = Eval.set Eval.Nil ___A in
  let _____A = Reify.set ____A in
  Value.eq_set __A ____A;
  Term.eq_set [] ___A _____A;
  Check_term.poly Ctx.empty __A a;
  let aa = Eval.poly Eval.Nil a in
  let aaa = Reify.el aa in
  Check_term.poly Ctx.empty __A aaa;
  let aaaa = Eval.poly Eval.Nil aaa in
  let aaaaa = Reify.el aaaa in
  Value.eq_el aa  aaaa;
  assert(Value.compare_el aa aaaa = 0);
  Term.eq_poly [] aaa aaaaa;
  ()

let ok_eq_pair (a, b, _A) =
  ok_pair (a, _A);
  ok_pair (b, _A);
  let aa = Eval.poly Eval.Nil a in
  let aaa = Reify.el aa in
  let aaaa = Eval.poly Eval.Nil aaa in
  let aaaaa = Reify.el aaaa in
  let bb = Eval.poly Eval.Nil b in
  let bbb = Reify.el bb in
  let bbbb = Eval.poly Eval.Nil bbb in
  let bbbbb = Reify.el bbbb in
  Value.eq_el aa  bb;
  assert(Value.compare_el aa bb = 0);
  Value.eq_el aa  bbbb;
  assert(Value.compare_el aa bbbb = 0);
  Value.eq_el aaaa  bb;
  assert(Value.compare_el aaaa bb = 0);
  Value.eq_el aaaa  bbbb;
  assert(Value.compare_el aaaa bbbb = 0);
  Term.eq_poly [] aaa bbb;
  Term.eq_poly [] aaaaa bbb;
  Term.eq_poly [] aaa bbbbb;
  Term.eq_poly [] aaaaa bbbbb;
  ()

let nok_pair (a, _A) =
  Check_term.set Ctx.empty _A;
  let __A = Eval.set Eval.Nil _A in
  if
    begin
      try
        Check_term.poly Ctx.empty __A a;
        true
      with _ -> false
    end
  then failwith "Expected check to fail...";
  ()

let main () =
  oks |> List.iter ok_pair;
  ok_eqs |> List.iter ok_eq_pair;
  noks |> List.iter nok_pair;
  ()
;;

main ();;
