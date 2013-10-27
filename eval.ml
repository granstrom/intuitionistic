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

(* === Dealing with built-in functions. === *)

let mkbinop int int32 int64 =
  let open Value in
  function
  | I8 -> begin
    function [Imm8 xx; Imm8 yy] -> Imm8 (Char.chr (int (Char.code xx) (Char.code yy)))
    | _ -> raise Base.Presupposition_error
  end
  | I16 -> begin
    function [Imm16 xx; Imm16 yy] -> Imm16 (int xx yy)
    | _ -> raise Base.Presupposition_error
  end
  | I32 -> begin
    function [Imm32 xx; Imm32 yy] -> Imm32 (int32 xx yy)
    | _ -> raise Base.Presupposition_error
  end
  | I64 -> begin
    function [Imm64 xx; Imm64 yy] -> Imm64 (int64 xx yy)
    | _ -> raise Base.Presupposition_error
  end

let mkunop int int32 int64 =
  let open Value in
  function
  | I8 -> begin
    function [Imm8 xx] -> Imm8 (Char.chr (int (Char.code xx)))
    | _ -> raise Base.Presupposition_error
  end
  | I16 -> begin
    function [Imm16 xx] -> Imm16 (int xx)
    | _ -> raise Base.Presupposition_error
  end
  | I32 -> begin
    function [Imm32 xx] -> Imm32 (int32 xx)
    | _ -> raise Base.Presupposition_error
  end
  | I64 -> begin
    function [Imm64 xx] -> Imm64 (int64 xx)
    | _ -> raise Base.Presupposition_error
  end

let bool_of_bool x =
  let open Value in
  Enum_cst(Base.bool_enum,
           if x then Base.bool_true_lit else Base.bool_false_lit)

let mkbinrel int int32 int64 =
  let open Value in
  function
  | I8 -> begin
    function [Imm8 xx; Imm8 yy] ->
      bool_of_bool (int (Char.code xx) (Char.code yy))
    | _ -> raise Base.Presupposition_error
  end
  | I16 -> begin
    function [Imm16 xx; Imm16 yy] -> bool_of_bool (int xx yy)
    | _ -> raise Base.Presupposition_error
  end
  | I32 -> begin
    function [Imm32 xx; Imm32 yy] -> bool_of_bool (int32 xx yy)
    | _ -> raise Base.Presupposition_error
  end
  | I64 -> begin
    function [Imm64 xx; Imm64 yy] -> bool_of_bool (int64 xx yy)
    | _ -> raise Base.Presupposition_error
  end

let mkshift int int32 int64 =
  let open Value in
  function
  | I8 -> begin
    function [Imm8 xx; Imm8 yy] ->
      Imm8 (Char.chr (int (Char.code xx) (Char.code yy land 0x07)))
    | _ -> raise Base.Presupposition_error
  end
  | I16 -> begin
    function [Imm16 xx; Imm8 yy] -> Imm16 (int xx (Char.code yy land 0x0f))
    | _ -> raise Base.Presupposition_error
  end
  | I32 -> begin
    function [Imm32 xx; Imm8 yy] -> Imm32 (int32 xx (Char.code yy land 0x1f))
    | _ -> raise Base.Presupposition_error
  end
  | I64 -> begin
    function [Imm64 xx; Imm8 yy] -> Imm64 (int64 xx (Char.code yy land 0x3f))
    | _ -> raise Base.Presupposition_error
  end

let mkdivrem int int32 int64 =
  let open Value in
  function
  | I8 -> begin
    function [Imm8 xx; Imm8 yy; Refl] ->
      Imm8 (Char.chr (int (Char.code xx) (Char.code yy)))
    | _ -> raise Base.Presupposition_error
  end
  | I16 -> begin
    function [Imm16 xx; Imm16 yy; Refl] -> Imm16 (int xx yy)
    | _ -> raise Base.Presupposition_error
  end
  | I32 -> begin
    function [Imm32 xx; Imm32 yy; Refl] -> Imm32 (int32 xx yy)
    | _ -> raise Base.Presupposition_error
  end
  | I64 -> begin
    function [Imm64 xx; Imm64 yy; Refl] -> Imm64 (int64 xx yy)
    | _ -> raise Base.Presupposition_error
  end

let aeqrel = mkbinrel (=) (=) (=)
let lessrel = mkbinrel (<) (<) (<)
let addop = mkbinop (+) Int32.add Int64.add
let subop = mkbinop (-) Int32.sub Int64.sub
let negop = mkunop (~-) Int32.neg Int64.neg
let mulop = mkbinop ( * ) Int32.mul Int64.mul
let xorop = mkbinop (lxor) Int32.logxor Int64.logxor
let iorop = mkbinop (lor) Int32.logor Int64.logor
let andop = mkbinop (land) Int32.logand Int64.logand
let notop = mkunop (lnot) Int32.lognot Int64.lognot
let lslop = mkshift (lsl) Int32.shift_left Int64.shift_left
let lsrop = mkshift (lsr) Int32.shift_right_logical Int64.shift_right_logical
let asrop = mkshift (asr) Int32.shift_right Int64.shift_right
let sdivop = mkdivrem (/) Int32.div Int64.div
let sremop = mkdivrem (mod) Int32.rem Int64.rem
let sextop a b =
  let open Value in
  match a, b with
  | aa, bb when aa = bb -> begin function [x] -> x
    | _ -> raise Base.Presupposition_error end
  (* Sign extensions. *)
  | I8, I16 -> begin function [Imm8 yy] -> Imm16(Char.code yy)
    | _ -> raise Base.Presupposition_error end
  | I8, I32 -> begin function [Imm8 yy] -> Imm32(Int32.of_int (Char.code yy))
    | _ -> raise Base.Presupposition_error end
  | I8, I64 -> begin function [Imm8 yy] -> Imm64(Int64.of_int (Char.code yy))
    | _ -> raise Base.Presupposition_error end
  | I16, I32 -> begin function [Imm16 yy] -> Imm32(Int32.of_int yy)
    | _ -> raise Base.Presupposition_error end
  | I16, I64 -> begin function [Imm16 yy] -> Imm64(Int64.of_int yy)
    | _ -> raise Base.Presupposition_error end
  | I32, I64 -> begin function [Imm32 yy] -> Imm64(Int64.of_int32 yy)
    | _ -> raise Base.Presupposition_error end
  (* Truncations. *)
  | I16, I8 -> begin function [Imm16 yy] -> Imm8(Char.chr yy)
    | _ -> raise Base.Presupposition_error end
  | I32, I8 -> begin function [Imm32 yy] -> Imm8(Char.chr (Int32.to_int yy))
    | _ -> raise Base.Presupposition_error end
  | I64, I8 -> begin function [Imm64 yy] -> Imm8(Char.chr (Int64.to_int yy))
    | _ -> raise Base.Presupposition_error end
  | I32, I16 -> begin function [Imm32 yy] -> Imm16(Int32.to_int yy)
    | _ -> raise Base.Presupposition_error end
  | I64, I16 -> begin function [Imm64 yy] -> Imm16(Int64.to_int yy)
    | _ -> raise Base.Presupposition_error end
  | I64, I32 -> begin function [Imm64 yy] -> Imm32(Int64.to_int32 yy)
    | _ -> raise Base.Presupposition_error end
  | _ -> raise Base.Presupposition_error

let constantly_refl n xs =
  if List.length xs <> n then raise Base.Presupposition_error;
  Value.Refl

let evalBuiltin : Value.builtin -> Value.imm list -> Value.imm =
  let open Value in
  function
  | Aeq a -> aeqrel a
  | Less a -> lessrel a
  | Add a -> addop a
  | Sub a -> subop a
  | Neg a -> negop a
  | Mul a -> mulop a
  | Xor a -> xorop a
  | Ior a -> iorop a
  | And a -> andop a
  | Not a -> notop a
  | Lsl a -> lslop a
  | Lsr a -> lsrop a
  | Asr a -> asrop a
  | Sdiv a -> sdivop a
  | Srem a -> sremop a
  | Sext (a, b) -> sextop a b
  | LessTrans _ -> constantly_refl 5
  | LessAntisym _ -> constantly_refl 1
  | AeqProp _ -> constantly_refl 3
  | AeqRefl _ -> constantly_refl 1
  | AddCommutative _ -> constantly_refl 2
  | AddAssociative _ -> constantly_refl 3
  | AddUnit _ -> constantly_refl 1
  | AddInverse _ -> constantly_refl 1
  | MulCommutative _ -> constantly_refl 2
  | MulAssociative _ -> constantly_refl 3
  | MulUnit _ -> constantly_refl 1
  | Distributive _ -> constantly_refl 3
  | SubAxiom _ -> constantly_refl 2

(* === Preparation for definition of eval. === *)

let mkApp f a =
  match f with
  | Value.Lambda ff -> Value.apv ff a
  | Value.Neut n -> Value.Neut(Value.App(n, a))
  | _ -> raise Base.Presupposition_error

(*
   n : enum { c1; ...; cn } (= E)
   C : E -> set
   cs[ci] : C(ci)
*)
let mkEnum_d n _C cs =
  match n with
  | Value.Neut m -> Value.Neut(Value.Enum_d(m, _C, cs))
  | Value.Imm(Value.Enum_cst(ds, s)) when Base.enum_equal ds (Base.enum_of_enum_map cs) ->
    begin
      try Base.Enum_map.find s cs
      with Not_found -> raise Base.Presupposition_error
    end
  | _ -> raise Base.Presupposition_error

let mkFst =
  function
  | Value.Neut m -> Value.Neut(Value.Fst m)
  | Value.Pair(a, _) -> a
  | _ -> raise Base.Presupposition_error

let mkSnd =
  function
  | Value.Neut m -> Value.Neut(Value.Snd m)
  | Value.Pair(_, b) -> b
  | _ -> raise Base.Presupposition_error

let mkSubst r _C d =
  match r with
  | Value.Neut m -> Value.Neut(Value.Subst(m, _C, d))
  | Value.Imm Value.Refl -> d
  | _ -> raise Base.Presupposition_error

let rec mkBuiltin p imms_rev =
  function
  | [] -> Value.Imm(evalBuiltin p (List.rev imms_rev))
  | Value.Neut n :: rs -> Value.Neut(Value.Builtin(p, List.rev imms_rev, n, rs))
  | Value.Imm imm :: rs -> mkBuiltin p (imm :: imms_rev) rs
  | _ -> raise Base.Presupposition_error

let rec mkRange_ n m =
  if n < m then
    Value.Invk(Value.Imm(Value.Imm32 n),
	       Value.Cst(mkRange_ (Int32.add n Int32.one) m))
  else
    Value.Ret Value.unit_cst

let mkRange n m =
  match n with
  | Value.Neut nn -> Value.Neut(Value.Range1(nn, m))
  | Value.Imm(Value.Imm32 nn) ->
    begin
      match m with
      | Value.Neut mm -> Value.Neut(Value.Range2(nn, mm))
      | Value.Imm(Value.Imm32 mm) -> mkRange_ nn mm
      | _ -> raise Base.Presupposition_error
    end
  | _ -> raise Base.Presupposition_error

(*
   p : I => A
   f : A -> I => B
   ----------------
   p >>=_B f : I => B

   a : A
   f : A -> I => B
   -----------------------------------
   ret a >>=_B f = f a : I => B

   c : |I|
   t : I@c -> I => A
   f : A -> I => B
   ------------------------------------------------------
   invk c t >>=_B f = invk c (\x -> t x >>=_B f) : I => B
*)
let rec mkBind n _B f : Value.el =
  let open Value in
  match n with
  | Neut m -> Neut(Bind(m, _B, f))
  | Ret a -> apv f a
  | Invk(c, Cst t) -> Invk(c, Cst(mkBind t _B f))
  | Invk(c, Fn t) -> Invk(c, Fn(fun x -> mkBind (t x) _B f))
  | _ -> raise Base.Presupposition_error

(*
   for _ in yield(a) { body }     = yield(a)
   for x in invoke(c, t) { body } = val x = do body(c/x); for y in t(x) { body }
*)
let rec mkFor n _U _I body =
  let open Value in
  match n with
  | Neut m -> Neut(For(m, _U, _I, body))
  | Ret a -> Ret a
  | Invk(c, Cst t) -> mkBind (apv body c) (apv _U c) (Cst(mkFor t _U _I body))
  | Invk(c, Fn t) -> mkBind (apv body c) (apv _U c) (Fn(fun x -> mkFor (t x) _U _I body))
  | _ -> raise Base.Presupposition_error

(*
local(c, r, a, n, yield(x)) = x

local(c, r, a, n, ({ val x = do left(t); v(x)})) = ({ val x = do t; local(c, r, a, n, v(x))})

local(c, r, a, n, ({ val x = do right(t); v(x) })) = local(c, r, a, t(n), v(t(n)))
*)
let rec mkLocal1 st i a n p =
  match p with
  | Value.Neut q -> Value.Neut(Value.Local1(st, i, a, n, q))
  | Value.Ret a -> Value.Ret a
  | Value.Invk(u, v) -> mkLocal2 st i a n u v
  | _ -> raise Base.Presupposition_error
and mkLocal2 st i a n u v =
  match u with
  | Value.Neut u' -> Value.Neut(Value.Local2(st, i, a, n, u', v))
  | Value.Pair(s, t) -> mkLocal3 st i a n s t v
  | _ -> raise Base.Presupposition_error
and mkLocal3 st i a n s t v =
  let open Value in
  match s with
  | Neut s' -> Neut(Local3(st, i, a, n, s', t, v))
  | Imm(Value.Enum_cst(e, l)) when e = Base.plus_enum ->
    begin
      match l with
      | w when w = Base.left_lit ->
	let vv = Fn(fun x -> mkLocal1 st i a n (apv v x)) in
	Invk(t, vv)
      | w when w = Base.right_lit ->
	  let new_n = mkApp t n in
	  mkLocal1 st i a new_n (apv v new_n)
      | _ -> raise Base.Presupposition_error
    end
  | _ -> raise Base.Presupposition_error

type assign =
  | Nil
  | Assign of assign * Base.var * Value.el

let lift(fn : assign -> 'a -> 'b) : assign -> 'a Term.fn -> 'b Value.fn =
  fun rho -> fun(p, a) ->
    match p with
    | Base.Variable "" -> Value.Cst(fn rho a)
    | x -> Value.Fn(fun xx -> fn (Assign(rho, x, xx)) a)

let rec set(rho : assign) : Term.set -> Value.set =
  let open Term in
  function
  | Pi(a, b) -> Value.Pi(set rho a, lift set rho b)
  | Sigma(a, b) -> Value.Sigma(set rho a, lift set rho b)
  | Tree(i, a) -> Value.Tree(poly rho i, poly rho a)
  | Id(a, b, c) -> Value.Id(set rho a, poly rho b, poly rho c)
  | Enum a -> Value.Enum a
  | Imm_set a -> Value.Imm_set a
  | Type -> Value.Type
  | T e -> univ (poly rho e)
  | BetaSet(a, b) -> Value.apv (lift set rho b) (mono rho a)

and univ : Value.el -> Value.set =
  let open Value in
  function
  | Pi_u(a, b) -> Pi(univ a, precomp univ b)
  | Sigma_u(a, b) -> Sigma(univ a, precomp univ b)
  | Tree_u(i, a) -> Tree(i, a)
  | Id_u(a, b, c) -> Id(univ a, b, c)
  | Enum_u a -> Enum a
  | Imm_set_u a-> Imm_set a
  | Neut x -> T x
  | _ -> raise Base.Presupposition_error

and poly(rho : assign) : Term.poly -> Value.el =
  let open Term in
  function
  | Mono a -> mono rho a
  | Lambda b -> Value.Lambda(lift poly rho b)
  | Pair(a, b) -> Value.Pair(poly rho a, poly rho b)
  | Ret a -> Value.Ret(poly rho a)
  | Invk(c, t) -> Value.Invk(poly rho c, lift poly rho t)
  | BetaPoly(a, b) -> Value.apv (lift poly rho b) (mono rho a)

and mono(rho : assign) : Term.mono -> Value.el =
  let open Term in
  function
  | Imm a -> Value.Imm a
  | Pi_u(a, b) -> Value.Pi_u(poly rho a, lift poly rho b)
  | Sigma_u(a, b) -> Value.Sigma_u(poly rho a, lift poly rho b)
  | Tree_u(i, a) -> Value.Tree_u(poly rho i, poly rho a)
  | Id_u(a, b, c) -> Value.Id_u(poly rho a, poly rho b, poly rho c)
  | Enum_u a -> Value.Enum_u a
  | Imm_set_u a -> Value.Imm_set_u a
  | Poly(e, _) -> poly rho e
  | Var x ->
    let rec lookup x =
      function
      | Nil -> raise Base.Presupposition_error
      | Assign(_, y, v) when x = y -> v
      | Assign(rest, _, _) -> lookup x rest
    in
    lookup x rho
  | App(f, a) -> mkApp (mono rho f) (poly rho a)
  | Fst(n) -> mkFst (mono rho n)
  | Snd(n) -> mkSnd (mono rho n)
  | Enum_d(n, _C, cs) -> mkEnum_d (mono rho n) (lift set rho _C)
    (Base.Enum_map.map (poly rho) (Base.enum_map_make cs))
  | Range(n, m) -> mkRange (poly rho n) (poly rho m)
  | Subst(r, _C, d) -> mkSubst (mono rho r)
    ((Base.comp lift lift) set rho _C) (poly rho d)
  | Builtin(p, rs) -> mkBuiltin p [] (List.map (poly rho) rs)
  | For(n, _U, _I, f) -> mkFor (mono rho n) (lift poly rho _U)
    (poly rho _I) (lift poly rho f)
  | Bind(n, _B, f) -> mkBind (mono rho n) (poly rho _B) (lift poly rho f)
  | Local1(st, i, a, n, p) -> mkLocal1 st (poly rho i) (poly rho a)
    (poly rho n) (mono rho p)
  | Local2(st, i, a, n, u, v) -> mkLocal2 st (poly rho i) (poly rho a)
    (poly rho n) (mono rho u) (lift poly rho v)
  | Local3(st, i, a, n, e, d, v) -> mkLocal3 st (poly rho i) (poly rho a)
    (poly rho n) (mono rho e) (poly rho d) (lift poly rho v)
  | Purify(c, m) -> mkPurify (poly rho c) (mono rho m)
  | BetaMono(a, b) -> Value.apv (lift mono rho b) (mono rho a)

and mkPurify c =
  let open Value in
  function
  | Neut n -> Neut(Purify (c, n))
  | Ret a -> a
  | Invk (d, _) -> mkEnum_d (mkFst d) (Cst (univ c)) Base.Enum_map.empty
  | _ -> raise Base.Presupposition_error

let interface_fn = Value.Fn(fun x -> Value.Pi(univ x, Value.Cst Value.Type))
let interface = Value.Sigma(Value.Type, interface_fn)
let interface_sum_type =
  let open Value in
  Pi(Type, Fn(fun _A -> Pi(Pi(univ _A, Cst interface), Cst interface)))
(*
   lam(A:type) { lam(B:A->interface) {
   (union(x:A):fst(B(x)), lam(z) { snd(B(fst(z)))(snd(z)) })
   }}
*)
let interface_sum =
  let open Value in
  lambda(fun _A -> lambda(fun _B ->
    let _C = Sigma_u(_A, Fn(fun x -> mkFst (mkApp _B x))) in
    Pair(_C, lambda(fun z ->  mkApp (mkSnd (mkApp _B (mkFst z))) (mkSnd z)))))

let abort t x = mkEnum_d x (Value.Cst t) Base.Enum_map.empty
let empty_interface =
  let open Value in
  Pair(Sigma_u(empty_u, Fn(abort Type)), lambda(fun x -> abort Type (mkFst x)))

let methods is_list =
  let is = is_list |> Base.enum_map_make in
  let is_set = Base.enum_of_enum_map is in
  let i_fam x = mkEnum_d x (Value.Cst interface) is in
  mkApp (mkApp interface_sum (Value.Enum_u is_set)) (Value.lambda i_fam)

let interface_plus a b =
  methods [
    Base.left_lit, a;
    Base.right_lit, b
  ]

let ref_interface st =
  let ss = (Value.Imm_set_u st) in
  Value.Pair(Value.Pi_u(ss, Value.Cst ss), Value.lambdac ss)

let ref_type =
  let open Value in
  Pi(interface, Fn(fun i ->
    Pi(Type, Fn(fun a ->
      Sigma(interface, Fn(fun j ->
        Pi(Tree(interface_plus i j, a), Cst(Tree(i, a)))))))))

let new_ref st =
  let open Value in
  lambda(fun n ->
    lambda(fun i ->
      lambda(fun a ->
        Pair(ref_interface st, lambda(fun p ->
          mkLocal1 st i a n p)))))

let new_ref_type st =
  Value.Pi(Value.Imm_set st, Value.Cst(ref_type))

(*
  Given
  A : type,
  B(x) : type (x:A),
  C : union(x:A)B(x) -> type,
  D : type,
  this gives the type
  fun(x:A):(method(y:B(x)):C(x,y)=>D)->(method(z:union(x:A):B(x)):C(z)=>D)
*)
let dot_type
    (_A : Value.el)
    (_B : Value.el Value.fn)
    (_C : Value.el)
    (_D : Value.el) =
  let open Value in
  Pi(univ _A, Fn(fun x ->
    let _Bx = apv _B x in
    let _Cx =  Value.lambda(fun y -> mkApp _C (Pair(x, y))) in
    Pi(Tree(Pair(_Bx, _Cx), _D),
       Cst(Tree(Pair(Sigma_u(_A, _B), _C), _D)))))
let dot
    (_A : Value.el)
    (_B : Value.el Value.fn)
    (_C : Value.el)
    (_D : Value.el) =
  let open Value in
  lambda(fun a ->
    lambda(fun p ->
      mkFor p (Fn(fun y -> mkApp _C (Pair(a, y))))
	(Pair(Sigma_u(_A, _B), _C)) (Fn(fun c ->
	  Value.Invk(Pair(a, c), Fn(fun z -> Value.Ret z))))))

(*
   E = enum { c1; ...; cn } : set
   B : E -> set
   n : union(x:E):B(x)
   C : union(x:E):B(x) -> set
   cs[ci] : func(y:B(ci)):C(ci, y)
   -----
   mkEnum_d2 n B C cs : C(n)
*)
let mkEnum_d2 n _B _C cs =
  let open Value in
  let _D x = Pi(apv _B x, Fn(fun y -> apv _C (Pair(x, y)))) in
  mkApp (mkEnum_d (mkFst n) (Fn _D) cs) (mkSnd n)

let zero_of_size =
  let open Value in
  function
  | I8 -> Imm8(Char.chr 0)
  | I16 -> Imm16 0
  | I32 -> Imm32 0l
  | I64 -> Imm64 0L

let one_of_size =
  let open Value in
  function
  | I8 -> Imm8(Char.chr 1)
  | I16 -> Imm16 1
  | I32 -> Imm32 1l
  | I64 -> Imm64 1L

let aeq a x y =
  let open Value in
  Id_u(bool_u,
       mkBuiltin (Value.Aeq a) [] [x; y],
       true_cst)

let less a x y =
  let open Value in
  Id_u(bool_u,
       mkBuiltin (Value.Less a) [] [x; y],
       true_cst)

let not_less a x y =
  let open Value in
  Id_u(bool_u,
       mkBuiltin (Value.Less a) [] [x; y],
       false_cst)

let positive a y = less a (Value.Imm(zero_of_size a)) y

let commutative t fn =
  let open Value in
  2, Sigma_u(t, Cst(t)),
  Fn(fun w ->
    let x = mkFst w in
    let y = mkSnd w in
    Id_u(t, fn x y, fn y x))

let associative t fn =
  let open Value in
  3, Sigma_u(t, Cst(Sigma_u(t, Cst(t)))),
  Fn(fun w ->
    let x = mkFst w in
    let y = mkFst (mkSnd w) in
    let z = mkSnd (mkSnd w) in
    Id_u(t, fn x (fn y  z), fn (fn x y) z))

let unit t fn u =
  let open Value in
  1, t, Fn(fun x -> Id_u(t, fn x u, x))

let distributive t mul add =
  let open Value in
  3, Sigma_u(t, Cst(Sigma_u(t, Cst(t)))),
  Fn(fun w ->
    let x = mkFst w in
    let y = mkFst (mkSnd w) in
    let z = mkSnd (mkSnd w) in
    Id_u(t, mul x (add y z), add (mul x y) (mul x z)))


let builtin_dom_cod =
  let open Value in
  let s x = Imm_set_u x in
  let add a x y = mkBuiltin (Add a) [] [x; y] in
  let neg a x = mkBuiltin (Neg a) [] [x] in
  let sub a x y = mkBuiltin (Sub a) [] [x; y] in
  let mul a x y = mkBuiltin (Mul a) [] [x; y] in
  function
  | Aeq a
  | Less a -> 2, Sigma_u(s a, Cst(s a)), Cst(bool_u)
  | Neg a
  | Not a -> 1, s a, Cst(s a)
  | Add a
  | Sub a
  | Mul a
  | Xor a
  | Ior a
  | And a -> 2, Sigma_u(s a, Cst(s a)), Cst(s a)
  | Lsl a
  | Lsr a
  | Asr a -> 2, Sigma_u(s a, Cst(i8_u)), Cst(s a)
  | Sdiv a
  | Srem a -> 3, Sigma_u(s a, Cst(Sigma_u(s a, Fn(fun y -> positive a y)))), Cst(s a)
  | Sext (a, b) -> 1, s a, Cst(s b)
  (* Axioms about <. *)
  | LessTrans a ->
    5, Sigma_u(s a, Fn(fun x -> Sigma_u(s a, Fn(fun y ->
      Sigma_u(s a, Fn(fun z -> Sigma_u(less a x y, Cst(less a y z)))))))),
    Fn(fun w -> less a (mkFst w) (mkFst (mkSnd (mkSnd w))))
  | LessAntisym a -> 1, s a, Fn(fun x -> not_less a x x)
  (* Axioms about ==. *)
  | AeqProp a ->
    3, Sigma_u(s a, Fn(fun x -> Sigma_u(s a, Fn(fun y -> aeq a x y)))),
    Fn(fun w -> Id_u(s a, mkFst w, mkFst (mkSnd w)))
  | AeqRefl a ->
    1, s a,
    Fn(fun w -> aeq a w w )
  (* Axioms about addition. *)
  | AddCommutative a -> commutative (s a) (add a)
  | AddAssociative a -> associative (s a) (add a)
  | AddUnit a -> unit (s a) (add a) (Imm(zero_of_size a))
  | AddInverse a -> 1, s a,
    (let z = Imm(zero_of_size a) in
     Fn(fun x -> Id_u(s a, add a x (neg a x), z)))
  (* Axioms about multiplication. *)
  | MulCommutative a -> commutative (s a) (mul a)
  | MulAssociative a -> associative (s a) (mul a)
  | MulUnit a -> unit (s a) (mul a) (Imm(one_of_size a))
  (* Distribution. *)
  | Distributive a -> distributive (s a) (mul a) (add a)
  (* Definition of subtraction. *)
  | SubAxiom a -> 2, Sigma_u(s a, Cst(s a)),
    Fn(fun w ->
      let x = mkFst w in
      let y = mkSnd w in
      Id_u(s a, add a x (neg a y), sub a x y))

let rec mkTuple n v =
  if n <= 1 then [v]
  else mkFst v :: mkTuple (n - 1) (mkSnd v)

let builtin_val_type builtin =
  let n, a, b = builtin_dom_cod builtin in
  Value.Lambda(Value.Fn(fun x -> mkBuiltin builtin [] (mkTuple n x))),
  Value.Pi_u(a, b)
