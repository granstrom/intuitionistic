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
   This module implements the most important algorithm of IPL, viz.,
   the reduction of an arbitrary program of base type, in a context
   where all variables are of base type, to a program representation
   that easily can be translated to LLVM.
*)

type el = Value.el
type neut = Value.neut
type component = Value.component
type label = Label of int
type target = Target of int
type alloca = Alloca of int
type size = Base.size
type builtin = Base.builtin
type var = Base.var
type imm = Base.imm
type 'a enum_map = 'a Base.enum_map

exception Compile_hole

(* An object of this type represents a piece of code that can be
   compiled to an LLVM value. *)
type value =
(* The first value evaluates to an enum literal. *)
| Select of value * value enum_map
(* Gives as result whatever the block returns through End_purify. *)
| Purify of target * block
| Op of builtin * value list
| Var of var
| Imm of imm

(* An object of this type represents a piece of code that can be
   translated to a terminated block of LLVM code. *)
and block' =
(* The first value evaluates to an enum literal: continue with the
   specified block. *)
| Switch of value * block enum_map
(* Final return from function. *)
| Ret of value
(* Similar to Ret, but instead of returning, branch to target. *)
| End_purify of value * target
(* Used to implement range loops. *)
| Goto of label
(* Range(from, to, x, loop_label, body, then) *)
| Range of value * value * var * label * block * block
(* Create a variable in the entry block of the function. *)
| Declare_alloca of alloca * size * value * block
(* Load the value of alloca into var, execute first code, update store
   with value, and execute second code with var bound to new value. *)
| Load_and_store of alloca * var * value * var * block
(* This construct is only used for memoization. *)
| Block_ref of label

(* A block can be "labelled" by memoization. *)
and block = label option ref * block'

(* Code to print values and blocks for debugging purposes. *)
let format_map (vv:Format.formatter -> 'a -> unit)
    (fmt:Format.formatter) (a:'a Base.enum_map) =
  Base.Enum_map.iter (fun k v ->
    Format.fprintf fmt "@ %a: %a" Base.format_enum_lit k vv v)
    a
let rec format_value (fmt:Format.formatter) :value -> unit =
  let open Format in
  function
  | Select(c, cs) ->
    fprintf fmt "@[<v 1>(select %a%a)@]"
      format_value c (format_map format_value) cs
  | Purify(Target l, c) ->
    fprintf fmt "@[<hov 2>(purify target_%d@ %a)@]" l format_block c
  | Op(op, []) -> raise Base.Presupposition_error
  | Op(op, args) ->
    fprintf fmt "(%a" Printing.builtin op;
    List.iter (fun x -> fprintf fmt " %a" format_value x) args;
    fprintf fmt ")"
  | Var(x) -> fprintf fmt "%a" Var.format x
  | Imm(i) -> fprintf fmt "%s" (Printing.string_of_imm i)
and format_block (fmt:Format.formatter) (bbb:block) :unit =
  let open Format in
  begin
    match !(fst bbb) with
    | Some(Label l) -> fprintf fmt "%d@@" l
    | None -> ()
  end;
  match snd bbb with
  | Switch(c, cs) ->
    fprintf fmt "@[<v 1>[switch %a%a]@]"
      format_value c (format_map format_block) cs
  | Goto(Label l) ->  fprintf fmt "[goto label_%d]" l
  | Ret(c) -> fprintf fmt "[ret %a]" format_value c
  | End_purify(c, Target l) ->
    fprintf fmt "@[<hov 1>[end_purify %a goto target_%d]@]" format_value c l
  | Declare_alloca(Alloca a, sz, v, c) ->
    fprintf fmt "@[<hov 2>[alloca [cell_%d:%s = %a]@ %a]@]"
      a (Printing.string_of_size sz) format_value v format_block c
  | Load_and_store(Alloca a, x, st, y, gt) ->
    fprintf fmt "@[<hov 1>[%a = [%a = cell_%d; %a]@ %a]@]"
      Var.format y Var.format x a format_value st format_block gt
  | Range(a, b, x, Label l, bdy, next) ->
    fprintf fmt
      "@[<hov 2>[range [@[<hv 0>%a in %a .. %a@ next: label_%d@ finally: %a@]]@ %a]@]"
      Var.format x format_value a format_value b l format_block next format_block bdy
  | Block_ref(Label l) -> fprintf fmt "[goto %d@@]" l

(* How to compile Value.Ret. *)
type yield = el -> block

(* How to compile Value.Invoke. *)
type invoke = el -> (el -> block) -> block

(* How to compile Value.Lambda. *)
type 'a lambda = el Value.fn -> 'a

(* How to compile Value.Pair. *)
type 'a pair = el -> el -> 'a

(* These functions are specified when the construct in question is not
   applicable, typically as it wouldn't be well typed. *)
let no_yield (_:el):block = raise Base.Presupposition_error
let no_invoke (_:el) (_:el -> block):block = raise Base.Presupposition_error
let no_lambda (_:el Value.fn):'a = raise Base.Presupposition_error
let no_pair (_:el) (_:el):'a = raise Base.Presupposition_error

(* These counters are used to generate unique names of various sorts. *)
let label_counter = ref 0
let target_counter = ref 0
let alloca_counter = ref 0
let next_label () =
  let x = !label_counter in
  label_counter:= x + 1;
  Label x
let next_target () =
  let x = !target_counter in
  target_counter:= x + 1;
  Target x
let next_alloca () =
  let x = !alloca_counter in
  alloca_counter:= x + 1;
  Alloca x
let reset_counters () =
  label_counter := 0;
  target_counter := 0;
  alloca_counter := 0;

(* Objects of type Value.el are comparable, and can be the key of a map. *)
module El_map = Map.Make(struct
  type t = Value.el
  let compare = Value.compare_el
end)

(* This function is used to memoize a 'yield' function. *)
let memo (yield:yield):yield =
  let map :block El_map.t ref = ref El_map.empty in
  fun (v:Value.el) ->
    (* First, try to find v in map. *)
    match try Some (El_map.find v !map) with Not_found -> None with
    | None ->
      (* Execute implementation function. *)
      let r = yield v in
      (* This is a new value, it must have label None. *)
      assert(!(fst r) = None);
      (* The value v wasn't in the map before calling 'yield', check
         that it still isn't there. *)
      assert(not (El_map.mem v !map));
      (* Add the result r to the map. *)
      map := El_map.add v r !map;
      (* And return r. *)
      r
    | Some result ->
      (* If the result has no label, i.e., if this is the first time
         we reuse it, create a label for it. *)
      let l =
        match !(fst result) with
        | None ->
          let l = next_label () in
          fst result := Some(l);
          l
        | Some l -> l
      in
      ref None, Block_ref l

(* Here starts the main compilation algorithm of IPL. *)

(* TODO: Make a special case of neut_value with no lambda and no
   pair. This functioncan be memoized. *)

(* How to translate a Value.neut into a value. *)
let rec neut_lp_value (lambda:value lambda) (pair:value pair) :neut->value =
  function
  | Value.Var x -> Var x
  | Value.Builtin(op, pre, n, post) ->
    let pre' = List.map (fun x -> Imm x) pre in
    let n' = neut_lp_value no_lambda no_pair n in
    let post' = List.map (el_lp_value no_lambda no_pair) post in
    Op(op, pre' @ n' :: post')
  | Value.Enum_d(n, _, cs) ->
    Select(neut_lp_value no_lambda no_pair n,
           Base.Enum_map.map (fun x -> el_lp_value lambda pair (Lazy.force x)) cs)
  | Value.App(f, a) ->
    let lambda' ff = el_lp_value lambda pair (Value.apv ff a) in
    neut_lp_value lambda' no_pair f
  | Value.Fst(n) ->
    let pair' p _ = el_lp_value lambda pair p in
    neut_lp_value no_lambda pair' n
  | Value.Snd(n) ->
    let pair' _ q = el_lp_value lambda pair q in
    neut_lp_value no_lambda pair' n
  (* Substitution is computationally irrelevant. *)
  | Value.Subst(_, _, p) -> el_lp_value lambda pair p
  | Value.Purify(_, p) ->
    let lbl = next_target () in
    let yield' x = ref None, End_purify (el_lp_value lambda pair x, lbl) in
    Purify(lbl, neut_iy_block no_invoke (memo yield') p)
  (* All other constructors of Value.neut create objets of procedure
     type. Hence they cannot end up here. *)
  | _ -> raise Base.Presupposition_error

(* How to translate a Value.el into a value. *)
and el_lp_value (lambda:value lambda) (pair:value pair) :el->value =
  function
  | Value.Imm(i) -> Imm(i)
  | Value.Neut(n) -> neut_lp_value lambda pair n
  | Value.Lambda(f) -> lambda f
  | Value.Pair(a, b) -> pair a b
  | Value.Hole -> raise Compile_hole
  (* All other constructors of Value.el create objets of procedure
     type, or objects of type Type. Hence they cannot end up here. *)
  | _ -> raise Base.Presupposition_error

(* How to translate a Value.neut of procedure type into a block. *)
and neut_iy_block (invoke:invoke) (yield:yield) :neut->block =
  function
  (* Note that a and b are integers. *)
  | Value.Range1(a, b) ->
    range invoke yield
      (neut_lp_value no_lambda no_pair a)
      (el_lp_value no_lambda no_pair b)
  | Value.Range2(a, b) ->
    range invoke yield
      (Imm (Base.Imm32 a))
      (neut_lp_value no_lambda no_pair b)
  | Value.Bind(c, _, t) ->
    let yield' a = el_iy_block invoke yield (Value.apv t a) in
    neut_iy_block invoke (memo yield') c
  | Value.For(n, _, _, t) ->
    let invoke' d s = el_iy_block invoke s (Value.apv t d) in
    neut_iy_block invoke' yield n
  | Value.Local(im, _, _, init, p) ->
    local invoke yield im init p
  | Value.Catch(_, _, _, f, p) ->
    catch invoke yield f p
  (* Note that n is of enum type. *)
  | Value.Enum_d(n, _, cs) ->
    ref None,
    Switch(neut_lp_value no_lambda no_pair n,
           Base.Enum_map.map (fun x -> el_iy_block invoke yield (Lazy.force x)) cs)
  | Value.App(f, a) ->
    let lambda' ff = el_iy_block invoke yield (Value.apv ff a) in
    neut_lp_block lambda' no_pair f
  | Value.Fst(n) ->
    let pair' p _ = el_iy_block invoke yield p in
    neut_lp_block no_lambda pair' n
  | Value.Snd(n) ->
    let pair' _ q = el_iy_block invoke yield q in
    neut_lp_block no_lambda pair' n
  (* Substitution is computationally irrelevant. *)
  | Value.Subst(_, _, p) -> el_iy_block invoke yield p
  | Value.Purify(_, p) ->
    let yield' x = el_iy_block invoke yield x in
    neut_iy_block no_invoke (memo yield') p
  | _ -> raise Base.Presupposition_error

(* How to translate a Value.el of procedure type into a block. *)
and el_iy_block (invoke:invoke) (yield:yield) :el->block =
  function
  | Value.Ret(a) -> yield a
  | Value.Invk(c, t) ->
    let cont x = el_iy_block invoke yield (Value.apv t x) in
    invoke c (memo cont)
  | Value.Neut(n) -> neut_iy_block invoke yield n
  | Value.Hole -> raise Compile_hole
  | _ -> raise Base.Presupposition_error

(* How to translate a Value.neut of procedure type into a block, when
   the translated Value.el in fact is of Pi or Sigma type. *)
and neut_lp_block (lambda:block lambda) (pair:block pair) :neut->block =
  function
  | Value.Enum_d(n, _, cs) ->
    ref None,
    Switch(neut_lp_value no_lambda no_pair n,
           Base.Enum_map.map (fun x -> el_lp_block lambda pair (Lazy.force x)) cs)
  | Value.App(f, a) ->
    let lambda' ff = el_lp_block lambda pair (Value.apv ff a) in
    neut_lp_block lambda' no_pair f
  | Value.Fst(n) ->
    let pair' p _ = el_lp_block lambda pair p in
    neut_lp_block no_lambda pair' n
  | Value.Snd(n) ->
    let pair' _ q = el_lp_block lambda pair q in
    neut_lp_block no_lambda pair' n
  (* Substitution is computationally irrelevant. *)
  | Value.Subst(_, _, p) -> el_lp_block lambda pair p
  | Value.Purify(_, p) ->
    let yield' x = el_lp_block lambda pair x in
    neut_iy_block no_invoke (memo yield') p
  | _ -> raise Base.Presupposition_error

(* How to translate a Value.el of procedure type into a block, when
   the translated Value.el in fact is of Pi or Sigma type. *)
and el_lp_block (lambda:block lambda) (pair:block pair) :el->block =
  function
  | Value.Neut(n) -> neut_lp_block lambda pair n
  | Value.Lambda(f) -> lambda f
  | Value.Pair(a, b) -> pair a b
  | Value.Hole -> raise Compile_hole
  | _ -> raise Base.Presupposition_error

(* This function is use to translate Value.Catch into a block. *)
and catch (invoke:invoke) (yield:yield) (f:el) (n:component):block =
  let open Value in
  let catcher' (y:el):block =
    (* f is a function b -> i => a, y is of type b. *)
    el_iy_block invoke yield (Eval.mkApp f y)
  in
  let catcher = memo catcher' in
  (* This is how an invocation will be compiled inside n. *)
  let invoke' (p:el) (t:el->block):block =
    (* p is of sigma type: x is the enum value and y the method argument. *)
    let pair (x:el) (y:el):block =
      let emit_base () = invoke y t in
      let emit_catch () = catcher y in
      (* The enum value x may need to be computed. *)
      match x with
      | Imm(Base.Enum_imm(e, l)) when Base.Enum_set.equal e Base.bool_enum ->
        begin
          match l with
          | w when w = Base.false_lit -> emit_base ()
          | w when w = Base.true_lit -> emit_catch ()
	  | _ -> raise Base.Presupposition_error
	end
      | Neut z ->
        let zz = neut_lp_value no_lambda no_pair z in
        let cases = Base.Enum_map.add Base.false_lit (emit_base ()) (
          Base.Enum_map.add Base.true_lit (emit_catch ()) Base.Enum_map.empty)
        in
        ref None, Switch(zz, cases)
      | _ -> raise Base.Presupposition_error
    in
    (* invoke p t inside n will be translated as follows. *)
    el_lp_block no_lambda pair p
  in
  let el_of_component = function
    | Component1 n -> Neut n
    | Component2(a, b) -> Invk(Neut a, b)
    | Component3(a, b, c) -> Invk(Pair(Neut a, b), c)
  in
  el_iy_block invoke' yield (el_of_component n)

(* This function is used to translate Value.Local into a block. *)
and local (invoke:invoke) (yield:yield) (sz:size) (ini:el) (n:component):block =
  let open Value in
  let alloca = next_alloca () in
  (* This is how an invocation will be compiled inside n. *)
  let invoke' (p:el) (t:el->block):block =
    (* p is of sigma type: x is the enum value and y the method argument. *)
    let pair (x:el) (y:el):block =
      let emit_base () = invoke y t in
      let emit_getset () =
        (* y is a function local->local. *)
        let get_var = Var.dummy () in
        let get_value = Neut(Var(get_var)) in
        let new_value = el_lp_value no_lambda no_pair (Eval.mkApp y get_value) in
        let set_var = Var.dummy () in
        let set_value = Neut(Var(set_var)) in
        let cont_block = t set_value in
        ref None, Load_and_store(alloca, get_var, new_value, set_var, cont_block)
      in
      (* The enum value x may need to be computed. *)
      match x with
      | Imm(Base.Enum_imm(e, l)) when Base.Enum_set.equal e Base.bool_enum ->
        begin
          match l with
          | w when w = Base.false_lit -> emit_base ()
          | w when w = Base.true_lit -> emit_getset ()
	  | _ -> raise Base.Presupposition_error
	end
      | Neut z ->
        let zz = neut_lp_value no_lambda no_pair z in
        let cases = Base.Enum_map.add Base.false_lit (emit_base ()) (
          Base.Enum_map.add Base.true_lit (emit_getset ()) Base.Enum_map.empty)
        in
        ref None, Switch(zz, cases)
      | _ -> raise Base.Presupposition_error
    in
    (* invoke p t inside n will be translated as follows. *)
    el_lp_block no_lambda pair p
  in
  (* The initial value is of base type (in fact, enum type). *)
  let ini' = el_lp_value no_lambda no_pair ini in
  let el_of_component = function
    | Component1 n -> Neut n
    | Component2(a, b) -> Invk(Neut a, b)
    | Component3(a, b, c) -> Invk(Pair(Neut a, b), c)
  in
  let body = el_iy_block invoke' yield (el_of_component n) in
  ref None, Declare_alloca(alloca, sz, ini', body)

and range (invoke:invoke) (yield:yield) (a:value) (b:value) :block =
  let x = Var.dummy () in
  let xx = Value.Neut(Value.Var x) in
  let lbl = next_label () in
  (* No need to memoize this yield function, as it is trivial. *)
  let yield' _ = ref None, Goto lbl in
  let body = invoke xx yield' in
  let term = yield Value.unit_cst in
  ref None, Range(a, b, x, lbl, body, term)


(* On the toplevel, we'd like to yield by returning from the
   function. *)
let ret_yield x = ref None, Ret(el_lp_value no_lambda no_pair x)



(*

Here is some code that I cound useful for debugging.

let rep str =
  let ctx = Initial.ctx in
  let expr = Syntax.expr Lex.token (Lexing.from_string str) in
  let _A, a = Check_expr.infer ctx expr in
  assert(let _B = Check_term.mono ctx a in
         Value.eq_set _A _B;
         true);
  let aa = Eval.mono (Ctx.assign ctx) a in
  (* Format.printf "%a is %a;\n" Printing.el aa Printing.set _A; *)
  aa


let test () =
  let a = rep "(
val (+) = mod32::+;
val (<) = mod32::<;
val (==) = mod32::==;
val fun (x bool) && (y bool) = x ? y : false;
val fun (x bool) || (y bool) = x ? true : y;
val fun (x i32) <= (y i32) = x < y || x == y;
val and = mod32::and;
val fun fib(x i32) = purify i32 {
  new a = new_i32(0);
  new b = new_i32(1);
  for _ in 0..x {
    val old_a = get a;
    val old_b = get b;
    a := old_b;
    b := old_a + old_b;
  }
  yield(get a);
};
val fun euler3(max i32) = purify i32 {
  new sum = new_i32(0);
  for i in 0..5 {
    val a = fib(i);
    // Count a if a <= max and the lsb of a is unset.
    if a < max + 1 && and(a, 1) == 0 {
      sum := sum + a;
    }
  }
  yield(get sum);
};
euler3)"
  in
  let v x = Value.Neut (Value.Var (Base.Variable "x")) in
  let b = Eval.mkApp (Eval.mkApp a (v "x")) (v "y") in
  let c = el_lp_value no_lambda no_pair b in
  c


open Ipl_compile;;
#install_printer format_block;;
#install_printer format_value;;
#install_printer Printing.el;;
#install_printer Printing.neut;;

#trace neut_iy_block;;
#trace el_iy_block;;
#trace neut_lp_block;;
#trace el_lp_block;;
#trace neut_lp_value;;
#trace el_lp_value;;

#trace neut_iy_block';;
#trace el_iy_block';;
#trace neut_lp_block';;
#trace el_lp_block';;
#trace neut_lp_value';;
#trace el_lp_value';;

test ();;


*)
