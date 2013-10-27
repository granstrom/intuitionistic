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
  LLVM documentation:
  http://www.class.umd.edu/old/enee/759c/llvm/llvm-3.0-install/obj/docs/ocamldoc/html/
*)

open Base

type llvalue = Llvm.llvalue
type lltype = Llvm.lltype
type llbasicblock = Llvm.llbasicblock
type llmodule = Llvm.llmodule
type imm = Value.imm
type el = Value.el
type neut = Value.neut
type value = Ipl_compile.value
type block = Ipl_compile.block
type label = Ipl_compile.label
type target = Ipl_compile.target
type alloca = Ipl_compile.alloca
type size = Value.size
let dump_value = Llvm.dump_value
let dump_module = Llvm.dump_module

(* No need to use any other context. *)
let global_context = Llvm.global_context ()
let builder = Llvm.builder global_context
let void = Llvm.void_type global_context
let append_block = Llvm.append_block global_context
let i8 = Llvm.i8_type global_context
let i16 = Llvm.i16_type global_context
let i32 = Llvm.i32_type global_context
let i64 = Llvm.i64_type global_context
let const_int = Llvm.const_int
let build_zext t v = Llvm.build_zext v t "" builder
let to_bool = build_zext i32
let const_of_int64 = Llvm.const_of_int64
let type_of = Llvm.type_of
let insertion_block () = Llvm.insertion_block builder
let block_terminator = Llvm.block_terminator
let insertion_block_terminator () =
  block_terminator (insertion_block ())
let position_at_end bb =
  Llvm.position_at_end bb builder
let build_br bb =
  Llvm.build_br bb builder |> ignore
let function_and_entry bb =
  let the_function = Llvm.block_parent bb in
  let entry_bb = Llvm.entry_block the_function in
  the_function, entry_bb
let new_block name =
  append_block name (Llvm.block_parent (insertion_block ()))

let lltype_of_size:size -> lltype =
  function
  | Value.I8 -> i8
  | Value.I16 -> i16
  | Value.I32 -> i32
  | Value.I64 -> i64

(* Find the ordinal number of enum constant c inside enum cs. *)
let enum_ordinal cs c =
  match Base.Enum_set.split c cs with
  | below, true, _ -> Base.Enum_set.cardinal below
  | _ -> raise Base.Presupposition_error

(* Enum constants are represented by i32 for now. *)
let mk_enum_const cs c = const_int i32 (enum_ordinal cs c)

(* We actually rely on the fact that false < true. *)
let _ = assert(enum_ordinal bool_enum bool_true_lit = 1)
let _ = assert(enum_ordinal bool_enum bool_false_lit = 0)

let llvalue_of_imm : imm -> llvalue =
  let open Value in
  function
  | Imm8 x -> const_int i8 (Char.code x)
  | Imm16 x -> const_int i16 x
  | Imm32 x -> const_of_int64 i32 (Int64.of_int32 x) true
  | Imm64 x -> const_of_int64 i64 x true
  | Enum_cst(cs, c) -> mk_enum_const cs c
  (* Due to eager evaluation, refl objects will need to be compiled
     (e.g., for sdiv), but they will not make it into the code. *)
  | Refl -> Llvm.undef i8

let lltype_of_imm:imm -> lltype =
  function
  | Value.Imm8 _ -> i8
  | Value.Imm16 _ -> i16
  | Value.Imm32 _ -> i32
  | Value.Imm64 _ -> i64
  | Value.Enum_cst(_, _) -> i32
  | Value.Refl -> i8

(* Create a shift argument of type a with value y. Only the lowest
   bits of y are taken in to account, depending on the size of a. *)
let mk_shift a y =
  let ty = lltype_of_size a in
  let yy = match a with
    | Value.I8 -> y
    | _ -> build_zext ty y
  in
  let tysz = match a with
    | Value.I8 -> 0x07
    | Value.I16 -> 0x0f
    | Value.I32 -> 0x1f
    | Value.I64 -> 0x3f
  in
  Llvm.build_and yy (const_int ty tysz) "shiftprep" builder

let builtin op vals =
  match op, vals with
  | Value.Add(_), [x; y] -> Llvm.build_add x y "" builder
  | Value.Sub(_), [x; y] -> Llvm.build_sub x y "" builder
  | Value.Neg(_), [x]    -> Llvm.build_neg x "" builder
  | Value.Mul(_), [x; y] -> Llvm.build_mul x y "" builder
  | Value.Srem(_), [x; y; _] -> Llvm.build_srem x y "" builder
  | Value.Sdiv(_), [x; y; _] -> Llvm.build_sdiv x y "" builder
  | Value.Xor _, [x; y] -> Llvm.build_xor x y "" builder
  | Value.Ior _, [x; y] -> Llvm.build_or  x y "" builder
  | Value.And _, [x; y] -> Llvm.build_and x y "" builder
  | Value.Not _, [x]    -> Llvm.build_not x "" builder
  | Value.Lsl a, [x; y] -> Llvm.build_shl  x (mk_shift a y) "" builder
  | Value.Lsr a, [x; y] -> Llvm.build_lshr x (mk_shift a y) "" builder
  | Value.Asr a, [x; y] -> Llvm.build_ashr x (mk_shift a y) "" builder
  (* Sign extend y to b. *)
  | Value.Sext(a, b), [y] when a < b ->
    Llvm.build_sext y (lltype_of_size b) "" builder
  (* Truncate y to b. *)
  | Value.Sext(a, b), [y] when a > b ->
    Llvm.build_trunc y (lltype_of_size b) "" builder
  | Value.Sext(a, b), [y] (* when a = b *) -> y
  | Value.Aeq(_), [x; y] ->
    to_bool (Llvm.build_icmp Llvm.Icmp.Eq  x y "" builder)
  | Value.Less(_), [x; y] ->
    to_bool (Llvm.build_icmp Llvm.Icmp.Slt x y "" builder)
  (* TODO: can a proof object end up being compiled? If so, simply add
     an undef instruction here instead of raising an exception. *)
  | _ -> raise Presupposition_error

let emit_alloca name tt =
  let start_bb = insertion_block () in
  let _, entry_bb = function_and_entry start_bb in
  position_at_end entry_bb;
  let local_var = Llvm.build_alloca tt name builder in
  position_at_end start_bb;
  local_var

(* A name-value map, mapping variables to LLVM values. *)
type var_map = llvalue Base.var_map
let var_map :var_map ref = ref Base.Var_map.empty

module Label_map = Map.Make(struct
  type t = label
  let compare = compare
end)
let lbl_map : llbasicblock Label_map.t ref = ref Label_map.empty

module Target_map = Map.Make(struct
  type t = target
  let compare = compare
end)
let target_map : (llbasicblock * llvalue option ref) Target_map.t ref
    = ref Target_map.empty

module Alloca_map = Map.Make(struct
  type t = alloca
  let compare = compare
end)
let alloca_map : llvalue Alloca_map.t ref = ref Alloca_map.empty

let rec compile_block (block:block) :unit =
  let open Ipl_compile in
  begin
    match !(fst block) with
    | None -> ()
    | Some (Label name as lbl) ->
      (* Declare this label for the rest of this session. *)
      let bb = new_block (Printf.sprintf "lbl_%d" name) in
      lbl_map := Label_map.add lbl bb !lbl_map;
      build_br bb;
      position_at_end bb;
  end;
  match snd block with
  | Switch(v, bs) ->
    begin
      match Enum_map.cardinal bs with
      | 0 -> ()
      | 1 -> compile_block (snd (Enum_map.choose bs))
      | _ ->
        let start_bb = insertion_block () in
        let unreachable_bb = new_block "unreachable" in
        position_at_end unreachable_bb;
        Llvm.build_unreachable builder |> ignore;
        position_at_end start_bb;
        let vv = compile_value v in
        let switch =
          Llvm.build_switch vv unreachable_bb (Enum_map.cardinal bs) builder
        in
        let cnt = ref 0 in
        let compile_case (Enum_lit x) ct =
          let bb = new_block x in
          Llvm.add_case switch (const_int i32 !cnt) bb;
          cnt := !cnt + 1;
          position_at_end bb;
          compile_block ct;
        in
        Enum_map.iter compile_case bs;
    end
  | Ret(v) ->
    Llvm.build_ret (compile_value v) builder |> ignore
  | End_purify(v, lbl) ->
    let vv = compile_value v in
    let vbb = insertion_block () in
    let bb, phi = Target_map.find lbl !target_map in
    begin
      match !phi with
      | None ->
        position_at_end bb;
        let p = Llvm.build_phi [vv, vbb] "purify" builder in
        phi := Some p;
        position_at_end vbb;
      | Some p ->
        Llvm.add_incoming (vv, vbb) p;
    end;
    build_br bb
  | Block_ref(lbl)
  | Goto(lbl) ->
    let bb = Label_map.find lbl !lbl_map in
    build_br bb;
  | Range(from, t0, x, lbl, body, next) ->
      (*
        start:
        ...
        %from = <code for from>
        %to = <code for to>
        begin:
        %from' = phi [loop:%from''; prev:%from]
        if %from' < %to goto loop else goto end;
        loop:
        <code for body with x = from' and lbl = loop_end>
        loop_end:
        %from'' = %from' + 1
        goto begin:
        end:
        <code for next>
      *)
    let t0' = compile_value t0 in
    let from' = compile_value from in
    let start_bb = insertion_block () in
    let begin_bb = new_block "begin" in
    let loop_bb = new_block "loop" in
    let loop_end_bb = new_block "loop_end" in
    let end_bb = new_block "end" in
    build_br begin_bb;
    position_at_end begin_bb;
    let from'' = Llvm.build_phi [from', start_bb] "range" builder in
    let cond = Llvm.build_icmp Llvm.Icmp.Ult from'' t0' "" builder in
    Llvm.build_cond_br cond loop_bb end_bb builder |> ignore;
    (* -------- *)
    position_at_end loop_bb;
    let old_var_map = !var_map in
    var_map := Base.Var_map.add x from'' old_var_map;
    let old_lbl_map = !lbl_map in
    lbl_map := Label_map.add lbl loop_end_bb old_lbl_map;
    compile_block body;
    position_at_end loop_end_bb;
    let from''' = Llvm.build_add from'' (Llvm.const_int i32 1) "" builder in
    Llvm.add_incoming (from''', loop_end_bb) from'';
    build_br begin_bb;
    (* -------- *)
    position_at_end end_bb;
    var_map := old_var_map;
    lbl_map := old_lbl_map;
    compile_block next
  | Declare_alloca(alloca, sz, init, body) ->
    let local_var = emit_alloca "local_cell" (lltype_of_size sz) in
    let old_alloca_map = !alloca_map in
    alloca_map := Alloca_map.add alloca local_var old_alloca_map;
    let init_n = compile_value init in
    Llvm.build_store init_n local_var builder |> ignore;
    compile_block body;
    alloca_map := old_alloca_map
  | Load_and_store(alloca, x, v, y, body) ->
    let local_var = Alloca_map.find alloca !alloca_map in
    let local_val = Llvm.build_load local_var "get" builder in
    let old_var_map = !var_map in
    var_map := Base.Var_map.add x local_val old_var_map;
    let vv = compile_value v in
    (* Store new value in cell. *)
    Llvm.build_store vv local_var builder |> ignore;
    (* Discard binding for x by using old_var_map. *)
    var_map := Base.Var_map.add y vv old_var_map;
    compile_block body;
    var_map := old_var_map

and compile_value :value->llvalue =
  let open Ipl_compile in
  function
  | Select(v, vs) ->
    begin
      match Enum_map.cardinal vs with
      | 0 -> Llvm.build_unreachable builder
      | 1 -> compile_value (snd (Enum_map.choose vs))
      | _ ->
        let start_bb = insertion_block () in
        let unreachable_bb = new_block "unreachable" in
        let merge_bb = new_block "merge" in
        position_at_end unreachable_bb;
        Llvm.build_unreachable builder |> ignore;
        position_at_end start_bb;
        let vv = compile_value v in
        let switch =
          Llvm.build_switch vv unreachable_bb (Enum_map.cardinal vs) builder
        in
        let cnt = ref 0 in
        let compile_case (Enum_lit x, ct) =
          let bb = new_block x in
          Llvm.add_case switch (const_int i32 !cnt) bb;
          cnt := !cnt + 1;
          position_at_end bb;
          let ct_value = compile_value ct in
          let after_bb = insertion_block () in
          build_br merge_bb;
          ct_value, after_bb
        in
        (* The return values of compile_case are modelled to be input to
           'build_phi'. *)
        let incoming = Enum_map.bindings vs |> List.map compile_case in
        position_at_end merge_bb;
        let phi = Llvm.build_phi incoming "merge" builder in
        phi
    end
  | Purify(Target name as target, body) ->
    let new_bb = new_block (Printf.sprintf "target_%d" name) in
    let old_target_map = !target_map in
    let phi = ref None in
    target_map := Target_map.add target (new_bb, phi) !target_map;
    compile_block body;
    target_map := old_target_map;
    position_at_end new_bb;
    begin
      match !phi with
      | None -> Llvm.build_unreachable builder
      | Some p -> p
    end
  | Op(op, vals) -> builtin op (List.map compile_value vals)
  | Var(x) -> Base.Var_map.find x !var_map
  | Imm(i) -> llvalue_of_imm i



let setup_module name =
  let the_module = Llvm.create_module global_context name in
  let open Llvm_executionengine in
  ignore (initialize_native_target ());
  (* Create the JIT. *)
  let the_execution_engine = ExecutionEngine.create the_module in
  let the_fpm = Llvm.PassManager.create_function the_module in
  (* Set up the optimizer pipeline.  Start with registering info about how the
   * target lays out data structures. *)
  Llvm_target.DataLayout.add
    (ExecutionEngine.target_data the_execution_engine) the_fpm;
  (* Promote alloca slots that have only loads and stores to registers. *)
  Llvm_scalar_opts.add_memory_to_register_promotion the_fpm;
  (* Simplify the control flow graph (deleting unreachable blocks, etc). *)
  Llvm_scalar_opts.add_cfg_simplification the_fpm;
  (* Loop invariant code motion. *)
  Llvm_scalar_opts.add_licm the_fpm;
  (* Induction variable simplification. *)
  Llvm_scalar_opts.add_ind_var_simplification the_fpm;
  (* Loop deletion. *)
  Llvm_scalar_opts.add_loop_deletion the_fpm;
  (* Do simple "peephole" optimizations and bit-twiddling optzn. *)
  Llvm_scalar_opts.add_instruction_combination the_fpm;
  (* Reassociate expressions. *)
  Llvm_scalar_opts.add_reassociation the_fpm;
  (* Combine instructions. *)
  Llvm_scalar_opts.add_instruction_combination the_fpm;
  (* Propagate constants. *)
  Llvm_scalar_opts.add_constant_propagation the_fpm;
  (* Sparse conditional constant propagation. *)
  Llvm_scalar_opts.add_sccp the_fpm;
  (* Eliminate Common SubExpressions. *)
  Llvm_scalar_opts.add_gvn the_fpm;
  (* Simplify the control flow graph (deleting unreachable blocks, etc). *)
  Llvm_scalar_opts.add_cfg_simplification the_fpm;
  (* Eliminate Common SubExpressions. *)
  Llvm_scalar_opts.add_gvn the_fpm;
  (* Simplify the control flow graph (deleting unreachable blocks, etc). *)
  Llvm_scalar_opts.add_cfg_simplification the_fpm;
  (* Aggressive dead code elimination. *)
  Llvm_scalar_opts.add_aggressive_dce the_fpm;
  Llvm.PassManager.initialize the_fpm |> ignore;
  the_execution_engine, the_module, the_fpm

type llproto = lltype * (var * lltype) list

let setup_fn the_module name (proto:llproto):Llvm.llvalue * llvalue Var_map.t =
  let names = snd proto |> List.map fst |> Array.of_list in
  let args = snd proto |> List.map snd |> Array.of_list in
  let cod = fst proto in
  let ft = Llvm.function_type cod args in
  let f =
    match Llvm.lookup_function name the_module with
    | None -> Llvm.declare_function name ft the_module
    | Some _ -> raise Presupposition_error
  in
  let p = Llvm.params f in
  let nameval i a =
    let Variable n = names.(i) in
    Llvm.set_value_name n a;
    Variable n, a
  in
  let nvals = Array.mapi nameval p in
  let m = Array.fold_right (fun (x, y) -> Base.Var_map.add x y)
    nvals Base.Var_map.empty
  in
  f, m

let main_engine, main_module, main_fpm = setup_module "IPL"

let compile_function_ name (proto:llproto) (body:Value.el) invoke =
  (* Format.printf "Body:%a\n@?" Printing.el body; *)
  let the_function, named_values = setup_fn main_module name proto in
  (* Create an entry block for alloca. *)
  let entry_bb = append_block "entry" the_function in
  (* Create a new basic block to start insertion into. *)
  let start_bb = append_block "start" the_function in
  Llvm.position_at_end start_bb builder;
  try
    let block = Ipl_compile.el_iy_block
      invoke
      Ipl_compile.ret_yield
      body
    in
    var_map    := named_values;
    lbl_map    := Label_map.empty;
    target_map := Target_map.empty;
    alloca_map := Alloca_map.empty;
    compile_block block;
    Ipl_compile.reset_counters ();
    (* Now that all alloca instructions have been inserted to the
       entry block, have it jump to the start block at the end of the
       entry block. *)
    Llvm.position_at_end entry_bb builder;
    build_br start_bb;
    (* Llvm.dump_module main_module; *)
    (* Validate the generated code, checking for consistency. *)
    Llvm_analysis.assert_valid_function the_function;
    (* Optimize the function. *)
    let _ = Llvm.PassManager.run_function the_function main_fpm in
    Llvm_analysis.assert_valid_function the_function;
    (* Llvm.dump_module main_module; *)
    the_function
  with
  | e ->
    Llvm.delete_function the_function;
    raise e

type proto = Value.size * (var * Value.size) list
let compile_function name (proto:proto) (body:Value.el) invoke =
  let cod = lltype_of_size (fst proto) in
  let dom = snd proto |> List.map (fun (x, y) ->
    x, lltype_of_size y)
  in
  compile_function_ name (cod, dom) body invoke

let generic_of_imm:imm -> Llvm_executionengine.GenericValue.t =
  let open Llvm_executionengine in
  function
  | Value.Imm8 x -> GenericValue.of_int i8 (Char.code x)
  | Value.Imm16 x -> GenericValue.of_int i16 x
  | Value.Imm32 x -> GenericValue.of_int32 i32 x
  | Value.Imm64 x -> GenericValue.of_int64 i64 x
  | Value.Enum_cst(cs, c) -> GenericValue.of_int i32 (enum_ordinal cs c)
  | Value.Refl -> raise Presupposition_error

let generic_eq_imm (y:Llvm_executionengine.GenericValue.t) =
  let open Llvm_executionengine in
  function
  | Value.Imm8 x -> GenericValue.as_int y = Char.code x
  | Value.Imm16 x -> GenericValue.as_int y = x
  | Value.Imm32 x -> GenericValue.as_int32 y = x
  | Value.Imm64 x -> GenericValue.as_int64 y = x
  | Value.Enum_cst(cs, c) -> GenericValue.as_int y = enum_ordinal cs c
  | Value.Refl -> raise Presupposition_error

let size_of_imm = function
  | Value.Imm8 _ -> Value.I8
  | Value.Imm16 _ -> Value.I16
  | Value.Imm32 _ -> Value.I32
  | Value.Imm64 _ -> Value.I64
  | Value.Enum_cst(_, _) -> Value.I32
  | Value.Refl -> raise Presupposition_error
