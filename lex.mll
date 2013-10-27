{

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

open Syntax
open Lexing

let incr_lineno lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <- { pos with
    pos_lnum = pos.pos_lnum + 1;
    pos_bol = pos.pos_cnum;
  }

type details =
  | Illegal_character of char
  | Literal_overflow of string
  | Invalid_hex

let format_details (fmt:Format.formatter) (err:details) :unit =
  match err with
  | Illegal_character c ->
    Format.fprintf fmt "illegal character (%s)" (Char.escaped c)
  | Literal_overflow ty ->
    Format.fprintf fmt "integer literal exceeds representable range for \
                        integers of type %s" ty
  | Invalid_hex ->
    Format.fprintf fmt "hex literal must be of size 2, 4, 8, or 16"

exception Error of (string * Base.pos) * details

let format_error (fmt:Format.formatter)
    ((fname, (a, b)), (err)):unit =
  Format.fprintf fmt "%s:%d.%d: %a" fname a b format_details err

let pos_of_lexpos (p:Lexing.position) :Base.pos =
  (p.Lexing.pos_lnum, p.Lexing.pos_cnum - p.Lexing.pos_bol)

let currpos (lexbuf:Lexing.lexbuf):string*Base.pos =
  lexbuf.lex_curr_p.pos_fname, (pos_of_lexpos (lexbuf.lex_curr_p))

let keyword_table =
  let bindings = [
    "eq", AEQ;
    "assert", ASSERT;
    "block", BLOCK;
    "call", CALL;
    "case", CASE;
    "compile", COMPILE;
    "dep", DEP;
    "do", DO;
    "else", ELSE;
    "enum", ENUM;
    "for", FOR;
    "fst", FST;
    "fun", FUN;
    "get", GET;
    "if", IF;
    "in", IN;
    "interpret", INTERPRET;
    "is", IS;
    "interface", INTERFACE;
    "meth", METH;
    "new", NEW;
    "opaque", OPAQUE;
    "purify", PURIFY;
    "refl", REFL;
    "snd", SND;
    "struct", STRUCT;
    "subst", SUBST;
    "switch", SWITCH;
    "test", TEST;
    "tuple", TUPLE;
    "type", TYPE;
    "union", UNION;
    "val", VAL;
    "yield", YIELD;
  ] in
  let tab = Hashtbl.create (List.length bindings) in
  List.iter (fun (a, b) -> Hashtbl.add tab a b) bindings;
  tab

let int_of_hex c =
  match c with
  | x when '0' <= x && x <= '9' -> (Char.code x) - (Char.code '0')
  | x when 'a' <= x && x <= 'h' -> (Char.code x) - (Char.code 'a') + 10
  | x when 'A' <= x && x <= 'H' -> (Char.code x) - (Char.code 'A') + 10
  | _ -> raise Base.Presupposition_error

let int64_of_hex_string str =
  let open Int64 in
  let result : int64 ref = ref zero in
  for i = 0 to String.length str - 1 do
    result := add (shift_left !result 4) (of_int (int_of_hex str.[i]))
  done;
  !result

let i64_of_string pos str =
  try
    Value.Imm64(Int64.of_string str)
  with
  | Failure _ -> raise (Error(pos, Literal_overflow "i64"))

let i32_of_string pos str =
  try
    Value.Imm32(Int32.of_string str)
  with
  | Failure _ -> raise (Error(pos, Literal_overflow "i32"))

let i16_of_string pos str =
  try
    let i = int_of_string str in
    if i > 32767 || i < -32768 then raise (Failure "")
    else Value.Imm16(i)
  with
  | Failure _ -> raise (Error(pos, Literal_overflow "i16"))

let i8_of_string pos str =
  try
    let i = int_of_string str in
    if i > 127 || i < -128 then raise (Failure "")
    else Value.Imm8(Char.chr i)
  with
  | Failure _ -> raise (Error(pos, Literal_overflow "i16"))


(* end of preamble *)
}

let newline = ('\010' | '\013' | "\013\010")
let blank = [' ' '\009' '\012']
let letter = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let hex = digit | ['a'-'h' 'A'-'H']
let identchar = letter | digit | '_'
let integer = '-'? digit+

rule token = parse
  | "//"
    {
      comment lexbuf
    }

  | newline
    {
      incr_lineno lexbuf;
      token lexbuf
    }

  | blank+
    {
      token lexbuf
    }

  | letter identchar*
  | '_' identchar+ as s
    {
      try Hashtbl.find keyword_table s
      with Not_found -> IDENT s
    }
  | "_"  { BLANK }

  | (integer as d) 'q' { IMM (i64_of_string (currpos lexbuf) d) }
  | integer as d       { IMM (i32_of_string (currpos lexbuf) d) }
  | (integer as d) 's' { IMM (i16_of_string (currpos lexbuf) d) }
  | (integer as d) 'c' { IMM (i8_of_string (currpos lexbuf) d) }

  | "0x" (hex+ as d)
      {
	let p = int64_of_hex_string d in
	IMM (
	  match String.length d with
	  | 2 -> Value.Imm8 (Char.chr (Int64.to_int p))
	  | 4 -> Value.Imm16 (Int64.to_int p)
	  | 8 -> Value.Imm32 (Int64.to_int32 p)
	  | 16 -> Value.Imm64 p
          | _ -> raise (Error(currpos lexbuf, Invalid_hex))
	)
      }

  | "&&" { AND_AND }
  | "@" { AT }

  | "!"  { BANG }
  | "!=" { BANG_EQ }
  | "||" { BAR_BAR }

  | "^^" { CARET_CARET }

  | "::" { COLON_COLON }
  | ":=" { COLON_EQ }
  | ":"  { COLON }
  | ","  { COMMA }

  | "."  { DOT }
  | ".." { DOT_DOT }

  | "="  { EQ }
  | "==" { EQ_EQ }
  | "===" { EQ_EQ_EQ }
  | "=>" { EQ_GREATER }

  | ">"  { GREATER }
  | ">=" { GREATER_EQ }

  | "<"  { LESS }
  | "<=" { LESS_EQ }

  | "-"  { MINUS }
  | "->" { MINUS_GREATER }

  | "+"  { PLUS }
  | "++"  { PLUS_PLUS }

  | "?"  { QUESTION }
  | "??" { QUESTION_QUESTION }
  | "'"  { QUOTE }

  | ";"  { SEMI }
  | "*"  { STAR }
  | "**"  { STAR_STAR }

  | "~"  { TILDE }

  (* Delimiter tokens *)
  | "{"  { LBRACE }
  | "["  { LBRACKET }
  | "("  { LPAREN }
  | "}"  { RBRACE }
  | "]"  { RBRACKET }
  | ")"  { RPAREN }

  | eof { EOF }

  | _ as c { raise (Error(currpos lexbuf, Illegal_character c)) }

and comment = parse
  | newline
    {
      incr_lineno lexbuf;
      token lexbuf
    }
  | _ { comment lexbuf }
  | eof { EOF }
