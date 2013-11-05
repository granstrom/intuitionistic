type t =
| Variable of string
| Dummy of int
| Print of int

let no = Variable ""

let format : Format.formatter -> t -> unit =
  fun f ->
    function
    | Variable "" -> Format.fprintf f "_"
    | Variable s -> Format.fprintf f "%s" s
    | Dummy x -> Format.fprintf f "#%d" x
    | Print x -> Format.fprintf f "@@%d" x

let dummy : unit -> t =
  let counter = ref 1 in
  fun () ->
    let result = !counter in
    counter := result + 1;
    Dummy result

let counter = ref 1

let print_dummy () =
  let result = !counter in
  counter := result + 1;
  Print result

let reset_print () =
  counter := 0

(* TODO: validate format of x. *)
let of_string (x:string) =
  assert(x <> "");
  Variable x
