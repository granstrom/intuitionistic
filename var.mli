type t
val no :t
val format :Format.formatter -> t -> unit
val dummy :unit -> t
val print_dummy :unit -> t
val reset_print :unit -> unit
val of_string :string -> t
