The intuitionistic programming language (IPL) is a new open source programming language, implemented in OCaml, combining a very high level of abstraction with compilation to efficient LLVM bytecode.

The semantics of IPL is intuitionistic type theory without recursive types. Type-theoretic constructs, such as lambda abstraction, pairing, and proof objects, are eliminated at compile time using a new algorithm which translates any type-theoretic term of base type, in a context where all variables are of base type, into clean LLVM bytecode.

The following language level features are supported: first class pure functions, first class dependent types, generic programming, first class interfaces, first class procedures, fully automatic memory management, no runtime requirements, no runtime garbage collection, logical consistency, precise type-theoretic semantics, theorem proving capabilities.

See http://intuitionistic.org for more information.