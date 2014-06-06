# INTUITIONISTIC TYPE THEORY PROGRAMMING LANGUAGE
#
# Copyright (c) 2006-2013 Johan G. Granstroem.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

OCAMLC=ocamlc
OCAMLOPT=ocamlopt
OCAMLDEP=ocamldep
OCAMLLEX=ocamllex
OCAMLYACC=ocamlyacc
LLC=llc
LLVM_DIS=llvm-dis
# Add non-standard location for LLVM bindings here. For example:
# INCLUDES=-I /my/non-standard/lib
INCLUDES=
OCAMLFLAGS=$(INCLUDES) -g
OCAMLOPTFLAGS=$(INCLUDES) -p

# ========== MAIN TARGETS

all: test_term test_expr test_llvm iplc iplc.opt ipltop

test: all
	./test_term
	./test_expr
	./test_llvm
	@for x in $$(ls examples/*.ipl); do echo "checking" $$x "done." && ./iplc $$x; done
	@for x in $$(ls examples/*.ipl); do echo "checking (opt)" $$x "done." && ./iplc.opt $$x; done

clean:
	rm -f test_term test_expr test_llvm iplc iplc.opt ipltop syntax.mli syntax.ml lex.ml
	rm -f *.cm[ioxa]
	rm -f examples/*.bc
	rm -f examples/*.s
	rm -f examples/*.o
	rm -f examples/*.ll
	rm -f *.o
	rm -f *.s
	rm -f syntax.output
	rm -f *~
	rm -f examples/*~
	rm -f .depend

# ========== PATTERN RULES

%.cmo: %.ml
	$(OCAMLC) $(OCAMLFLAGS) -c $<

%.cmi: %.mli
	$(OCAMLC) $(OCAMLFLAGS) -c $<

%.cmx: %.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

%.ml %.mli: %.mly
	$(OCAMLYACC) -v $<

%.ml: %.mll
	$(OCAMLLEX) $<

%.bc: %.ipl iplc
	./iplc $<

%.s: %.bc
	$(LLC) $<

%.ll: %.bc
	$(LLVM_DIS) $<

%.o: %.s
	$(CC) -c $<

.PRECIOUS: %.mli %.mly

# ========== LEVEL 1

LEVEL1=var.cmo base.cmo value.cmo term.cmo eval.cmo printing.cmo reify.cmo ctx.cmo check_term.cmo initial.cmo

TEST_TERM_OBJS=$(LEVEL1) test_term.cmo
test_term: $(TEST_TERM_OBJS)
	$(OCAMLC) $(OCAMLFLAGS) $(TEST_TERM_OBJS) -o test_term

# ========== LEVEL 2

LEVEL2=$(LEVEL1) expr.cmo check_expr.cmo lex.cmo syntax.cmo

lex.ml: syntax.cmi syntax.cmo

TEST_EXPR_OBJS=$(LEVEL2) test_expr.cmo
test_expr: $(TEST_EXPR_OBJS)
	$(OCAMLC) $(OCAMLFLAGS) $(TEST_EXPR_OBJS) -o test_expr

# ========== LEVEL 3

LEVEL3=$(LEVEL2) ipl_compile.cmo ipl_llvm.cmo

LLVM_LIBS=llvm.cma llvm_executionengine.cma llvm_analysis.cma llvm_scalar_opts.cma llvm_target.cma llvm_bitwriter.cma
LLVM_FLAGS=-ccopt -lstdc++

TEST_LLVM_OBJS=$(LEVEL3) test_llvm.cmo
test_llvm: $(TEST_LLVM_OBJS)
	$(OCAMLC) $(OCAMLFLAGS) $(LLVM_FLAGS) $(LLVM_LIBS) $(TEST_LLVM_OBJS) -o test_llvm

IPLC_OBJS=$(LEVEL3) iplc.cmo
iplc: $(IPLC_OBJS)
	$(OCAMLC) $(OCAMLFLAGS) $(LLVM_FLAGS) $(LLVM_LIBS) $(IPLC_OBJS) -o iplc

# Flag -noassert could be added here, but last time I checked, it made little difference.
iplc.opt: $(IPLC_OBJS:.cmo=.cmx)
	$(OCAMLOPT) $(OCAMLOPTFLAGS) $(LLVM_FLAGS) $(LLVM_LIBS:.cma=.cmxa) $(IPLC_OBJS:.cmo=.cmx) -o iplc.opt

ipltop: $(IPLC_OBJS)
	ocamlmktop -custom -ccopt -Wno-write-strings -g unix.cma $(LLVM_FLAGS) $(LLVM_LIBS) $(IPLC_OBJS) -o ipltop

# ========== DEPENDENCIES

.depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

-include .depend
