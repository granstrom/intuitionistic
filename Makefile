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

# Release instructions.
# make clean
# cd ..
# tar -czf ipl`date "+%Y%m%d"`.tar.gz ipl/


OCAMLC=ocamlc
OCAMLOPT=ocamlopt
OCAMLDEP=ocamldep
INCLUDES=
OCAMLFLAGS=$(INCLUDES) -g
OCAMLOPTFLAGS=$(INCLUDES)

# ========== MAIN TARGETS

all: test_term test_expr test_llvm iplc iplc.opt ipltop

test: all
	./test_term
	./test_expr
	./test_llvm
	for x in $$(ls examples/*.ipl); do echo "checking..." $$x "done." && ./iplc $$x; done

# ========== COMMON RULES

.SUFFIXES: .ml .mli .cmo .cmi .cmx

.ml.cmo:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.mli.cmi:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

clean:
	rm -f test_term test_expr test_llvm iplc iplc.opt ipltop syntax.mli syntax.ml lex.ml
	rm -f *.cm[ioxa]
	rm -f examples/*.bc
	rm -f examples/*.ll
	rm -f *.o
	rm -f *.s
	rm -f syntax.output
	rm -f *~
	rm -f .depend

# ========== LEVEL 1

LEVEL1=base.cmo value.cmo term.cmo eval.cmo printing.cmo reify.cmo ctx.cmo check_term.cmo

TEST_TERM=$(LEVEL1) test_term.cmo
test_term: $(TEST_TERM)
	$(OCAMLC) $(OCAMLFLAGS) $(TEST_TERM) -o test_term

# ========== LEVEL 2

LEVEL2=$(LEVEL1) expr.cmo initial.cmo check_expr.cmo lex.cmo syntax.cmo

syntax.ml syntax.mli: syntax.mly base.cmo expr.cmo
	ocamlyacc -v syntax.mly

lex.ml: lex.mll syntax.cmi
	ocamllex lex.mll

TEST_EXPR=$(LEVEL2) test_expr.cmo
test_expr: $(TEST_EXPR)
	$(OCAMLC) $(OCAMLFLAGS) $(TEST_EXPR) -o test_expr

# ========== LEVEL 3

LEVEL3=$(LEVEL2) ipl_compile.cmo ipl_llvm.cmo

TEST_LLVM=$(LEVEL3) test_llvm.cmo
LLVM_FLAGS=-I /usr/local/lib/ocaml llvm.cma llvm_executionengine.cma llvm_analysis.cma llvm_scalar_opts.cma llvm_target.cma llvm_bitwriter.cma -cc g++
test_llvm: $(TEST_LLVM)
	$(OCAMLC) $(OCAMLFLAGS) $(LLVM_FLAGS) $(TEST_LLVM) -o test_llvm

IPLC_OBJS=$(LEVEL3) iplc.cmo
iplc: $(IPLC_OBJS)
	$(OCAMLC) $(OCAMLFLAGS) $(LLVM_FLAGS) $(IPLC_OBJS) -o iplc

# Flag -noassert could be added here, but last time I checked, it made little difference.
iplc.opt: $(IPLC_OBJS:.cmo=.cmx)
	$(OCAMLOPT) -cclib '-Xlinker -no_compact_unwind' $(OCAMLOPTFLAGS) $(LLVM_FLAGS:.cma=.cmxa) $(IPLC_OBJS:.cmo=.cmx) -o iplc.opt

ipltop: $(IPLC_OBJS)
	ocamlmktop -custom -ccopt -Wno-write-strings -g -cc g++ unix.cma $(LLVM_FLAGS) $(IPLC_OBJS) -o ipltop

# ========== SAMPLES

.ipl.bc:
	./iplc $< $@

.bc.s:
	llc $<

.s.o:
	gcc -c $<

# ========== DEPENDENCIES

.depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

include .depend
