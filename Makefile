# Program main file
ARLC=src/arlc

# Ocamlbuild
OCBOPTS=-use-ocamlfind
# OCBOPTS=-use-ocamlfind -lib unix -pkgs menhirLib -use-menhir
OCAMLBUILD=ocamlbuild $(OCBOPTS)

.PHONY: arlc clean arlc.byte arlc.native arlc.d.byte arlc.d.native arlc.p.byte arlc.p.native

VERSION=native

all: arlc

arlc: arlc.$(VERSION)
	cp arlc.$(VERSION) arlc

arlc.byte:
	$(OCAMLBUILD) $(ARLC).byte

arlc.native:
	$(OCAMLBUILD) $(ARLC).native

arlc.p.byte:
	$(OCAMLBUILD) $(ARLC).p.byte

arlc.d.byte:
	$(OCAMLBUILD) $(ARLC).d.byte

arlc.p.native:
	$(OCAMLBUILD) $(ARLC).p.native

clean::
	$(OCAMLBUILD) -clean
	rm -f src/parser.conflicts
	rm -rf arlc arlc.* TAGS

# Completed examples
EXAMPLES=histogram two-level-a two-level-b two-level-c dummysum noisysum binary idc dualquery online fixedprice competitive competitive-b summarization

.PHONY: examples
examples:
	for file in $(EXAMPLES); do \
	        echo "Testing $$file" ; \
		./arlc --soft-assertions -v 1 -L examples/popl --timeout 20 examples/popl/$$file.rlc ; \
	done
