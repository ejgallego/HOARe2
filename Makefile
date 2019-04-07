.PHONY: arlc clean

all: arlc

arlc:
	dune build

clean::
	dune clean

# Completed examples
EXAMPLES=histogram two-level-a two-level-b two-level-c dummysum noisysum binary idc dualquery online fixedprice competitive competitive-b summarization

.PHONY: examples
examples:
	for file in $(EXAMPLES); do \
	        echo "Testing $$file" ; \
		dune exec -- arlc --soft-assertions -v 1 -L examples/popl --timeout 20 examples/popl/$$file.rlc ; \
	done
