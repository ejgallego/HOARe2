.PHONY: arlc clean

all: arlc

arlc:
	dune build

clean::
	dune clean

# Completed examples
EXAMPLES=histogram two-level-a two-level-b dummysum noisysum binary idc dualquery fixedprice competitive competitive-b summarization
.PHONY: examples

# Not working:
# online two-level-c false composition

examples:
	for file in $(EXAMPLES); do \
	        echo "Testing $$file" ; \
		dune exec -- arlc -v 0 -L examples/popl --timeout 20 examples/popl/$$file.rlc || exit 1; \
	done
