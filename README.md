# Welcome to the HOARe² compiler distribution!

[![Build Status](https://travis-ci.com/ejgallego/HOARe2.svg?branch=master)](https://travis-ci.com/ejgallego/HOARe2)

We provide the type checker and examples used in papers:

* "Higher-Order Approximate Relational Refinement Types for Mechanism
   Design and Differential Privacy"
   - ACM: http://dl.acm.org/citation.cfm?id=2677000
   - ArXiV: http://arxiv.org/abs/1407.6845

* "Computer-aided verification in mechanism design"
   - ACM: https://dl.acm.org/citation.cfm?id=3081132
   - ArXiV: http://arxiv.org/abs/1502.04052

## Build instructions:

We recommend using OPAM 2.0 to install the tool, you'll need a recent
repository and standard gnu tools (gcc and make). Note the concrete
versions needed, in particular you need why3 1.2.1. In case of doubt,
the `.travis.yml` file should contain reproducible build
instructions. A typical workflow is:

```
$ opam install --deps-only -d -t .
$ why3 config --detect
$ dune build
$ dune exec -- arlc -L examples/popl/ examples/popl/dummysum.rlc
```

### Provers:

You want to install some SMT solvers to run the tool.
We recommend the following set:

```
$ why3 config --detect
Found prover Alt-Ergo version 2.3.0, OK.
Found prover CVC4 version 1.6, OK.
Found prover CVC4 version 1.4
Found prover CVC3 version 2.4.1, OK.
Found prover Eprover version 2.3, OK.
```

You may be lucky with other versions. Links:

- Alt-Ergo: (http://alt-ergo.ocamlpro.com/)
- CVC3 2.4.1 and CVC4 1.4 / 1.6:
  http://www.cs.nyu.edu/acsys/cvc3/
  http://cvc4.cs.nyu.edu/web/
- Eprover 2.0:
  http://wwwlehre.dhbw-stuttgart.de/~sschulz/E/E.html

### Running HOARe²:

To type-check a program just run:

```
$ dune exec -- arlc examples/ex01
```

`arlc --help` should display help for the tool.

## Editing and viewing examples:

The examples are in the examples/ directory.

We recommend using Emacs and Tuareg-mode to open the .rlc files. It is
not perfect but it does a good job, as our syntax is closely based on
OCaml's one.

You can add:

```
(add-to-list 'auto-mode-alist '("\\.rlc$"      . tuareg-mode) t)
```

to your emacs to automate the mode-loading process.

### Reproducing results:

The provided Travis setup does provide a reproducible checking of the
main examples, including `summarization`. Our CI setup will fail for
any commit that breaks this.

Note that the `binary` example produces .why files to be verified
using the Why3 IDE. We hope to improve this. Use

```
$ why3 ide -I examples/popl $file
```
to proceed.

In particular:

- `examples/binary_vc_length_power_0.why`:

  Requires the use of Eprover, it will then check.

- `examples/binary_vc_m_ass_0_solved.why`:

  This one is tricky and needs Eprover and CVC3 to check.

## More about the tool

If you are curious about the examples individually, we provide several
verbosity options to witness the type checking process `-v 1` to `-v 9`.

Depending on your machine the solvers may need a larger timeout. You
can control it using the --timeout parameter but the default should be
fine for most.

Some examples may take a long time, if they fail with a timeout,
try increasing it:

```
$ dune exec -- arlc --timeout 90 examples/summarization.rlc
```

The tool is in alpha stage, it may be difficult to use for your own
particular programs, but we would be happy to help.

The most common failure of the typechecking is solvers failing to
verify an assertion. If that happens, you can use:

```
$ why3 ide arlc_current.why
```

to play with the proof context and debug the cause of failure.

## Limitations of the tool

There are two important limitations of the tool, however  workarounds do exists:

- Bidirectional type-checking is very limited at the moment. This
  means that you may need to use a cut (see eq_v in dummysum.rlc for
  example) in the leaves to hint the type checker about the return
  type.

  Also `match` expressions do require annotations.

- Assertion checking may fail with an error if the assertion cannot be
  translated to Why3. Why3 has limited support for higher-order and we
  have not implemented a complete defunctionalization/demonadlization
  procedure yet.

  In most cases is possible to factorize the program to avoid
  this error.

## Language extensions

In order to help with development, two helper primitives "trust" and
"have" are supported.

```
have : { Assertion }        in
```

Will introduce a cut or intermediate lemma for helping the SMT. In
quite a few cases, the SMTs cannot prove A -> B directly, but with a
hint C, they are able to prove A -> C, and C -> B. (We usually
discover this conditions using why3ide).

The `have` primitive just eases the introduction of cuts.

```
trust (ass_name) res : T = e in
```

Will consider e to have type T without calling the SMTs. However, it
will output the pending proof to a file "ass_name.why", allowing to
prove it using the why3ide. We also output a Coq file for the
Coq-inclined user.

We hope you have fun, don't hesitate to contact us for any question or
help.

## Language reference:

TODO
