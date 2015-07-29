# Welcome to the HOARe² compiler distribution!

This compiler implements the type system described in the paper:

"Higher-Order Approximate Relational Refinement Types for Mechanism
 Design and Differential Privacy"
 (http://dl.acm.org/citation.cfm?id=2677000)

as well as some extensions used in current work.

## Build instructions:

### Required tools:

You will need an ocaml toolchain (>= 4.02.3) with ocamlfind,
ocamlbuild, and standard gnu tools (gcc and make).

Installation of those tools can be done through standard channels,
using OPAM will considerably ease the task.

### Installing Why3:

The tool builds against Why3 0.86.1 from (http://why3.lri.fr/).
See the why3 readme for why3 dependencies. The basic build process
should go like:

```
$ ./configure
$ make
$ make install
$ make byte opt
$ make install-lib
```

### Provers:

Prover support is always a changuing issue, the tool has been tested with the following SMT solvers:

```
$ why3 config --detect
Found prover Alt-Ergo version 1.00.prv, Ok.
Found prover CVC4 version 1.4, Ok.
Found prover CVC3 version 2.4.1, Ok.
Found prover Eprover version 1.8-001, Ok.
Found prover Coq version 8.4pl4, Ok.
```

You may be lucky with other versions.

- Alt-Ergo: (http://alt-ergo.ocamlpro.com/)
- CVC3 2.4.1 and CVC4 1.4:
  http://www.cs.nyu.edu/acsys/cvc3/
  http://cvc4.cs.nyu.edu/web/
- Eprover 1.8:
  http://wwwlehre.dhbw-stuttgart.de/~sschulz/E/E.html

### Building HOARe²:

A simple `make` will compile the tool.

To type a program run:

```
$ ./arlc examples/ex01
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

For practical reasons, a couple of examples produce a .why file to be
verified using the Why3ide.

Use

$ why3ide -I examples $file

to proceed.

In particular:

- examples/binary_vc_length_power_0.why:

  Requires the use of Eprover, it will then check.

- examples/binary_vc_m_ass_0_solved.why

  This one is tricky and needs Eprover and CVC3 to check.

- examples/summarization_vc_pSig_cut_0.why:

  CVC4 can solve the file as is with a large enough timeout (90s),
  using the split tactic in the IDE allows the goal to be solved
  immediately.

## More about the tool

If you are curious about the examples individually, we provide several
verbosity options to witness the type checking process `-v 1` to `-v 9`.

Depending on your machine the solvers may need a larger timeout. You
can control it using the --timeout parameter but the default should be
fine for most.

Some examples may take a long time, if they fail with a timeout,
try increasing it:

```
$ ./arlc --timeout 90 examples/summarization.rlc
```

The tool is in alpha stage, it may be difficult to use for your own
particular programs, but we would be happy to help.

The most common failure of the typechecking is solvers failing to
verify an assertion. If that happens, you can use:

```
$ why3ide arlc_current.why
```

to play with the proof context and debug the cause of failure.

## Limitations of the tool

There are two important limitations of the tool, however  workarounds do exists:

- Bidirectional type-checking is very limited at the moment. This
  means that you may need to use a cut (see eq_v in dummysum.rlc for
  example) in the leaves to hint the type checker about the return
  type.

  Also "match" require annotations.

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

