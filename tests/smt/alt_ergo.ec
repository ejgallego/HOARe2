require import List.
require import Real.

(************************************************************************)
(* Distance over reals *)

op d_r (x1 x2 : real) : real = `|x1 - x2|.

lemma d_r_pos : forall (x1 x2 : real) , 0%r <= d_r x1 x2.
proof. by smt. qed.

lemma d_rr : forall (r : real) , d_r r r = 0%r.
proof. by smt. qed.

(************************************************************************)
(* Distance over list of reals *)

op d_lr (l1 l2 : real list) : real =
  with l1 = "[]", l2 = "[]"           => 0%r
  with l1 = (::) x xs, l2 = (::) y ys => d_r x y + d_lr xs ys
  with l1 = "[]",      l2 = (::) y ys => 0%r
  with l1 = (::) x xs, l2 = "[]"      => 0%r.

lemma d_lr_pos : forall (l1 l2 : real list),
        0%r <= d_lr l1 l2.
proof.
elim=> [| l1 ll1 ih] [|l2 ll2] //.
by smt.
qed.

lemma eq_dist : forall (l1 l2 : real list),
    l1 = l2 => d_lr l1 l2 = 0%r .
proof.
  move=> l1 l2 <- {l2}.
  elim l1 => // l1 ll1 /= <-.
  by smt.
qed.

op adjacent (l1 l2 : real list ) =
  with l1 = "[]", l2 = "[]"           => true
  with l1 = (::) x xs, l2 = (::) y ys => (d_r x y <= 1%r && xs = ys) || (x = y && adjacent xs ys)
  with l1 = "[]",      l2 = (::) y ys => false
  with l1 = (::) x xs, l2 = "[]"      => false.

lemma adjacent_bound : forall (l1 l2 : real list),
        adjacent l1 l2 => d_lr l1 l2 <= 1%r .
proof. by elim=> [|x xs ih] [|y ys] //=; smt. qed.
(*   apply oraE. *)
(*   + case=> Hx ->. *)
(*     by rewrite eq_dist //. *)
(*   + move=> Hn [-> Ha]. *)
(*     by rewrite d_rr /= ih. *)
(* qed. *)

lemma mult_mon_right : forall (e k : real),
        0%r <= e   =>
        0%r <= k   =>
        k   <= 1%r =>
        e * k <= e.
proof.
  move=> e k He H0k Hk1.
  by smt.
qed.

lemma bugpy (x y : real) :
0%r <= x => 1%r <= y => x / y = x * 1%r / y => 0%r < x.
proof.
  move=> h1 h2 h3.
  smt.
qed.

lemma bug : forall (e x1 x2 : real)
                   (xs1 xs2 : real list),
                   0%r <= e =>
                   adjacent ((::) x1 xs1) ((::) x2 xs2) =>
                   (e * d_r x1 x2) <= 0%r.
proof.
  move => e x1 x2 xs1 xs2 H0e Hadj.
  by smt.
qed.
(*   move: d_r_pos  => H1.       *)
(*   move: d_lr_pos => H2.       *)
(*   move: eq_dist  => H3.       *)
(*   move: adjacent_bound => H4. *)
(*   move: mult_mon_right => H5. *)
(*   pragma verbose.             *)
(*   by smt.                     *)
(* qed.                          *)


