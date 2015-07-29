Require Import Utf8.
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.

Require Import bigop ssralg ssrnum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.
Import GRing.Theory Num.Theory.

(* In Section Theory we prove the consistency of the axioms and
   definitions given to alt-ergo.

   In Section PBug we prove that the inferred theorem is inconsistent.
*)

Section Theory.

  (************************************************************************)
  (* Distance over reals *)

  Variable (R : numDomainType).

  Definition d_r (x1 x2 : R) : R := `| x1 - x2|.

  Lemma d_r_eq  x : d_r x x = 0.
  Proof. by rewrite /d_r subrr normr0. Qed.

  Lemma d_r_pos  x1 x2 : 0 <= d_r x1 x2.
  Proof. by rewrite normr_ge0. Qed.

  (************************************************************************)
  (* Distance over list of reals *)

  Fixpoint lsum (l : seq R) :=
    match l with
      | [::] => 0
      | x :: xs => `|x| + lsum xs
    end.

  Lemma lsum_pos (l : seq R) : 0 <= lsum l.
  Proof.
    elim: l => //= x l ih.
    by rewrite addr_ge0 ?normr_ge0 ?ih.
  Qed.

  Fixpoint d_lr (l1 l2 : seq R) : R :=
    match l1, l2 with
      | [::], [::] => 0
      | (x :: xs), (y :: ys) => d_r x y + d_lr xs ys
      | [::], l | l, [::] => lsum l
    end.

  (* More lemmas *)
  Lemma d_lr_pos (l1 l2 : seq R) : 0 <= d_lr l1 l2.
  Proof.
    by elim: l1 l2 => [|x1 x ih] [|y1 y] //=;
    rewrite addr_ge0 ?normr_ge0 ?lsum_pos.
  Qed.

  Lemma eq_dist (l1 l2 : seq R) : l1 = l2 -> d_lr l1 l2 = 0.
  Proof.
    move=><- {l2}.
    elim: l1 => //= l ll ih.
    by rewrite d_r_eq add0r.
  Qed.


  Fixpoint adjacent (l1 l2 : seq R) := match l1, l2 with
    | [::], [::] => true
    | (x1 :: l1), (x2 :: l2) => [|| [&& l1 == l2 & d_r x1 x2 <= 1]
                                  | [&& x1 == x2 & adjacent l1 l2]
                                ]
    | _, _ => false
  end.

  Lemma adjacent_bound (l1 l2 : seq R) :
        adjacent l1 l2 -> d_lr l1 l2 <= 1.
  Proof.
    elim: l1 l2 => [|l1 ll1 ih] [|l2 ll2] //= /orP [] /andP [/eqP Hd Hl].
    + by rewrite eq_dist ?addr0.
    + by rewrite Hd d_r_eq add0r ih.
  Qed.

  Lemma mult_mon_right (e k : R) :
    0 <= e ->
    0 <= k ->
    k <= 1 ->
    e * k <= e.
  Proof. by move=> *; rewrite -{2}[e]mulr1 ler_pmul. Qed.

End Theory.

Section PBug.

  Variable (R : numDomainType).

  Lemma nbug (e x1 x2 : R) xs1 xs2 (He : 0 <= e) (Hadj : adjacent (x1::xs1) (x2::xs2)) :
    e * d_r x1 x2 <= 0.
  Proof. admit. (* by why3. *) Qed.

  Goal False.
  Proof.
    have Eadj: adjacent [:: 1] [:: 0].
      by move=> R'; rewrite /= /d_r subr0 normr1 lerr.
    move: (nbug ler01 (Eadj R)).
    by rewrite /d_r subr0 mul1r normr1 ler10.
  Qed.

End PBug.
