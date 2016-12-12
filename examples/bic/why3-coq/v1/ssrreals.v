(* (c) Copyright Emilio Jesús Gallego Arias.                            *)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import bigop ssralg div ssrnum.
Import GRing.Theory Num.Theory.

(******************************************************************************)
(* ssreflect interfaces for Coq's Reals                                       *)
(*                                                                            *)
(* We follow ssrint.v / rat.v                                                 *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* STATUS: VERY EXPERIMENTAL                                                  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Reals.

Module realEq.
Section realEq.

Definition reals_eq (r1 r2 : R) : bool :=
  match total_order_T r1 r2 with
    | inleft  (left _)  => false
    | inleft  (right _) => true
    | inright _         => false
  end.

Lemma reals_eqP : Equality.axiom reals_eq.
Proof.
  move=> r1 r2.
  apply/(iffP idP); rewrite /reals_eq.
  - by case: total_order_T; try case.
  - by move => ->; case: total_order_T; try case; try move/Rlt_irrefl.
Qed.

Definition Mixin := EqMixin reals_eqP.
End realEq.
End realEq.

Canonical reals_eqType := Eval hnf in EqType R realEq.Mixin.

Module realChoice.
Section realChoice.

Require Import ChoiceFacts.
Require Import ClassicalFacts.
Require Import Classical_Prop.

Section FindP.
Variable (P : pred R).

(* Bad bad bad... This seems weak but could be very dangerous *)
Axiom R_dec : {r | P r = true} + (forall r, P r = false).
(* Axiom R_ext : forall (P Q : pred R), P =1 Q -> . *)

Definition find (n : nat) : option R.
  case: R_dec=> [[r _]|_].
  - by left.
  - by right.
Defined.

Lemma find_some n x : find n = Some x -> P x.
Proof.
  rewrite /find.
  by case: R_dec=> // -[r /= P'] []<-.
Qed.

Lemma find_exists : (exists x, P x) -> exists n, find n.
Proof.
  move=> [x HP].
  rewrite /find.
  case: R_dec=>//=.
  - case=> a Pa.
    by exists 0.
  - by move/(_ x); rewrite HP.
Qed.
End FindP.

Lemma find_ext : forall P Q : pred R, P =1 Q -> find P =1 find Q.
Proof.
  move=> P Q HPQ x.
  rewrite /find.
  do 2!case: R_dec=>//.
  - move=> [r Pr] [s Ps].
    (* This seems not provable without additional axioms *)
    admit.
  - move=> Pfr [s Ps]; move: (Pfr s).
    by rewrite -HPQ Ps.
  - move=> [r Pr] /(_ r).
    by rewrite HPQ Pr.
Qed.

Definition Mixin := Choice.Mixin find_some find_exists find_ext.

(* Old trick for choice *)
(* We postulate a bijection from Coq's reals to a rcf structure while
   we think of using a proper choice axiom for them *)
(*
Axiom (rR : rcfType).
Axiom rcf_of_real : forall (r : R), rR.
Axiom real_of_rcf : forall (r : rR), R.
Axiom rcf_realK : cancel rcf_of_real real_of_rcf.

Definition Mixin := CanChoiceMixin rcf_realK.
*)

End realChoice.
End realChoice.

Canonical real_choiceType := Eval hnf in ChoiceType R realChoice.Mixin.

Module realZmod.
Section realZmod.

Lemma addRA : associative Rplus.
Proof. by move=> x y z; rewrite Rplus_assoc. Qed.

Definition addRC : commutative Rplus := Rplus_comm.
Definition add0R : left_id 0%R Rplus := Rplus_0_l.

Lemma addNR : left_inverse 0%R Ropp Rplus.
Proof. by move=> x; rewrite addRC Rplus_opp_r. Qed.

Definition Mixin := ZmodMixin addRA addRC add0R addNR.

End realZmod.
End realZmod.

Canonical real_ZmodType := ZmodType R realZmod.Mixin.

Module realRing.
Section realRing.

Local Open Scope R_scope.

Definition mulRC : commutative Rmult := Rmult_comm.
Definition mul1R : left_id 1%R Rmult := Rmult_1_l.

Lemma mulRA : associative Rmult.
Proof. by move=> x y z; rewrite Rmult_assoc. Qed.

Lemma mulR_addl : left_distributive Rmult Rplus.
Proof. by move=> x y z; rewrite {1}mulRC Rmult_plus_distr_l [z*x]mulRC [z*y]mulRC. Qed.

Lemma nonzero1 : 1%R != 0.
Proof. exact/eqP/R1_neq_R0. Qed.

Definition comMixin := ComRingMixin mulRA mulRC mul1R mulR_addl nonzero1.
End realRing.
End realRing.

Canonical real_Ring    := Eval hnf in RingType R realRing.comMixin.
Canonical real_comRing := Eval hnf in ComRingType R realRing.mulRC.

Module realUnitRing.
Section realUnitRing.

Implicit Types m n : R.

Local Open Scope R_scope.
Definition unit := [qualify a n : R | n != 0].
Definition inv n : R := if n == 0 then 0 else / n.

Lemma mulRV : {in unit, left_inverse 1 inv Rmult}.
Proof.
  move=> n /eqP.
  rewrite Rmult_comm /inv.
  by case: eqP=>// _; apply/Rinv_r.
Qed.

Lemma unitPl m n : n * m = 1 -> m \is a unit.
Proof.
  rewrite qualifE.
  case: eqP => //->.
  rewrite Rmult_0_r => /esym.
  by move/R1_neq_R0.
Qed.

Lemma inv_out : {in [predC unit], inv =1 id}.
Proof.
  move=> x.
  rewrite inE /= qualifE /inv.
  by move/negbNE/eqP => ->; rewrite eqxx.
Qed.

Lemma idomain_axiom m n : m * n = 0 -> (m == 0) || (n == 0).
Proof.
  by case/(Rmult_integral m n)=> ->; rewrite eqxx ?orbT.
Qed.

Fact inv0 : inv 0 = 0.
Proof. by rewrite /inv eqxx. Qed.

Definition comMixin := ComUnitRingMixin mulRV unitPl inv_out.
Definition fieldUnitMixin := FieldUnitMixin mulRV inv0.

End realUnitRing.
End realUnitRing.

Canonical real_unitRing    := Eval hnf in UnitRingType R realUnitRing.comMixin.
Canonical real_comUnitRing := Eval hnf in [comUnitRingType of R].
Canonical real_iDomain     := Eval hnf in IdomainType R realUnitRing.idomain_axiom.

Fact real_field_axiom : GRing.Field.mixin_of real_unitRing. Proof. exact. Qed.
Canonical real_field       := Eval hnf in FieldType R real_field_axiom.

Module realClosedField.
Section realClosedField.

Lemma axiom : GRing.ClosedField.axiom [ringType of R].
  move=> x f H.
  admit.
Qed.

(* Now we can use the proof of quantifier elimination *)
Require Import closed_field.
Definition QEmixin := closed_fields_QEMixin axiom.

End realClosedField.
End realClosedField.

Canonical real_decField    := Eval hnf in DecFieldType R realClosedField.QEmixin.
Canonical real_closedField := Eval hnf in ClosedFieldType R realClosedField.axiom.

Module realOrdered.
Section realOrdered.

Local Open Scope R_scope.
Implicit Types m n x y z : R.

Require Import Psatz.
Definition norm (x : R) := Rabs x.

(* Boolean order for R *)
Definition ltR : R -> R -> bool := Rlt_dec.

Lemma ltRP x y : reflect (Rlt x y) (ltR x y).
Proof. by apply/(iffP idP); rewrite /ltR; case: Rlt_dec. Qed.

Definition leR : R -> R -> bool := Rle_dec.

Lemma leRP x y : reflect (Rle x y) (leR x y).
Proof. by apply/(iffP idP); rewrite /leR; case: Rle_dec. Qed.

(* Local Notation "x < y" := (ltR x y). *)
(* Local Notation "x <= y" := (leR x y). *)

Fact le_norm_add x y : leR (norm (x + y)) (norm x + norm y).
Proof. exact/leRP/Rabs_triang. Qed.

Fact lt_add x y : ltR 0 x -> ltR 0 y -> ltR 0 (x + y).
Proof.
  move => /ltRP Hx /ltRP Hy.
  exact/ltRP/Rplus_lt_0_compat.
Qed.

Fact eq0_norm x : norm x = 0 -> x = 0.
Proof.
  move/eqP; apply: contraTeq => /eqP H.
  exact/eqP/Rabs_no_R0.
Qed.

Fact le_total x y : leR x y || leR y x.
Proof.
  move: (Rle_dec x y) => [/leRP H1|].
  - by rewrite H1.
  - by move/Rnot_le_lt/Rlt_le/leRP=> ->; rewrite orbT.
Qed.

Fact normM : {morph (fun n => norm n) : x y / x * y}.
Proof. exact/Rabs_mult. Qed.

Lemma subz_ge0 m n : leR 0 (n - m) = leR m n.
Proof. by apply/leRP; case: ifP=> /leRP H; lra. Qed.

Fact le_def x y : (leR x y) = (norm (y - x) == y - x).
Proof.
  apply/esym.
  case: leRP=> [H | /Rnot_le_lt H]; apply/eqP; rewrite /norm.
  - have Hxy: y - x >= 0; first by lra.
    by rewrite Rabs_right.
  - have Hxy: y - x <  0; first by lra.
    have Hme: x - y >= 0; first by lra.
    rewrite Rabs_left ?Ropp_minus_distr // => Heq.
    rewrite Heq in Hme.
    exact: (Rlt_not_ge _ _ Hxy).
Qed.

Fact lt_def x y : (ltR x y) = (y != x) && (leR x y).
Proof.
  apply/ltRP; case: ifP.
  - move=> /andP [/eqP H1].
    by case/leRP=>// /esym.
  - move/nandP=> [/negbNE/eqP-> | /leRP H].
    + exact/Rlt_irrefl.
    + by move/Rlt_le.
Qed.

Definition Mixin :=
   NumMixin le_norm_add lt_add eq0_norm (in2W le_total) normM
            le_def lt_def.

End realOrdered.
End realOrdered.


Canonical real_numDomainType  := NumDomainType  R realOrdered.Mixin.
Canonical real_realDomainType := RealDomainType R (realOrdered.le_total 0).

Canonical real_numFieldType       := [numFieldType  of R].
Canonical real_realFieldType      := [realFieldType of R].
Canonical real_numClosedFieldType := [numClosedFieldType of R].

Lemma addRE (x y : R) : GRing.add x y = Rplus x y.
Proof. by []. Qed.

Lemma oppRE (x : R) : GRing.opp x = Ropp x.
Proof. by []. Qed.

Lemma subRE (x y : R) : GRing.add x (GRing.opp y) = Rminus x y.
Proof. by []. Qed.

Lemma leRE (x y : R) : Num.Def.ler x y = realOrdered.leR x y.
Proof. by []. Qed.

Lemma ltRE (x y : R) : Num.Def.ltr x y = realOrdered.ltR x y.
Proof. by []. Qed.

Print Assumptions real_realFieldType.

Module realArchi.
Section realArchi.

Local Open Scope ring_scope.
Lemma absRE (r : R) : `|r|%R = Rabs r :> R. Proof. by []. Qed.

Lemma real_archimedean : Num.archimedean_axiom [numDomainType of R].
Proof.
  move=> x.
  exists (Z.abs_nat (up x)).
  apply/realOrdered.ltRP.
  rewrite absRE.
  move: (archimed x)=> [/Rgt_lt H1 H2].
  (* EG: TODO *)
  admit.
Qed.

Canonical real_archi := ArchiFieldType R real_archimedean.

End realArchi.
End realArchi.

(* Canonical real_numClosed := Eval hnf in [rcfType of R]. *)

Section Test.
Open Scope ring_scope.

Goal forall (x y : R), 0 <= y -> x <= x + y.
Proof. by move=> x y; rewrite ler_addl. Qed.

End Test.
