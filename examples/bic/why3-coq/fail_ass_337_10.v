(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require Reals.Rbasic_fun.
Require BuiltIn.
Require int.Int.
Require real.Real.
Require real.RealInfix.
Require real.Abs.
Require real.FromInt.
Require bool.Bool.
Require list.List.
Require list.Length.
Require list.Mem.
Require list.NthNoOpt.
Require list.HdTlNoOpt.
Require list.Append.
Require list.Reverse.
Require list.NumOcc.
Require list.Permut.

Axiom func : forall (a:Type) (b:Type), Type.
Parameter func_WhyType : forall (a:Type) {a_WT:WhyType a}
  (b:Type) {b_WT:WhyType b}, WhyType (func a b).
Existing Instance func_WhyType.

(* Why3 assumption *)
Definition pred (a:Type) := (func a bool).

Parameter infix_at: forall {a:Type} {a_WT:WhyType a}
  {b:Type} {b_WT:WhyType b}, (func a b) -> a -> b.

Axiom distr : forall (a:Type), Type.
Parameter distr_WhyType : forall (a:Type) {a_WT:WhyType a},
  WhyType (distr a).
Existing Instance distr_WhyType.

Parameter munit: forall {a:Type} {a_WT:WhyType a}, a -> (distr a).

Parameter mbind: forall {a:Type} {a_WT:WhyType a} {b:Type} {b_WT:WhyType b},
  (distr a) -> (func a (distr b)) -> (distr b).

(* Why3 assumption *)
Definition bool_skeleton (b1:bool) (b2:bool): Prop := match (b1,
  b2) with
  | (true, true) => True
  | (false, false) => True
  | _ => False
  end.

Axiom b_eq_sk : forall (b1:bool) (b2:bool), (b1 = b2) -> (bool_skeleton b1
  b2).

(* Why3 assumption *)
Definition fst {a:Type} {a_WT:WhyType a} {b:Type} {b_WT:WhyType b} (x:(a*
  b)%type): a := match x with
  | (r, _) => r
  end.

(* Why3 assumption *)
Definition snd {a:Type} {a_WT:WhyType a} {b:Type} {b_WT:WhyType b} (x:(a*
  b)%type): b := match x with
  | (_, r) => r
  end.

(* Why3 assumption *)
Definition fst3 {a:Type} {a_WT:WhyType a} {b:Type} {b_WT:WhyType b}
  {c:Type} {c_WT:WhyType c} (x:(a* b* c)%type): a :=
  match x with
  | (r, _, _) => r
  end.

(* Why3 assumption *)
Definition snd3 {a:Type} {a_WT:WhyType a} {b:Type} {b_WT:WhyType b}
  {c:Type} {c_WT:WhyType c} (x:(a* b* c)%type): b :=
  match x with
  | (_, r, _) => r
  end.

(* Why3 assumption *)
Definition thd3 {a:Type} {a_WT:WhyType a} {b:Type} {b_WT:WhyType b}
  {c:Type} {c_WT:WhyType c} (x:(a* b* c)%type): c :=
  match x with
  | (_, _, r) => r
  end.

(* Why3 assumption *)
Definition fth {a:Type} {a_WT:WhyType a} {b:Type} {b_WT:WhyType b}
  {c:Type} {c_WT:WhyType c} {d:Type} {d_WT:WhyType d} (x:(a* b* c*
  d)%type): d := match x with
  | (_, _, _, r) => r
  end.

(* Why3 assumption *)
Inductive nat :=
  | Zero : nat
  | Succ : nat -> nat.
Axiom nat_WhyType : WhyType nat.
Existing Instance nat_WhyType.

Parameter nat_skeleton: nat -> nat -> Prop.

Axiom nat_skeleton_def : forall (n1:nat) (n2:nat), match (n1,
  n2) with
  | (Zero, Zero) => (nat_skeleton n1 n2)
  | ((Succ x1), (Succ x2)) => (nat_skeleton n1 n2) <-> (nat_skeleton x1 x2)
  | _ => ~ (nat_skeleton n1 n2)
  end.

Axiom nat_sk : forall (n1:nat) (n2:nat), (n1 = n2) -> (nat_skeleton n1 n2).

(* Why3 assumption *)
Fixpoint nat_plus (x:nat) (y:nat) {struct x}: nat :=
  match x with
  | Zero => y
  | (Succ x') => (Succ (nat_plus x' y))
  end.

(* Why3 assumption *)
Fixpoint nat_to_int (x:nat) {struct x}: Z :=
  match x with
  | Zero => 0%Z
  | (Succ x') => (1%Z + (nat_to_int x'))%Z
  end.

(* Why3 assumption *)
Definition nat_to_real (x:nat): R := (Reals.Raxioms.IZR (nat_to_int x)).

Parameter int_to_nat: Z -> nat.

Axiom conv_int_nat_int : forall (x:Z), (0%Z <= x)%Z ->
  ((nat_to_int (int_to_nat x)) = x).

Axiom conv_nat_int_nat : forall (x:nat), ((int_to_nat (nat_to_int x)) = x).

Axiom nat_int_pos : forall (n:nat), (0%Z <= (nat_to_int n))%Z.

Axiom nat_int_plus : forall (n1:nat) (n2:nat),
  (((nat_to_int n1) + (nat_to_int n2))%Z = (nat_to_int (nat_plus n1 n2))).

Axiom nat_real_pos : forall (n:nat), (0%R <= (nat_to_real n))%R.

Axiom nat_real_plus : forall (n1:nat) (n2:nat),
  (((nat_to_real n1) + (nat_to_real n2))%R = (nat_to_real (nat_plus n1 n2))).

Axiom conv_nat_int_real : forall (x:nat),
  ((Reals.Raxioms.IZR (nat_to_int x)) = (nat_to_real x)).

(* Why3 assumption *)
Definition d_r (x1:R) (x2:R): R := (Reals.Rbasic_fun.Rabs (x1 - x2)%R).

Axiom d_r_pos : forall (x1:R) (x2:R), (0%R <= (d_r x1 x2))%R.

Parameter d_b: bool -> bool -> R.

Axiom d_b_def : forall (x1:bool) (x2:bool), ((x1 = x2) -> ((d_b x1
  x2) = 0%R)) /\ ((~ (x1 = x2)) -> ((d_b x1 x2) = 1%R)).

Parameter d_lr: (list R) -> (list R) -> R.

Axiom d_lr_def : forall (l1:(list R)) (l2:(list R)), match (l1,
  l2) with
  | (Init.Datatypes.nil, Init.Datatypes.nil) => ((d_lr l1 l2) = 0%R)
  | ((Init.Datatypes.cons x xs), (Init.Datatypes.cons y ys)) => ((d_lr l1
      l2) = ((d_r x y) + (d_lr xs ys))%R)
  | _ => ((d_lr l1 l2) = 0%R)
  end.

Axiom d_lr_pos : forall (l1:(list R)) (l2:(list R)), (0%R <= (d_lr l1 l2))%R.

Axiom d_lr_cons : forall (x1:R) (x2:R) (l1:(list R)) (l2:(list R)), ((d_lr l1
  l1) <= (d_lr (Init.Datatypes.cons x1 l1) (Init.Datatypes.cons x2 l2)))%R.

Axiom eq_dist : forall (l1:(list R)) (l2:(list R)), (l1 = l2) -> ((d_lr l1
  l2) = 0%R).

Axiom d_lr_head_tail : forall (x1:R) (x2:R) (xs1:(list R)) (xs2:(list R)),
  (((d_r x1 x2) + (d_lr xs1 xs2))%R = (d_lr (Init.Datatypes.cons x1 xs1)
  (Init.Datatypes.cons x2 xs2))).

Axiom d_lr_head_tail' : forall (x1:R) (x2:R) (xs1:(list R)) (xs2:(list R))
  (l1:(list R)) (l2:(list R)), (l1 = (Init.Datatypes.cons x1 xs1)) ->
  ((l2 = (Init.Datatypes.cons x2 xs2)) -> (((d_r x1 x2) + (d_lr xs1
  xs2))%R = (d_lr l1 l2))).

Parameter d_lb: (list bool) -> (list bool) -> R.

Axiom d_lb_def : forall (l1:(list bool)) (l2:(list bool)), match (l1,
  l2) with
  | (Init.Datatypes.nil, Init.Datatypes.nil) => ((d_lb l1 l2) = 0%R)
  | ((Init.Datatypes.cons x xs), (Init.Datatypes.cons y ys)) => ((d_lb l1
      l2) = ((d_b x y) + (d_lb xs ys))%R)
  | _ => ((d_lb l1 l2) = 0%R)
  end.

Axiom d_lb_pos : forall (l1:(list bool)) (l2:(list bool)), (0%R <= (d_lb l1
  l2))%R.

Axiom d_lb_cons : forall (x1:bool) (x2:bool) (l1:(list bool))
  (l2:(list bool)), ((d_lb l1 l1) <= (d_lb (Init.Datatypes.cons x1 l1)
  (Init.Datatypes.cons x2 l2)))%R.

Axiom eq_dist_b : forall (l1:(list bool)) (l2:(list bool)), (l1 = l2) ->
  ((d_lb l1 l2) = 0%R).

Axiom d_lb_head_tail : forall (x1:bool) (x2:bool) (xs1:(list bool))
  (xs2:(list bool)), (((d_b x1 x2) + (d_lb xs1
  xs2))%R = (d_lb (Init.Datatypes.cons x1 xs1)
  (Init.Datatypes.cons x2 xs2))).

Axiom d_lb_head_tail' : forall (x1:bool) (x2:bool) (xs1:(list bool))
  (xs2:(list bool)) (l1:(list bool)) (l2:(list bool)),
  (l1 = (Init.Datatypes.cons x1 xs1)) ->
  ((l2 = (Init.Datatypes.cons x2 xs2)) -> (((d_b x1 x2) + (d_lb xs1
  xs2))%R = (d_lb l1 l2))).

Parameter adjacent: (list R) -> (list R) -> Prop.

Axiom adjacent_def : forall (l1:(list R)) (l2:(list R)), match (l1,
  l2) with
  | (Init.Datatypes.nil, Init.Datatypes.nil) => (adjacent l1 l2)
  | ((Init.Datatypes.cons x1 l11), (Init.Datatypes.cons x2 l21)) => (adjacent
      l1 l2) <-> ((((Reals.Rbasic_fun.Rabs (x1 - x2)%R) <= 1%R)%R /\
      (l11 = l21)) \/ ((x1 = x2) /\ (adjacent l11 l21)))
  | _ => ~ (adjacent l1 l2)
  end.

Axiom eq_adjacent : forall (l1:(list R)) (l2:(list R)), (l1 = l2) ->
  (adjacent l1 l2).

Axiom adjacent_impl : forall (x1:R) (x2:R) (l1:(list R)) (l2:(list R)),
  (adjacent (Init.Datatypes.cons x1 l1) (Init.Datatypes.cons x2 l2)) ->
  (adjacent l1 l2).

Axiom adjacent_bound_head : forall (x1:R) (x2:R) (l1:(list R)) (l2:(list R)),
  (adjacent (Init.Datatypes.cons x1 l1) (Init.Datatypes.cons x2 l2)) ->
  ((d_r x1 x2) <= 1%R)%R.

Axiom adjacent_bound_tail : forall (x1:R) (x2:R) (l1:(list R)) (l2:(list R)),
  (adjacent (Init.Datatypes.cons x1 l1) (Init.Datatypes.cons x2 l2)) ->
  ((d_lr l1 l2) <= 1%R)%R.

Axiom adjacent_bound : forall (l1:(list R)) (l2:(list R)), (adjacent l1
  l2) -> ((d_lr l1 l2) <= 1%R)%R.

Axiom adjacent_cons_bound : forall (x1:R) (x2:R) (y1:R) (y2:R) (xs1:(list R))
  (xs2:(list R)) (l1:(list R)) (l2:(list R)), (adjacent l1 l2) ->
  ((l1 = (Init.Datatypes.cons x1 xs1)) ->
  ((l2 = (Init.Datatypes.cons x2 xs2)) -> (((d_r y1 y2) <= (d_lr xs1
  xs2))%R -> ((d_r (x1 + y1)%R (x2 + y2)%R) <= (d_lr l1 l2))%R))).

Parameter adjacent_b: (list bool) -> (list bool) -> Prop.

Axiom adjacent_b_def : forall (l1:(list bool)) (l2:(list bool)), match (l1,
  l2) with
  | (Init.Datatypes.nil, Init.Datatypes.nil) => (adjacent_b l1 l2)
  | ((Init.Datatypes.cons x1 l11), (Init.Datatypes.cons x2 l21)) =>
      (adjacent_b l1 l2) <-> (((~ (x1 = x2)) /\ (l11 = l21)) \/ ((x1 = x2) /\
      (adjacent_b l11 l21)))
  | _ => ~ (adjacent_b l1 l2)
  end.

Axiom eq_adjacent_b : forall (l1:(list bool)) (l2:(list bool)), (l1 = l2) ->
  (adjacent_b l1 l2).

Axiom adjacent_b_impl : forall (x1:bool) (x2:bool) (l1:(list bool))
  (l2:(list bool)), (adjacent_b (Init.Datatypes.cons x1 l1)
  (Init.Datatypes.cons x2 l2)) -> (adjacent_b l1 l2).

Axiom adjacent_b_bound_head : forall (x1:bool) (x2:bool) (l1:(list bool))
  (l2:(list bool)), (adjacent_b (Init.Datatypes.cons x1 l1)
  (Init.Datatypes.cons x2 l2)) -> ((d_b x1 x2) <= 1%R)%R.

Axiom adjacent_b_bound_tail : forall (x1:bool) (x2:bool) (l1:(list bool))
  (l2:(list bool)), (adjacent_b (Init.Datatypes.cons x1 l1)
  (Init.Datatypes.cons x2 l2)) -> ((d_lb l1 l2) <= 1%R)%R.

Axiom adjacent_b_bound : forall (l1:(list bool)) (l2:(list bool)),
  (adjacent_b l1 l2) -> ((d_lb l1 l2) <= 1%R)%R.

Parameter list_skeleton: forall {a:Type} {a_WT:WhyType a}, (list a) ->
  (list a) -> Prop.

Axiom list_skeleton_def : forall {a:Type} {a_WT:WhyType a},
  forall (l1:(list a)) (l2:(list a)), match (l1,
  l2) with
  | (Init.Datatypes.nil, Init.Datatypes.nil) => (list_skeleton l1 l2)
  | ((Init.Datatypes.cons _ l11), (Init.Datatypes.cons _ l21)) =>
      (list_skeleton l1 l2) <-> (list_skeleton l11 l21)
  | _ => ~ (list_skeleton l1 l2)
  end.

Axiom adj_sk : forall (l1:(list R)) (l2:(list R)), (adjacent l1 l2) ->
  (list_skeleton l1 l2).

Axiom adj_b_sk : forall (l1:(list bool)) (l2:(list bool)), (adjacent_b l1
  l2) -> (list_skeleton l1 l2).

Axiom eq_sk : forall {a:Type} {a_WT:WhyType a}, forall (l1:(list a))
  (l2:(list a)), (l1 = l2) -> (list_skeleton l1 l2).

Axiom w_ext : forall {a:Type} {a_WT:WhyType a} {b:Type} {b_WT:WhyType b},
  forall (f:(func a b)) (g:(func a b)), (forall (x:a), ((infix_at f
  x) = (infix_at g x))) -> (f = g).

Axiom ty : Type.
Parameter ty_WhyType : WhyType ty.
Existing Instance ty_WhyType.

Axiom oc : Type.
Parameter oc_WhyType : WhyType oc.
Existing Instance oc_WhyType.

Parameter differAt: forall {a:Type} {a_WT:WhyType a}, nat -> (list a) ->
  (list a) -> Prop.

Axiom differAt_def : forall {a:Type} {a_WT:WhyType a}, forall (i:nat)
  (l1:(list a)) (l2:(list a)),
  match i with
  | Zero => match (l1,
      l2) with
      | ((Init.Datatypes.cons _ l11), (Init.Datatypes.cons _ l21)) =>
          (differAt i l1 l2) <-> (l11 = l21)
      | _ => ~ (differAt i l1 l2)
      end
  | (Succ i') => match (l1,
      l2) with
      | ((Init.Datatypes.cons x1 l11), (Init.Datatypes.cons x2 l21)) =>
          (differAt i l1 l2) <-> ((x1 = x2) /\ (differAt i' l11 l21))
      | _ => ~ (differAt i l1 l2)
      end
  end.

(* Why3 assumption *)
Fixpoint allPerms {a:Type} {a_WT:WhyType a} (l:(list a))
  (l':(list (list a))) {struct l'}: Prop :=
  match l' with
  | Init.Datatypes.nil => True
  | (Init.Datatypes.cons x l'1) => (list.Permut.permut l x) /\ (allPerms l
      l'1)
  end.

Axiom memAllPerms : forall {a:Type} {a_WT:WhyType a}, forall (s:(list a))
  (x:(list a)) (r:(list (list a))), (allPerms s r) -> ((list.Mem.mem x r) ->
  (list.Permut.permut s x)).

(* Why3 assumption *)
Fixpoint sumFuns {a:Type} {a_WT:WhyType a} (funs:(list (func a R)))
  (alloc:a) {struct funs}: R :=
  match funs with
  | Init.Datatypes.nil => 0%R
  | (Init.Datatypes.cons f fs) => ((infix_at f alloc) + (sumFuns fs alloc))%R
  end.

Parameter sumFuns1: forall {a:Type} {a_WT:WhyType a}, (list (func a R)) ->
  (func a R).

Axiom sumFuns1_def : forall {a:Type} {a_WT:WhyType a},
  forall (funs:(list (func a R))) (alloc:a), ((infix_at (sumFuns1 funs)
  alloc) = (sumFuns funs alloc)).

(* Why3 assumption *)
Fixpoint allBut {a:Type} {a_WT:WhyType a} (i:nat)
  (l:(list a)) {struct i}: (list a) :=
  match i with
  | Zero => (list.HdTlNoOpt.tl l)
  | (Succ i') => (allBut i' (list.HdTlNoOpt.tl l))
  end.

Axiom allButDiff : forall {a:Type} {a_WT:WhyType a}, forall (i:nat)
  (l1:(list a)) (l2:(list a)), (differAt i l1 l2) -> ((allBut i
  l1) = (allBut i l2)).

Axiom sumAllBut : forall {a:Type} {a_WT:WhyType a}, forall (i:nat) (alloc:a)
  (fs:(list (func a R))), ((nat_to_int i) < (list.Length.length fs))%Z ->
  (((sumFuns (allBut i fs)
  alloc) + (infix_at (list.NthNoOpt.nth (nat_to_int i) fs)
  alloc))%R = (sumFuns fs alloc)).

(* Why3 assumption *)
Fixpoint insertAt {a:Type} {a_WT:WhyType a} (i:nat) (x:a)
  (l:(list a)) {struct i}: (list a) :=
  match i with
  | Zero => (Init.Datatypes.cons x l)
  | (Succ i') => (Init.Datatypes.cons (list.HdTlNoOpt.hd l) (insertAt i' x
      (list.HdTlNoOpt.tl l)))
  end.

Axiom insertAtZero : forall {a:Type} {a_WT:WhyType a}, forall (x:a)
  (l:(list a)), ((insertAt Zero x l) = (Init.Datatypes.cons x l)).

Axiom nthInsertAt : forall {a:Type} {a_WT:WhyType a}, forall (x:a)
  (l:(list a)) (i:nat), ((nat_to_int i) <= (list.Length.length l))%Z ->
  ((list.NthNoOpt.nth (nat_to_int i) (insertAt i x l)) = x).

Axiom insertAtDifferAt : forall {a:Type} {a_WT:WhyType a}, forall (i:nat)
  (x1:a) (x2:a) (l1:(list a)) (l2:(list a)),
  ((nat_to_int i) <= (list.Length.length l1))%Z -> ((l1 = l2) -> (differAt i
  (insertAt i x1 l1) (insertAt i x2 l2))).

Axiom insertAtLength : forall {a:Type} {a_WT:WhyType a}, forall (i:nat) (x:a)
  (l:(list a)), ((nat_to_int i) <= (list.Length.length l))%Z ->
  ((list.Length.length (insertAt i x l)) = ((list.Length.length l) + 1%Z)%Z).

(* Why3 assumption *)
Fixpoint repeat {a:Type} {a_WT:WhyType a} (n:nat)
  (x:a) {struct n}: (list a) :=
  match n with
  | Zero => Init.Datatypes.nil
  | (Succ n') => (Init.Datatypes.cons x (repeat n' x))
  end.

Parameter fc: forall {a:Type} {a_WT:WhyType a}, a -> (func (list a) (distr
  (list a))).

Parameter fc1: forall {a:Type} {a_WT:WhyType a}, (list (distr a)) -> (func a
  (distr (list a))).

Axiom fc_def : forall {a:Type} {a_WT:WhyType a}, forall (p:a) (ps:(list a)),
  ((infix_at (fc p) ps) = (munit (Init.Datatypes.cons p ps))).

(* Why3 assumption *)
Definition seqM {a:Type} {a_WT:WhyType a} (l:(list (distr a))): (distr
  (list a)) :=
  match l with
  | Init.Datatypes.nil => (munit Init.Datatypes.nil)
  | (Init.Datatypes.cons x xs) => (mbind x (fc1 xs))
  end.

Axiom fc_def1 : forall {a:Type} {a_WT:WhyType a}, forall (xs:(list (distr
  a))) (p:a), ((infix_at (fc1 xs) p) = (mbind (seqM xs) (fc p))).

Parameter fc2: forall {a:Type} {a_WT:WhyType a}, (func a (distr a)) -> (func
  a (distr a)).

Parameter sampleAndApply: forall {a:Type} {a_WT:WhyType a}, (distr a) ->
  (func (func a (distr a)) (distr a)).

Axiom fc_def2 : forall {a:Type} {a_WT:WhyType a}, forall (f:(func a (distr
  a))) (t:a), ((infix_at (fc2 f) t) = (infix_at f t)).

Axiom sampleAndApply_def : forall {a:Type} {a_WT:WhyType a},
  forall (mu:(distr a)) (f:(func a (distr a))),
  ((infix_at (sampleAndApply mu) f) = (mbind mu (fc2 f))).

Parameter mapHO: forall {a:Type} {a_WT:WhyType a} {b:Type} {b_WT:WhyType b},
  (func a b) -> (list a) -> (list b).

(* Why3 assumption *)
Fixpoint allPres {a:Type} {a_WT:WhyType a} (mu:(distr a)) (l:(list (func a
  (distr a)))) {struct l}: Prop :=
  match l with
  | Init.Datatypes.nil => True
  | (Init.Datatypes.cons x xs) => (allPres mu xs)
  end.

Axiom allPresUnpack : forall (n:nat) (mu:(distr ty)) (l:(list (func ty (distr
  ty)))), ((list.Length.length l) = (nat_to_int n)) -> ((allPres mu l) ->
  ((repeat n mu) = (mapHO (sampleAndApply mu) l))).

Parameter enumPerms: (list ty) -> (list (list ty)).

Axiom enumPermsLength : forall (g:(list ty)),
  (0%Z < (list.Length.length (enumPerms g)))%Z.

Axiom enumPermsPerm : forall (g:(list ty)) (p:(list ty)), (list.Mem.mem p
  (enumPerms g)) -> (list.Permut.permut g p).

Axiom enumPermsAll : forall (g:(list ty)), (allPerms g (enumPerms g)).

Parameter findMax: (func (list ty) R) -> (list (list ty)) -> (list ty).

Axiom findMaxMem : forall (obj:(func (list ty) R)) (r:(list (list ty))),
  (0%Z < (list.Length.length r))%Z -> (list.Mem.mem (findMax obj r) r).

Axiom findMaxMax : forall (obj:(func (list ty) R)) (x:(list ty))
  (r:(list (list ty))), (0%Z < (list.Length.length r))%Z -> ((list.Mem.mem x
  r) -> ((infix_at obj x) <= (infix_at obj (findMax obj r)))%R).

Parameter mapIdxPrices: Z -> (func nat R) -> (list R).

Axiom mapIdxPricesDef : forall (i:Z) (sz:Z) (f:(func nat R)), (0%Z <= i)%Z ->
  ((i < sz)%Z -> ((0%Z <= sz)%Z -> ((list.NthNoOpt.nth i (mapIdxPrices sz
  f)) = (infix_at f (int_to_nat i))))).

Axiom mapIdxPricesLen : forall (sz:Z) (f:(func nat R)), (0%Z <= sz)%Z ->
  ((list.Length.length (mapIdxPrices sz f)) = sz).

Parameter castDistPres: (func (distr ty) (func (list (func ty (distr ty)))
  (list (func ty (distr ty))))).

Parameter m: nat.

Parameter n: nat.

Parameter predm: nat.

Parameter predn: nat.

Parameter unif: (func nat (distr nat)).

Parameter repeatM: (func nat (func (distr ty) (distr (list ty)))).

Parameter mu: (distr ty).

Parameter alg: (func (list ty) oc).

Parameter value: (func ty (func oc R)).

Parameter expect1: (func (distr ((list ty)* (list ty)* nat)%type) (func (func
  ((list ty)* (list ty)* nat)%type R) R)).

Parameter expect2: (func (distr R) R).

Parameter mapIdxMoves: (func Z (func (func nat (func ty (distr ty)))
  (list (func ty (distr ty))))).

Parameter mapWithIdxValue: (func (list ty) (func (func Z (func ty (func
  (list ty) R))) (list (func (list ty) R)))).

Parameter makePrefs: (func (list ty) (func (func ty (func ty R)) (list (func
  (list ty) R)))).

Parameter vcg: (func (list ty) (func (list ty) (func (func ty (func ty R))
  ((list ty)* (list R))%type))).

Parameter rsmcoins: (distr ((list ty)* (list ty)* nat)%type).

Parameter rsmdet: (func nat (func ((list ty)* (list ty)* nat)%type (func ty
  (func ty (ty* R)%type)))).

Parameter others: (func nat (func ty (distr ty))).

Parameter othermoves: (list (func ty (distr ty))).

Parameter truety1: ty.

Parameter truety2: ty.

Parameter report1: ty.

Parameter report2: ty.

Parameter f1: (func ((list ty)* (list ty)* nat)%type R).

Parameter f2: (func ((list ty)* (list ty)* nat)%type R).

Parameter ref_: unit.

Axiom castDistPres_rtype : forall (mu1:(distr ty)), forall (l:(list (func ty
  (distr ty)))), (allPres mu1 (infix_at (infix_at castDistPres mu1) l)) /\
  ((list.Length.length (infix_at (infix_at castDistPres mu1)
  l)) = (list.Length.length l)).

Axiom m_rtype : (1%Z <= (nat_to_int m))%Z.

Axiom n_rtype : (1%Z <= (nat_to_int n))%Z.

Axiom predm_rtype : ((Succ predm) = m).

Axiom predn_rtype : ((Succ predn) = n).

Axiom expect1_rtype : forall (mu1:(distr ((list ty)* (list ty)* nat)%type))
  (mu2:(distr ((list ty)* (list ty)* nat)%type)), forall (f11:(func
  ((list ty)* (list ty)* nat)%type R)) (f21:(func ((list ty)* (list ty)*
  nat)%type R)), (forall (r:((list ty)* (list ty)* nat)%type),
  (((list.Length.length (fst3 r)) = (nat_to_int predm)) /\
  (((list.Length.length (fst3 r)) = (nat_to_int predm)) /\
  (((list.Length.length (snd3 r)) = (nat_to_int m)) /\
  (((list.Length.length (snd3 r)) = (nat_to_int m)) /\
  ((nat_to_int (thd3 r)) < (nat_to_int m))%Z)))) -> ((infix_at f21
  r) <= (infix_at f11 r))%R) -> ((infix_at (infix_at expect1 mu2)
  f21) <= (infix_at (infix_at expect1 mu1) f11))%R.

Axiom mapIdxMoves_rtype : forall (sz:Z), forall (f:(func nat (func ty (distr
  ty)))), (0%Z <= sz)%Z ->
  ((list.Length.length (infix_at (infix_at mapIdxMoves sz) f)) = sz).

Axiom mapWithIdxValue_rtype : forall (xs1:(list ty)) (xs2:(list ty)),
  ((list.Length.length xs1) = (list.Length.length xs2)) -> forall (f:(func Z
  (func ty (func (list ty) R)))),
  ((list.Length.length (infix_at (infix_at mapWithIdxValue xs1)
  f)) = (list.Length.length (infix_at (infix_at mapWithIdxValue xs2) f))) /\
  (((list.Length.length (infix_at (infix_at mapWithIdxValue xs1)
  f)) = (list.Length.length xs1)) /\ ((forall (idx:Z), ((0%Z <= idx)%Z /\
  (idx < (list.Length.length xs1))%Z) -> ((list.NthNoOpt.nth idx
  (infix_at (infix_at mapWithIdxValue xs1) f)) = (infix_at (infix_at f idx)
  (list.NthNoOpt.nth idx xs1)))) /\ ((forall (idx:Z), ((0%Z <= idx)%Z /\
  (idx < (list.Length.length xs1))%Z) -> ((list.NthNoOpt.nth idx
  (infix_at (infix_at mapWithIdxValue xs2) f)) = (infix_at (infix_at f idx)
  (list.NthNoOpt.nth idx xs2)))) /\ forall (idx:Z), ((0%Z <= idx)%Z /\
  (idx < (list.Length.length xs1))%Z) -> ((differAt (int_to_nat idx) xs1
  xs2) -> ((allBut (int_to_nat idx) (infix_at (infix_at mapWithIdxValue xs1)
  f)) = (allBut (int_to_nat idx) (infix_at (infix_at mapWithIdxValue xs2)
  f))))))).

Axiom makePrefs_rtype : forall (reps1:(list ty)) (reps2:(list ty)),
  (((list.Length.length reps1) = (list.Length.length reps2)) /\
  ((list.Length.length reps1) = (nat_to_int m))) -> forall (wts:(func ty
  (func ty R))), ((list.Length.length (infix_at (infix_at makePrefs reps1)
  wts)) = (list.Length.length (infix_at (infix_at makePrefs reps2) wts))) /\
  (((list.Length.length (infix_at (infix_at makePrefs reps1)
  wts)) = (nat_to_int m)) /\ ((forall (i:Z), forall (alloc:(list ty)),
  ((0%Z <= i)%Z /\ ((i <= (nat_to_int predm))%Z /\
  ((nat_to_int m) = (list.Length.length alloc)))) ->
  ((infix_at (list.NthNoOpt.nth i (infix_at (infix_at makePrefs reps1) wts))
  alloc) = (infix_at (infix_at wts (list.NthNoOpt.nth i reps1))
  (list.NthNoOpt.nth i alloc)))) /\ ((forall (i:Z), forall (alloc:(list ty)),
  ((0%Z <= i)%Z /\ ((i <= (nat_to_int predm))%Z /\
  ((nat_to_int m) = (list.Length.length alloc)))) ->
  ((infix_at (list.NthNoOpt.nth i (infix_at (infix_at makePrefs reps2) wts))
  alloc) = (infix_at (infix_at wts (list.NthNoOpt.nth i reps2))
  (list.NthNoOpt.nth i alloc)))) /\ forall (i:Z), forall (alloc:(list ty)),
  ((0%Z <= i)%Z /\ ((i <= (nat_to_int predm))%Z /\
  ((nat_to_int m) = (list.Length.length alloc)))) -> ((differAt
  (int_to_nat i) reps1 reps2) -> ((allBut (int_to_nat i)
  (infix_at (infix_at makePrefs reps1) wts)) = (allBut (int_to_nat i)
  (infix_at (infix_at makePrefs reps2) wts))))))).

Axiom vcg_rtype : forall (reps1:(list ty)) (reps2:(list ty)),
  (((list.Length.length reps1) = (list.Length.length reps2)) /\
  ((list.Length.length reps1) = (nat_to_int m))) -> forall (surs1:(list ty))
  (surs2:(list ty)), ((surs1 = surs2) /\
  ((list.Length.length surs1) = (nat_to_int m))) -> forall (wts:(func ty
  (func ty R))), (forall (i:Z), ((0%Z <= i)%Z /\
  ((i <= (nat_to_int predm))%Z /\ (differAt (int_to_nat i) reps1 reps2))) ->
  (((infix_at (infix_at wts (list.NthNoOpt.nth i reps1)) (list.NthNoOpt.nth i
  (fst (infix_at (infix_at (infix_at vcg reps2) surs2)
  wts)))) - (list.NthNoOpt.nth i (snd (infix_at (infix_at (infix_at vcg
  reps2) surs2) wts))))%R <= ((infix_at (infix_at wts (list.NthNoOpt.nth i
  reps1)) (list.NthNoOpt.nth i (fst (infix_at (infix_at (infix_at vcg reps1)
  surs1) wts)))) - (list.NthNoOpt.nth i
  (snd (infix_at (infix_at (infix_at vcg reps1) surs1) wts))))%R)%R) /\
  ((list.Permut.permut surs1 (fst (infix_at (infix_at (infix_at vcg reps1)
  surs1) wts))) /\ (list.Permut.permut surs2
  (fst (infix_at (infix_at (infix_at vcg reps2) surs2) wts)))).

Parameter lam_others: nat -> ty -> ty -> (func (list ty) (distr R)).

Parameter lam_t: nat -> (func ty (func ty R)).

Parameter lam_others1: nat -> ty -> ty -> (func (list ty) (distr R)).

Parameter lam_t1: nat -> (func ty (func ty R)).

Axiom lam_others_def : forall (idx:nat) (t:ty) (s:ty) (others1:(list ty)),
  ((infix_at (lam_others idx t s) others1) = (munit (infix_at (infix_at value
  t) (infix_at alg (insertAt idx s others1))))).

Axiom lam_t_def : forall (idx:nat) (t:ty), forall (s:ty),
  ((infix_at (infix_at (lam_t idx) t) s) = (infix_at expect2
  (mbind (infix_at (infix_at repeatM predn) mu) (lam_others idx t s)))).

Axiom lam_others_def1 : forall (idx:nat) (t:ty) (s:ty) (others1:(list ty)),
  ((infix_at (lam_others1 idx t s)
  others1) = (munit (infix_at (infix_at value t) (infix_at alg (insertAt idx
  s others1))))).

Axiom lam_t_def1 : forall (idx:nat) (t:ty), forall (s:ty),
  ((infix_at (infix_at (lam_t1 idx) t) s) = (infix_at expect2
  (mbind (infix_at (infix_at repeatM predn) mu) (lam_others1 idx t s)))).

Axiom rsmdet_rtype : forall (idx:nat), forall (coins1:((list ty)* (list ty)*
  nat)%type) (coins2:((list ty)* (list ty)* nat)%type), ((coins1 = coins2) /\
  (((list.Length.length (fst3 coins1)) = (nat_to_int predm)) /\
  (((list.Length.length (fst3 coins2)) = (nat_to_int predm)) /\
  (((list.Length.length (snd3 coins1)) = (nat_to_int m)) /\
  (((list.Length.length (snd3 coins2)) = (nat_to_int m)) /\
  (((nat_to_int (thd3 coins1)) < (nat_to_int m))%Z /\
  ((nat_to_int (thd3 coins2)) < (nat_to_int m))%Z)))))) ->
  forall (truety11:ty) (truety21:ty), (truety11 = truety21) ->
  forall (report11:ty) (report21:ty),
  ((nat_to_int idx) <= (nat_to_int predn))%Z -> ((report11 = truety11) ->
  (((infix_at (infix_at (lam_t idx) truety11)
  (fst (infix_at (infix_at (infix_at (infix_at rsmdet idx) coins2) truety21)
  report21))) - (snd (infix_at (infix_at (infix_at (infix_at rsmdet idx)
  coins2) truety21) report21)))%R <= ((infix_at (infix_at (lam_t1 idx)
  truety11) (fst (infix_at (infix_at (infix_at (infix_at rsmdet idx) coins1)
  truety11) report11))) - (snd (infix_at (infix_at (infix_at (infix_at rsmdet
  idx) coins1) truety11) report11)))%R)%R).

Axiom others_rtype : True.

Axiom othermoves_rtype : (allPres mu othermoves) /\
  ((list.Length.length othermoves) = (nat_to_int predn)).

Axiom truety_rtype : (truety1 = truety2).

Axiom report_rtype : (report1 = truety1).

Parameter lam_othersurs: ((list ty)* (list ty)* nat)%type -> (func (list ty)
  (distr R)).

Parameter lam_othersurs1: ((list ty)* (list ty)* nat)%type -> (func (list ty)
  (distr R)).

Axiom lam_othersurs_def : forall (coins:((list ty)* (list ty)* nat)%type)
  (othersurs:(list ty)), ((infix_at (lam_othersurs coins)
  othersurs) = (munit (infix_at (infix_at value truety1) (infix_at alg
  (Init.Datatypes.cons (fst (infix_at (infix_at (infix_at (infix_at rsmdet
  Zero) coins) truety1) report1)) othersurs))))).

Axiom lam_othersurs_def1 : forall (coins:((list ty)* (list ty)* nat)%type)
  (othersurs:(list ty)), ((infix_at (lam_othersurs1 coins)
  othersurs) = (munit (infix_at (infix_at value truety2) (infix_at alg
  (Init.Datatypes.cons (fst (infix_at (infix_at (infix_at (infix_at rsmdet
  Zero) coins) truety2) report2)) othersurs))))).

Axiom ref__rtype : (forall (coins:((list ty)* (list ty)* nat)%type),
  ((infix_at f1 coins) = ((infix_at expect2
  (mbind (seqM (mapHO (sampleAndApply mu) othermoves))
  (lam_othersurs coins))) - (snd (infix_at (infix_at (infix_at (infix_at rsmdet
  Zero) coins) truety1) report1)))%R)) /\ forall (coins:((list ty)*
  (list ty)* nat)%type), ((infix_at f2 coins) = ((infix_at expect2
  (mbind (seqM (mapHO (sampleAndApply mu) othermoves))
  (lam_othersurs1 coins))) - (snd (infix_at (infix_at (infix_at (infix_at rsmdet
  Zero) coins) truety2) report2)))%R).

(* Why3 goal *)
Theorem ty_goal : forall (r:((list ty)* (list ty)* nat)%type),
  (((list.Length.length (fst3 r)) = (nat_to_int predm)) /\
  (((list.Length.length (fst3 r)) = (nat_to_int predm)) /\
  (((list.Length.length (snd3 r)) = (nat_to_int m)) /\
  (((list.Length.length (snd3 r)) = (nat_to_int m)) /\
  ((nat_to_int (thd3 r)) < (nat_to_int m))%Z)))) -> ((infix_at f2
  r) <= (infix_at f1 r))%R.
intros r (h1,(h2,(h3,(h4,h5)))).

Qed.

