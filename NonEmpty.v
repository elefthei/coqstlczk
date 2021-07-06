Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
      
(** ** NonEmpty lists *)
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.
Local Open Scope nat_scope.
Require Import Coq.micromega.Lia.

Inductive NonEmpty (a : Type) : Type :=
  | NE_Sing : a -> NonEmpty a
  | NE_Cons : a -> NonEmpty a -> NonEmpty a.

Arguments NE_Sing [_] _.
Arguments NE_Cons [_] _ _.

Fixpoint NE_from_list {a} (x : a) (xs : list a) : NonEmpty a :=
  match xs with
    | nil => NE_Sing x
    | cons y ys => NE_Cons x (NE_from_list y ys)
  end.

Fixpoint NE_length {a} (ne : NonEmpty a) : nat :=
  match ne with
    | NE_Sing x => 1
    | NE_Cons x xs => 1 + NE_length xs
  end.

Fixpoint NE_to_list {a} (ne : NonEmpty a) : list a :=
  match ne with
    | NE_Sing x => cons x nil
    | NE_Cons x xs => cons x (NE_to_list xs)
  end.

Coercion NE_to_list : NonEmpty >-> list.

Lemma NE_to_list_from_list {a} : forall (x : a) xs,
  NE_to_list (NE_from_list x xs) = x :: xs.
Proof.
  intros x xs.
  generalize dependent x.
  induction xs; cbn; try reflexivity.
  - rewrite IHxs; intros; reflexivity.
Defined.

Definition NE_head {a} (ne : NonEmpty a) : a :=
  match ne with
    | NE_Sing x => x
    | NE_Cons x _ => x
  end.
Fixpoint NE_last {a} (ne : NonEmpty a) : a :=
  match ne with
    | NE_Sing x => x
    | NE_Cons x xs => NE_last xs
  end.
Fixpoint NE_tail a (ne : NonEmpty a) : list a :=
  match ne with
    | NE_Sing x => [x]
    | NE_Cons x xs => x :: NE_tail xs
  end.

Fixpoint NE_app a (na: NonEmpty a)(nb: NonEmpty a): NonEmpty a :=
  match na with
  | NE_Cons h ts => NE_Cons h (NE_app ts nb)
  | NE_Sing a => NE_Cons a nb
  end.

Fixpoint NE_map a b (f:a -> b)(na: NonEmpty a): NonEmpty b :=
  match na with
  | NE_Cons h ts => NE_Cons (f h) (NE_map f ts)
  | NE_Sing a => NE_Sing (f a)
  end.

Lemma NE_length_gt_0: forall s (l: NonEmpty s),
    NE_length l > 0.
  intros. induction l; cbn; lia.
Defined.

(** NonEmpty nat *)
Fixpoint NE_max (na: NonEmpty nat): nat :=
  match na with
  | NE_Cons h ts => if (NE_max ts) <? h then h else (NE_max ts)
  | NE_Sing a => a
  end.

Lemma NE_max_cons_h: forall h ts,
  NE_max ts <= h ->
  NE_max (NE_Cons h ts) = h.
Proof.
  intros; destruct h.
  - inversion H.
    cbn.
    rewrite H1.
    reflexivity.
  - cbn.
    destruct (Nat.leb_spec0 (NE_max ts) h).
    + reflexivity.
    + inversion H.
      reflexivity.      
      apply n in H1.
      contradiction.
Defined.

Lemma NE_max_cons_ts: forall h ts,
  h <= NE_max ts ->
  NE_max (NE_Cons h ts) = NE_max ts.
Proof.
  intros; destruct h.
  - reflexivity.
  - cbn.
    destruct (NE_max ts <=? h) eqn:Hn.
    rewrite Nat.leb_le in Hn.
    lia.
    reflexivity.
Defined.

Lemma NE_max_cons: forall h ts i,
    NE_max (NE_Cons h ts) <= i ->
    h <= i /\ NE_max ts <= i.
Proof.
  intros.
  assert(Hnot: forall a b, ~ a <= b -> b < a) by lia.
  destruct (Nat.le_decidable (NE_max ts) h); split.
  - pose proof (NE_max_cons_h H0).
    rewrite H1 in H.
    assumption.
  - pose proof (NE_max_cons_h H0).
    rewrite H1 in H.
    exact (Nat.le_trans _ _ _ H0 H).
Admitted.

Lemma NE_max_sing: forall v i,
    NE_max (NE_Sing v) <= i ->
    v <= i.
  intros; cbn in *; assumption.
Defined.

Lemma NE_map_cons: forall a b (f: a -> b) h ts,
  NE_map f (NE_Cons h ts) = NE_Cons (f h) (NE_map f ts).
  intros; cbn; reflexivity.
Defined.

Lemma NE_map_sing: forall a b (f: a -> b) v,
    NE_map f (NE_Sing v) = NE_Sing (f v).
  intros; cbn; reflexivity.
Defined.
