Definition atom := nat.

Inductive form : Type :=
| Var : atom  -> form
| Bot : form
| Top : form
| Nabl : form -> form
| Disj : form -> form -> form
| Conj : form -> form -> form
| Impl : form -> form -> form.

Definition Neg (p : form) : form := Impl p Bot.

Notation "^x_ x" := (Var x) (at level 30).
Coercion atom_as_form (a : atom) : form := Var a.


Notation "⊥" := Bot. (* 22a5 *)
Notation "⊤" := Top. (* 22a4 *)
Notation "¬ p" := (Neg p) (at level 31). (* 00ac *)
Notation "∇ p" := (Nabl p) (at level 32). (* 2207 *)
Infix "∧" := Conj (left associativity, at level 34). (* 2227 *)
Infix "∨" := Disj (left associativity, at level 36). (* 2228 *)
Infix "⊃" := Impl (right associativity, at level 37). (* 2283 *)

Notation "⎕ p" := (⊤ ⊃ p) (at level 33). (* 2395 *)

Require Import PeanoNat.
Theorem formeq_dec : forall p q : form, {p = q} + {p <> q}.
Proof.
  induction p; induction q;
      try (left; reflexivity);
      try (right; intros H; inversion H; contradiction H);
      try (destruct (IHp1 q1); destruct (IHp2 q2);
        subst;
        try (right; intros H; inversion H; contradiction n);
        left; reflexivity).
    - destruct (PeanoNat.Nat.eq_dec a a0).
      + left. subst. reflexivity.
      + right. intros H. inversion H. contradiction n.
    - destruct (IHp q); subst;
      try (right; intros H; inversion H; contradiction n);
      left; reflexivity.
Defined.

Fixpoint formeq (p q : form) : bool :=
  match (p, q) with
  | (^x_n, ^x_m) => PeanoNat.Nat.eqb n m
  | (⊥, ⊥) => true
  | (⊤, ⊤) => true
  | (∇p, ∇q) => formeq p q
  | (p1 ∧ p2, q1 ∧ q2) => (formeq p1 q1) && (formeq p2 q2)
  | (p1 ∨ p2, q1 ∨ q2) => (formeq p1 q1) && (formeq p2 q2)
  | (p1 ⊃ p2, q1 ⊃ q2) => (formeq p1 q1) && (formeq p2 q2)
  | _ => false
  end.

Lemma formeq_sound : forall p q : form, formeq p q = true -> p = q.
Proof.
  induction p; induction q;
    intros E; simpl in E;
    inversion E;
    f_equal;
    try (
      destruct (andb_prop _ _ E) as [E1 E2];
      try apply (IHp1 q1 E1);
      try apply (IHp2 q2 E2)
    );
    try reflexivity.
    - apply Nat.eqb_eq. apply E.
    - apply (IHp q E).
Qed.

Lemma formeq_refl : forall p : form, formeq p p = true.
Proof.
  intros p. induction p; simpl;
    try apply andb_true_intro; try split;
    try apply IHp;
    try apply IHp1;
    try apply IHp2.
  apply Nat.eqb_refl.
Qed.

Lemma formeq_complete : forall p q : form, p = q -> formeq p q = true.
Proof. intros p q E. rewrite E. apply formeq_refl. Qed. 

Fixpoint rank (p : form) : nat :=
  match p with
  | ∇p => rank p
  | p1 ∧ p2 => S ((rank p1) + (rank p2))
  | p1 ∨ p2 => S ((rank p1) + (rank p2))
  | p1 ⊃ p2 => S ((rank p1) + (rank p2))
  | _ => S O
  end.

Fixpoint nabla (n : nat) (a : form) : form :=
  match n with
  | O => a
  | S n' => ∇ (nabla n' a)
  end.

Infix "^∇" := nabla (right associativity, at level 32).

Require Import List.
Import List.ListNotations.

Notation "∇l G" := (map Nabl G) (no associativity, at level 60).
Notation "∇o D" := (option_map Nabl D) (no associativity, at level 60).
Notation "n ^∇l G" := (map (nabla n) G) (no associativity, at level 60).
Notation "n ^∇o D" := (option_map (nabla n) D) (no associativity, at level 60).

Definition context : Type := list form.

Definition subsingleton : Type := option form.

Lemma nabla_Sn : forall a n, (S n)^∇ a = n^∇ (∇ a).
Proof. induction n. reflexivity. simpl in *. rewrite <- IHn. reflexivity. Qed.

Lemma nabla_singleton : forall a, [∇ a] = ∇l [a]. Proof. reflexivity. Qed.

Lemma nabla_some : forall a, Some (∇ a) = ∇o Some a. Proof. reflexivity. Qed.

Lemma nabla_n_singleton : forall a n, [n^∇ a] = n^∇l [a]. Proof. reflexivity. Qed.

Lemma nabla_n_some : forall a n, Some (n^∇ a) = n^∇o (Some a). Proof. reflexivity. Qed.

Lemma nabla_Nabl : forall a n, S n ^∇ a = ∇ (n ^∇ a).
Proof. reflexivity. Qed.

Lemma nabla_Nabl_list : forall G n, S n ^∇l G = ∇l (n ^∇l G).
Proof.
  induction G; simpl; try reflexivity.
  intros n. simpl in IHG. rewrite (IHG n). reflexivity.
Qed.

Lemma nabla_Nabl_option : forall D n, S n ^∇o D = ∇o (n ^∇o D).
Proof. induction D; simpl; try reflexivity. Qed.

Inductive sequent : Type :=
| Seq : context -> subsingleton -> sequent.

Definition replace_form (l : context) (a : form) (b : form) : list form := a :: (remove formeq_dec b l).

Notation "l '[[' b '::=' a ']]'" := (replace_form l a b) (at level 100).

Coercion form_to_some (P : form) : (option form) := Some P.
Coercion list_to_form (P : form) : (list form) := [P].