Require Import List.
Require Import lang.
Import List.ListNotations.
Coercion form_to_some (P : form) : (option form) := Some P.
Coercion list_to_form (P : form) : (list form) := [P].

Reserved Notation "G ⇒ D" (no associativity, at level 61). (* 21d2 *)

Inductive ST : sequent -> Prop :=
  | Id:     forall a : form, a ⇒ a (* ST [a] a *)
  | RT:     [] ⇒ ⊤
  | LF:     ⊥ ⇒ None
  | Lw:     forall G D p, G ⇒ D -> p::G ⇒ D
  | Rw:     forall G p, G ⇒ None -> G ⇒ p
  | La1:    forall G D (a b : form), a::G ⇒ D -> (a ∧ b)::G ⇒ D
  | La2:    forall G D (a b : form), b::G ⇒ D -> (a ∧ b)::G ⇒ D
  | Ra:     forall G (a b : form), G ⇒ a -> G ⇒ b -> G ⇒ (a ∧ b)
  | Lo:     forall G D (a b : form), a::G ⇒ D -> b::G ⇒ D -> (a ∨ b)::G ⇒ D
  | Ro1:    forall G (a b : form), G ⇒ a -> G ⇒ (a ∨ b)
  | Ro2:    forall G (a b : form), G ⇒ b -> G ⇒ (a ∨ b)
  | Li:     forall G D (a b : form), G ⇒ a -> b::G ⇒ D -> ∇(a ⊃ b)::G ⇒ D
  | Ri:     forall G (a b : form), a::(∇l G) ⇒ b -> G ⇒ (a ⊃ b)
  | N:      forall G a, G ⇒ Some a -> ∇l G ⇒ Some (∇ a)
  | Ex:    forall G S D a b, G++a::b::S ⇒ D -> G++b::a::S ⇒ D
where "G ⇒ D" := (ST (Seq G D)).

Notation "⇒ p" := ([] ⇒ p) (no associativity, at level 62).


Reserved Notation "G ⇒+ D" (no associativity, at level 61). (* 21d2 *)

Inductive STp : sequent -> Prop :=
| PId:     forall a : form, a ⇒+ a
| PRT:     [] ⇒+ ⊤
| PLF:     ⊥ ⇒+ None
| PLw:     forall G D p, G ⇒+ D -> p::G ⇒+ D
| PRw:     forall G p, G ⇒+ None -> G ⇒+ p
| PLa1:    forall G D (a b : form), a::G ⇒+ D -> (a ∧ b)::G ⇒+ D
| PLa2:    forall G D (a b : form), b::G ⇒+ D -> (a ∧ b)::G ⇒+ D
| PRa:     forall G (a b : form), G ⇒+ a -> G ⇒+ b -> G ⇒+ (a ∧ b)
| PLo:     forall G D (a b : form), a::G ⇒+ D -> b::G ⇒+ D -> (a ∨ b)::G ⇒+ D
| PRo1:    forall G (a b : form), G ⇒+ a -> G ⇒+ (a ∨ b)
| PRo2:    forall G (a b : form), G ⇒+ b -> G ⇒+ (a ∨ b)
| PLi:     forall G D (a b : form), G ⇒+ a -> b::G ⇒+ D -> ∇(a ⊃ b)::G ⇒+ D
| PRi:     forall G (a b : form), a::(∇l G) ⇒+ b -> G ⇒+ (a ⊃ b)
| PN:      forall G a, G ⇒+ Some a -> ∇l G ⇒+ Some (∇ a)
| PEx:    forall G S D a b, G++a::b::S ⇒+ D -> G++b::a::S ⇒+ D
| Cut:    forall (a : form) G S D, G ⇒+ a -> a::S ⇒+ D -> G++S ⇒+ D
where "G ⇒+ D" := (STp (Seq G D)).

Notation "⇒+ p" := ([] ⇒+ p) (no associativity, at level 62).


Lemma ST_STp : forall {s : sequent}, ST s -> STp s.
Proof.
  intros s H. induction H.
    - apply PId.
    - apply PRT.
    - apply PLF.
    - apply PLw. apply IHST.
    - apply PRw. apply IHST.
    - apply PLa1. apply IHST.
    - apply PLa2. apply IHST.
    - apply PRa.
      + apply IHST1.
      + apply IHST2.
    - apply PLo.
      + apply IHST1.
      + apply IHST2.
    - apply PRo1. apply IHST.
    - apply PRo2. apply IHST.
    - apply PLi.
      + apply IHST1.
      + apply IHST2.
    - apply PRi. apply IHST.
    - apply PN. apply IHST.
    - apply PEx. apply IHST.
Defined.

Coercion ST_STp : ST >-> STp.


Lemma nabla_N : forall G (a : form) n, G ⇒ a -> n^∇l G ⇒ n^∇ a.
Proof.
  induction n.
    - simpl. rewrite map_id. intros H. apply H.
    - intros H. rewrite nabla_Nabl_list. simpl.
      apply IHn in H. apply N in H. apply H.
Qed.

Lemma nabla_N_p : forall G (a : form) n, G ⇒+ a -> n^∇l G ⇒+ n^∇ a.
Proof.
  induction n.
    - simpl. rewrite map_id. intros H. apply H.
    - intros H. rewrite nabla_Nabl_list. simpl.
      apply IHn in H. apply PN in H. apply H.
Qed.

Lemma nabla_form : forall a b : form, a ⇒ b -> [∇ a] ⇒ (∇ b).
Proof. intros. rewrite nabla_singleton. rewrite nabla_some. apply N. apply H. Qed.

Lemma nabla_form_p : forall a b : form, a ⇒+ b -> [∇ a] ⇒+ (∇ b).
Proof. intros. rewrite nabla_singleton. rewrite nabla_some. apply PN. apply H.
Qed.

Lemma nabla_n_form : forall n (a b : form), a ⇒ b -> [n^∇ a] ⇒ (n^∇ b).
Proof. intros. rewrite nabla_n_singleton. rewrite nabla_n_some. apply nabla_N. apply H. Qed.

Lemma nabla_n_form_p : forall n (a b : form), a ⇒+ b -> [n^∇ a] ⇒+ (n^∇ b).
Proof. intros. rewrite nabla_n_singleton. rewrite nabla_n_some. apply nabla_N_p. apply H. Qed.

Lemma nabla_n_dist_and : forall a b n, [n^∇ (a ∧ b)] ⇒ n^∇ a ∧ n^∇ b.
Proof.
  intros.
  apply Ra;
    rewrite nabla_n_some; rewrite nabla_n_singleton; apply nabla_N.
    - apply La1. apply Id.
    - apply La2. apply Id.
Qed.

Lemma nabla_box : forall a, ∇ (⎕ a) ⇒ a.
Proof. intros. apply Li. apply RT. apply Id. Qed.
Definition nabla_box_p := fun a => ST_STp (nabla_box a).

Lemma box_nabla: forall a : form, a ⇒ ⎕ ∇ a.
Proof.
  intros. apply Ri.
  apply Lw. apply Id.
Qed.
Definition box_nabla_p := fun a => ST_STp (box_nabla a).

Lemma nabla_dist_or : forall a b, ∇ (a ∨ b) ⇒+ ∇ a ∨ ∇ b.
Proof.
  intros. apply (Cut (∇(⎕ (∇ a ∨ ∇ b))) ([∇ (a ∨ b)]) nil (∇ a ∨ ∇ b)).
    - rewrite nabla_singleton. apply PN.
      apply PLo.
        + apply PRi. apply PLw. apply PRo1. apply PId.
        + apply PRi. apply PLw. apply PRo2. apply PId.
    - apply nabla_box_p.
Qed.

Lemma nabla_n_dist_or : forall a b n, n^∇ (a ∨ b) ⇒+ n^∇ a ∨ n^∇ b.
Proof.
  induction n. apply PId.
  apply (Cut (∇ (n^∇ a ∨ n^∇ b)) ([S n ^∇ (a ∨ b)]) []).
    - simpl. rewrite nabla_singleton. apply PN. apply IHn.
    - apply nabla_dist_or.
Qed.

Lemma nabla_bot : ∇ ⊥ ⇒+ ⊥.
Proof.
  apply (Cut (∇⎕⊥) (∇⊥)).
    - apply nabla_form_p. apply PRw. apply PLF.
    - apply nabla_box_p.
Qed.
(* -------------------------------------------------------------- *)
Lemma nabla_n_bot : forall n m, n^∇ ⊥ ⇒+ (n - m)^∇ ⊥.
Proof. 
  induction m; simpl.
    - rewrite PeanoNat.Nat.sub_0_r. apply PId.
    - apply (Cut ((n - m) ^∇ ⊥) (n ^∇ ⊥ )).
      + apply IHm.
      + rewrite PeanoNat.Nat.sub_succ_r.
        destruct (n - m).
          * simpl. apply PId.
          * unfold pred. rewrite nabla_Sn.
            apply nabla_n_form_p. apply nabla_bot.
Qed.

Tactic Notation "swap_hd" := apply (Ex [] _ _ _ _); simpl.

Lemma modus_ponens : forall a b : form, [∇(a ⊃ b); a] ⇒ b.
Proof. intros. apply Li.
    - apply Id.
    - swap_hd. apply Lw. apply Id.
Qed.


Lemma nabla_n_dist_impl : forall a b n, n^∇ (a ⊃ b) ⇒ n^∇ a ⊃ n^∇ b.
Proof.
  intros. apply Ri. simpl.
  rewrite <- nabla_Nabl.
  rewrite nabla_Sn.
  rewrite nabla_n_singleton.
  rewrite <- map_cons.
  apply nabla_N.
  swap_hd. apply modus_ponens.
Qed.