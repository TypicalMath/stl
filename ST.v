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