Require Import List.
Require Import lang.
Import List.ListNotations.

Reserved Notation "G ⇒3 D" (no associativity, at level 61). (* 21d2 *)

Inductive ST3 : sequent -> Prop :=
  | TId:     forall (p : atom) G, ^x_p :: G ⇒3 ^x_p
  | TRT:     forall G, G ⇒3 ⊤
  | TLF:     forall G D, ⊥ :: G ⇒3 D
  | TLw:     forall G D P, G ⇒3 D -> G ++ P ⇒3 D
  | TRw:     forall G a, G ⇒3 None -> G ⇒3 a
  | TLa:    forall G D (a b : form), a::b::G ⇒3 D -> (a ∧ b)::G ⇒3 D
  | TRa:     forall G (a b : form), G ⇒3 a -> G ⇒3 b -> G ⇒3 (a ∧ b)
  | TLo:     forall G D (a b : form), a::G ⇒3 D -> b::G ⇒3 D -> (a ∨ b)::G ⇒3 D
  | TRo1:    forall G (a b : form), G ⇒3 a -> G ⇒3 (a ∨ b)
  | TRo2:    forall G (a b : form), G ⇒3 b -> G ⇒3 (a ∨ b)
  | TLi:     forall G D (a b : form), ∇(a ⊃ b)::G ⇒3 a -> ∇(a ⊃ b)::b::G ⇒3 D -> ∇(a ⊃ b)::G ⇒3 D
  | TRi:     forall G (a b : form), a::(∇l G) ⇒3 b -> G ⇒3 (a ⊃ b)
  | TN:      forall G a, G ⇒3 Some a -> ∇l G ⇒3 Some (∇ a)
  | TEx:    forall G P D a b, G++a::b::P ⇒3 D -> G++b::a::P ⇒3 D
where "G ⇒3 D" := (ST3 (Seq G D)).

Notation "⇒3 a" := ([] ⇒3 a) (no associativity, at level 62).


Reserved Notation "G ⇒3+ D" (no associativity, at level 61). (* 21d2 *)

Inductive ST3p : sequent -> Prop :=
| PTId:     forall (p : atom) G, ^x_p :: G ⇒3+ ^x_p
| PTRT:     forall G, G ⇒3+ ⊤
| PTLF:     forall G D, ⊥ :: G ⇒3+ D
| PTLw:     forall G D P, G ⇒3+ D -> G ++ P ⇒3+ D
| PTRw:     forall G a, G ⇒3+ None -> G ⇒3+ a
| PTLa:    forall G D (a b : form), a::b::G ⇒3+ D -> (a ∧ b)::G ⇒3+ D
| PTRa:     forall G (a b : form), G ⇒3+ a -> G ⇒3+ b -> G ⇒3+ (a ∧ b)
| PTLo:     forall G D (a b : form), a::G ⇒3+ D -> b::G ⇒3+ D -> (a ∨ b)::G ⇒3+ D
| PTRo1:    forall G (a b : form), G ⇒3+ a -> G ⇒3+ (a ∨ b)
| PTRo2:    forall G (a b : form), G ⇒3+ b -> G ⇒3+ (a ∨ b)
| PTLi:     forall G D (a b : form), ∇(a ⊃ b)::G ⇒3+ a -> ∇(a ⊃ b)::b::G ⇒3+ D -> ∇(a ⊃ b)::G ⇒3+ D
| PTRi:     forall G (a b : form), a::(∇l G) ⇒3+ b -> G ⇒3+ (a ⊃ b)
| PTN:      forall G a, G ⇒3+ Some a -> ∇l G ⇒3+ Some (∇ a)
| PTEx:    forall G P D a b, G++a::b::P ⇒3+ D -> G++b::a::P ⇒3+ D
| Cut:    forall (a : form) G P D, G ⇒3+ a -> a::P ⇒3+ D -> G++P ⇒3+ D
where "G ⇒3+ D" := (ST3p (Seq G D)).

Notation "⇒3+ a" := ([] ⇒3+ a) (no associativity, at level 62).


Lemma ST3_ST3p : forall {s : sequent}, ST3 s -> ST3p s.
Proof.
  intros s H. induction H.
    - apply PTId.
    - apply PTRT.
    - apply PTLF.
    - apply PTLw. apply IHST3.
    - apply PTRw. apply IHST3.
    - apply PTLa. apply IHST3.
    - apply PTRa.
      + apply IHST3_1.
      + apply IHST3_2.
    - apply PTLo.
      + apply IHST3_1.
      + apply IHST3_2.
    - apply PTRo1. apply IHST3.
    - apply PTRo2. apply IHST3.
    - apply PTLi.
      + apply IHST3_1.
      + apply IHST3_2.
    - apply PTRi. apply IHST3.
    - apply PTN. apply IHST3.
    - apply PTEx. apply IHST3.
Defined.

Coercion ST3_ST3p : ST3 >-> ST3p.