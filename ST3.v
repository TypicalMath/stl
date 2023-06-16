Require Import List.
Require Import lang.
Import List.ListNotations.

Definition max := PeanoNat.Nat.max.

Reserved Notation "G '⇒3' D '⨡' n " (no associativity, at level 61). (* 21d2, 2a21 *)

Inductive ST3 : nat -> sequent -> Prop :=
  | TId:     forall (p : atom) G, ^x_p :: G ⇒3 ^x_p ⨡ 0
  | TRT:     forall G, G ⇒3 ⊤ ⨡ 0
  | TLF:     forall G D, ⊥ :: G ⇒3 D ⨡ 0
  | TLw:     forall G D P n, G ⇒3 D ⨡ n -> G ++ P ⇒3 D ⨡ S n
  | TRw:     forall G a n, G ⇒3 None ⨡ n -> G ⇒3 a ⨡ S n
  | TLa:    forall G D (a b : form) n, a::b::G ⇒3 D ⨡ n -> (a ∧ b)::G ⇒3 D ⨡ S n
  | TRa:     forall G (a b : form) n m, G ⇒3 a ⨡ n -> G ⇒3 b ⨡ m -> G ⇒3 (a ∧ b) ⨡ S (max n m)
  | TLo:     forall G D (a b : form) n m, a::G ⇒3 D ⨡ n -> b::G ⇒3 D ⨡ m -> (a ∨ b)::G ⇒3 D ⨡ S (max n m)
  | TRo1:    forall G (a b : form) n, G ⇒3 a ⨡ n -> G ⇒3 (a ∨ b) ⨡ S n
  | TRo2:    forall G (a b : form) n, G ⇒3 b ⨡ n -> G ⇒3 (a ∨ b) ⨡ S n
  | TLi:     forall G D (a b : form) n m, ∇(a ⊃ b)::G ⇒3 a ⨡ n -> ∇(a ⊃ b)::b::G ⇒3 D ⨡ m -> ∇(a ⊃ b)::G ⇒3 D ⨡ S (max n m)
  | TRi:     forall G (a b : form) n, a::(∇l G) ⇒3 b ⨡ n -> G ⇒3 (a ⊃ b) ⨡ S n
  | TN:      forall G a n, G ⇒3 Some a ⨡ n -> ∇l G ⇒3 Some (∇ a) ⨡ S n
  | TEx:    forall G P D a b n, G++a::b::P ⇒3 D ⨡ n -> G++b::a::P ⇒3 D ⨡ S n
where "G ⇒3 D ⨡ n" := (ST3 n (Seq G D)).

Notation "⇒3 a ⨡ n" := ([] ⇒3 a ⨡ n) (no associativity, at level 62).

Reserved Notation "G ⇒3+ D ⨡ n" (no associativity, at level 61). (* 21d2, 2a21 *)

Inductive ST3p : nat -> sequent -> Prop :=
| PTId:     forall (p : atom) G, ^x_p :: G ⇒3+ ^x_p ⨡ 0
| PTRT:     forall G, G ⇒3+ ⊤ ⨡ 0
| PTLF:     forall G D, ⊥ :: G ⇒3+ D ⨡ 0
| PTLw:     forall G D P n, G ⇒3+ D ⨡ n -> G ++ P ⇒3+ D ⨡ S n
| PTRw:     forall G a n, G ⇒3+ None ⨡ n -> G ⇒3+ a ⨡ S n
| PTLa:    forall G D (a b : form) n, a::b::G ⇒3+ D ⨡ n-> (a ∧ b)::G ⇒3+ D ⨡ S n
| PTRa:     forall G (a b : form) n m, G ⇒3+ a ⨡ n -> G ⇒3+ b ⨡ m-> G ⇒3+ (a ∧ b) ⨡ S (max n m)
| PTLo:     forall G D (a b : form) n m, a::G ⇒3+ D ⨡ n -> b::G ⇒3+ D ⨡ m -> (a ∨ b)::G ⇒3+ D ⨡ S (max n m)
| PTRo1:    forall G (a b : form) n, G ⇒3+ a ⨡ n -> G ⇒3+ (a ∨ b) ⨡ S n
| PTRo2:    forall G (a b : form) n, G ⇒3+ b ⨡ n -> G ⇒3+ (a ∨ b) ⨡ S n
| PTLi:     forall G D (a b : form) n m, ∇(a ⊃ b)::G ⇒3+ a ⨡ n -> ∇(a ⊃ b)::b::G ⇒3+ D ⨡ m -> ∇(a ⊃ b)::G ⇒3+ D ⨡ S (max n m)
| PTRi:     forall G (a b : form) n, a::(∇l G) ⇒3+ b ⨡ n -> G ⇒3+ (a ⊃ b) ⨡ S n
| PTN:      forall G a n, G ⇒3+ Some a ⨡ n -> ∇l G ⇒3+ Some (∇ a) ⨡ S n
| PTEx:    forall G P D a b n, G++a::b::P ⇒3+ D ⨡ n -> G++b::a::P ⇒3+ D ⨡ S n
| Cut:    forall (a : form) G P D n m, G ⇒3+ a ⨡ n -> a::P ⇒3+ D ⨡ m -> G++P ⇒3+ D ⨡ S (max n m)
where "G ⇒3+ D ⨡ n" := (ST3p n (Seq G D)).

Notation "⇒3+ a ⨡ n" := ([] ⇒3+ a ⨡ n) (no associativity, at level 62).


Lemma ST3_ST3p : forall n {s : sequent}, ST3 n s -> ST3p n s.
Proof.
  intros n s H. induction H.
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