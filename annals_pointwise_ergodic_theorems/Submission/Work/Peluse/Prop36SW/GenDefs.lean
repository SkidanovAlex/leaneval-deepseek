import Mathlib
import Submission.Work.Peluse.Holds.Corrected

/-!
# `PeluseLadderA` with a general parameter type

`Work.Peluse.C46.PeluseLadderA` (Peluse's Lemma 5.7) quantifies its parameter set as
`A : Finset (Fin n → ℤ)` and its coefficient functions as `p : ι → (Fin n → ℤ) → ℤ`.  The
`d - 1`-fold iteration of that lemma (Peluse's §5, the proof of her Proposition 3.6) produces, at
each step, a parameter set which is a *dependent product* (`A × paramBox × shifts`), so it is far
more convenient to have the lemma available for an arbitrary finite parameter type `P`.

This module provides that form.  The definitions `pDirG`, `pDirFamG`, `conclDirG` are the
parameter-type-generic copies of `Work.Peluse.UControl.pDir`, `pDirFam` and `conclDir`, and
`PeluseLadderAG` is the corresponding copy of `PeluseLadderA`.  The transfer
`peluseLadderAG_of_ladder` is by encoding `P` into `Fin 1 → ℤ` along an injection
`P ↪ ℤ` (`Fintype.equivFin` followed by the cast `ℕ → ℤ`), which is available because `P` is
finite.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Prop36SW

noncomputable section

open Work.Peluse.UControl

/-- The ladder's `pDir` with a general parameter type: the direction `(∑_{s ∈ ω} p_s(a)·a'_s)[M₁]`. -/
def pDirG {ι : Type} {k : ι → ℕ} {P : Type} (p : ι → P → ℤ) (M₁ : ℕ)
    (a : P) (a' : Slot ι k → ℤ) (ω : SlotSet ι k) : Finset ℤ :=
  arithIcc (∑ s ∈ ω.1, p s.1 a * a' s) M₁

/-- The ladder's `pDirFam` with a general parameter type. -/
def pDirFamG {ι : Type} {k : ι → ℕ} {P : Type} (p : ι → P → ℤ) (M₁ : ℕ)
    (a : P) (a' : Slot ι k → ℤ) {kω : SlotSet ι k → ℕ} (j : FamIdx kω) : Finset ℤ :=
  pDirG p M₁ a a' j.1

/-- The ladder's `conclDir` with a general parameter type: `t'` long directions at the peeled
slot's coefficient and the short directions of the remaining slots. -/
def conclDirG {ι : Type} {k : ι → ℕ} {P : Type} (p : ι → P → ℤ) (M₁ M₂ : ℕ) (γ' : ℝ)
    (s₀ : Slot ι k) (t' : ℕ) (a : P) (b : Slot ι k → ℤ) {kω : SlotSet ι k → ℕ} :
    ConclIdx s₀ kω t' → Finset ℤ :=
  fun j => match j with
    | Sum.inl _ => arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat
    | Sum.inr ⟨ω, r⟩ => arithIcc (∑ s ∈ ω.1, p s.1 a * b s) M₁

/-- The index type of the *short* directions of the ladder's conclusion: the nonempty subsets of
the slots avoiding the peeled slot `s₀`, with the ladder's multiplicities. -/
abbrev ShortIdx {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ)
    (kω : SlotSet ι k → ℕ) (s₀ : Slot ι k) : Type :=
  Σ ω : {s : Finset (Slot ι k) // s.Nonempty ∧ s₀ ∉ s}, Fin (kω ⟨ω.1, ω.2.1⟩)

/-- The *short* direction family of the ladder's conclusion (with a general parameter type `P`),
in `Fin`-normal form. -/
def shortFamG {ι : Type} [Fintype ι] [DecidableEq ι] {k : ι → ℕ} {P : Type}
    (kω : SlotSet ι k → ℕ) (p : ι → P → ℤ) (M₁ : ℕ) (a : P) (b : Slot ι k → ℤ)
    (s₀ : Slot ι k) : Fin (Fintype.card (ShortIdx k kω s₀)) → Finset ℤ :=
  fun j => arithIcc (∑ s ∈ ((Fintype.equivFin (ShortIdx k kω s₀)).symm j).1.1, p s.1 a * b s) M₁

/-- **Peluse's Lemma 5.7 with a general parameter type.**  Same statement as
`Work.Peluse.C46.PeluseLadderA` with `(Fin n → ℤ)` replaced by an arbitrary finite type `P`. -/
def PeluseLadderAG : Prop :=
  ∀ {P : Type} [Fintype P] [DecidableEq P] {ι : Type} [Fintype ι] [DecidableEq ι]
    (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (p : ι → P → ℤ) (D : ℕ),
    ∃ (K : ℕ) (C₀ : ℝ) (t' : ℕ) (c : ℝ),
      1 ≤ K ∧ 0 < C₀ ∧ 1 ≤ t' ∧ 0 < c ∧
      ∀ (A : Finset P) (M₁ M₂ N : ℕ) (γ γ' : ℝ) (f : P → ℤ → ℂ),
        1 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ N → ((M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ)) →
        0 < γ → γ ≤ 1 → 0 < γ' → C₀ * γ' ≤ γ ^ K →
        (∀ i a, a ∈ A → 0 < p i a) →
        (∀ i a, a ∈ A → p i a * (M₁ : ℤ) * (M₂ : ℤ) ≤ (N : ℤ)) →
        (∀ i a, a ∈ A → |p i a| * (M₁ : ℤ) * (M₂ : ℤ) ≤ (D : ℤ) * (N : ℤ)) →
        (∀ a ∈ A, ∀ x, ‖f a x‖ ≤ 1) → (∀ a ∈ A, SupportIn (f a) N) →
        C₀ * (γ * γ') ^ (-(K : ℤ)) ≤ (M₂ : ℝ) →
        γ ≤ ((A.card : ℝ))⁻¹ * ((paramBox (k := k) M₂).card : ℝ)⁻¹ *
              ∑ a ∈ A, ∑ a' ∈ paramBox (k := k) M₂,
                boxNorm (Fintype.card (FamIdx kω))
                  (fun j : Fin (Fintype.card (FamIdx kω)) =>
                    pDirFamG p M₁ a a' ((Fintype.equivFin (FamIdx kω)).symm j)) (symIcc N) (f a) →
        ∀ s₀ : Slot ι k,
          c * (γ * γ') ^ K ≤
            ((A.card : ℝ))⁻¹ * ((paramBox (k := k) M₂).card : ℝ)⁻¹ *
              ∑ a ∈ A, ∑ b ∈ paramBox (k := k) M₂,
                boxNorm (Fintype.card (ConclIdx s₀ kω t'))
                  (fun j : Fin (Fintype.card (ConclIdx s₀ kω t')) =>
                    conclDirG p M₁ M₂ γ' s₀ t' a b
                      ((Fintype.equivFin (ConclIdx s₀ kω t')).symm j))
                  (symIcc N) (f a)

end

end Work.Peluse.Prop36SW
