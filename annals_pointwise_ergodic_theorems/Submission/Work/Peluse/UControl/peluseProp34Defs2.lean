import Mathlib
import Submission.Work.Peluse.UControl.peluseProp34Defs

/-!
# The corrected interfaces for the proof of Peluse's Proposition 3.4 (`Prop34`)

This module records the **corrected** forms of the two chapters of the proof of `Prop34` found in
`NOTES_UControl_peluseProp34.md` §3 and §7.  The versions in `pelusePetChapterDefs.lean`
(`PetChapter`) and `peluseProp34Defs.lean` (`LinFamBound`) carry (i) a window hypothesis of the form
`A·δ' ≤ γ^K` while their conclusion's level carries `A^{−K}`, and (ii) a gauge that is a *power* of
the level; both make the constant bookkeeping of the assembly fail (the exponents point the wrong way
in `A`, resp. in `γ`).  The corrected clauses are:

* **matched powers of the scale constant**: the window is `A^{K₀+3}·δ' ≤ γ^K` and the conclusion
  `γ^K ≤ A^{K₀}·(averaged quantity)`, with `K₀` (and `Cne₀`) produced *before* `A` — this is the
  faithful rendering of Peluse's `δ' ≪_{C,ℓ} δ^{O_ℓ(1)}`, whose implied constant is a polynomial in
  the scale imbalance `C ↔ A`;
* **a linear gauge** `δ' ≤ γ/C₄` in the averaged Lemma 4.10, exactly as in the workspace's flat
  analogue `PETTwo.pet_family_boxnorm_of_configuration` (`γ' ≤ γ/(1000(t+1))`).

Everything else is as in the two files imported above; the two predicates below are stated so that
the assembly

`Prop34 P ⟸ PetChapterV3 P ∧ (∀ D, LinFamBoundLin P D)`

is pure bookkeeping (the three transfer lemmas already proved in `peluseProp34.lean`, the
unfolding of `petDir`, and definite polynomial conditions on `A`).
-/

set_option autoImplicit false
open scoped BigOperators
open Polynomial

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse

/-- `linFamAvg` is antitone in its `A`-free presentation: the averaged fibre at the level `γ`: this
is just a name for the quantity the PET chapter produces (see `linFamAvg`). -/
abbrev petLevel (K₀ : ℕ) (A γ : ℝ) (K : ℕ) : ℝ := γ ^ K / A ^ K₀

/-- **The PET chapter with matched powers of the scale constant** (the corrected form of
`PetChapter`): for every scale constant `A ≥ 1` there are `K ≤ K₀` and `Cne ≤ Cne₀·A` such that,
whenever the window satisfies `A^{K₀+3}·δ' ≤ γ^K`, the level `γ^K/A^{K₀}` is at most the averaged
linear-configuration value.  `K₀ ≥ 4` and `Cne₀ ≥ 1` depend on `P` only and are produced before `A`,
which is what lets the consumer choose `A` to absorb the constants of the last step. -/
def PetChapterV3 (P : Polynomial ℤ) : Prop :=
  ∃ D : IdxDatum, 2 ≤ Fintype.card (D.I (P.natDegree - 1)) ∧
  ∃ (K₀ Cne₀ : ℕ), 4 ≤ K₀ ∧ 1 ≤ Cne₀ ∧
  ∀ A : ℝ, 1 ≤ A → ∃ K : ℕ, 2 ≤ K ∧ K ≤ K₀ ∧ ∃ Cne : ℕ, 1 ≤ Cne ∧ (Cne : ℝ) ≤ (Cne₀ : ℝ) * A ∧
    ∀ (N M : ℕ) (F : Fin (P.natDegree + 1) → ℤ → ℂ) (γ δ' : ℝ),
      2 ≤ P.natDegree → 1 ≤ N → 1 ≤ M →
      (N : ℝ) ≤ A * (M : ℝ) ^ P.natDegree →
      (M : ℝ) ^ P.natDegree ≤ A * γ⁻¹ * (N : ℝ) →
      0 < γ → γ ≤ 1 → 0 < δ' → A ^ (K₀ + 3) * δ' ≤ γ ^ K →
      2 ≤ (⌊δ' * (M : ℝ)⌋).toNat →
      (∀ i x, ‖F i x‖ ≤ 1) → (∀ i, SupportIn (F i) N) →
      γ ≤ ‖LambdaMD N M P F‖ →
      ∃ (b : Fin (Fintype.card (D.I (P.natDegree - 1))) → Bool)
        (β : D.Idx P.natDegree → Fin (Fintype.card (D.I (P.natDegree - 1))) → ℤ),
        (∀ a ∈ D.parBox P.natDegree (⌊δ' * (M : ℝ)⌋).toNat,
            ∀ i : Fin (Fintype.card (D.I (P.natDegree - 1))), ∀ y ∈ Finset.Icc 1 M,
              |petDir D P.natDegree P.leadingCoeff a i * (y : ℤ) + β a i|
                ≤ (Cne : ℤ) * (N : ℤ)) ∧
        γ ^ K ≤ A ^ K₀ * linFamAvg D P.natDegree P.leadingCoeff N M (⌊δ' * (M : ℝ)⌋).toNat
          (F ⟨P.natDegree, Nat.lt_succ_self _⟩) b β

/-- **The averaged Lemma 4.10 with a *linear* gauge** (the corrected form of `LinFamBound`): from
`γ ≤ linFamAvg` and `δ' ≤ γ/C₄` one gets the averaged level-`|I_{d-1}|` box-norm power of `f` along
the datum's direction family at the enlarged support `symIcc ((4·Cne+1)·N)`. -/
def LinFamBoundLin (P : Polynomial ℤ) (D : IdxDatum) : Prop :=
  ∃ K4 : ℕ, 1 ≤ K4 ∧ ∃ C4 : ℝ, 1 ≤ C4 ∧
    ∀ (N M : ℕ) (f : ℤ → ℂ) (δ' γ : ℝ) (Cne : ℕ)
      (b : Fin (Fintype.card (D.I (P.natDegree - 1))) → Bool)
      (β : D.Idx P.natDegree → Fin (Fintype.card (D.I (P.natDegree - 1))) → ℤ),
      2 ≤ P.natDegree → 2 ≤ Fintype.card (D.I (P.natDegree - 1)) → 1 ≤ N → 2 ≤ M →
      0 < δ' → 0 < γ → γ ≤ 1 → 1 ≤ Cne →
      (∀ x : ℤ, ‖f x‖ ≤ 1) → SupportIn f N →
      (∀ a ∈ D.parBox P.natDegree (⌊δ' * (M : ℝ)⌋).toNat,
        ∀ i : Fin (Fintype.card (D.I (P.natDegree - 1))), ∀ y ∈ Finset.Icc 1 M,
          |petDir D P.natDegree P.leadingCoeff a i * (y : ℤ) + β a i|
            ≤ (Cne : ℤ) * (N : ℤ)) →
      1 ≤ (⌊δ' * (M : ℝ)⌋).toNat →
      γ ≤ linFamAvg D P.natDegree P.leadingCoeff N M (⌊δ' * (M : ℝ)⌋).toNat f b β →
      δ' ≤ γ / C4 →
      (γ / C4) ^ K4 ≤
        (((D.parBox P.natDegree (⌊δ' * (M : ℝ)⌋).toNat).card : ℕ) : ℝ)⁻¹ *
          ∑ a ∈ D.parBox P.natDegree (⌊δ' * (M : ℝ)⌋).toNat,
            Work.Peluse.boxNormPow (Fintype.card (D.I (P.natDegree - 1)))
              (fun i : Fin (Fintype.card (D.I (P.natDegree - 1))) =>
                Work.Peluse.arithIcc (petDir D P.natDegree P.leadingCoeff a i)
                  (⌊δ' * (M : ℝ)⌋).toNat)
              (Work.Peluse.symIcc ((4 * Cne + 1) * N)) f

/-- **The PET chapter in the shape the assembly needs** (see
`NOTES_UControl_peluseProp34.md` §9-§11): the window keeps the form of `Prop34` itself
(`A * δ' ≤ γ^K`); the conclusion displays the level as `γ^K / Cst₀` with `Cst₀` bounded by a constant
`Cst₁` produced **before** `A`; and — because the (two-scale) `Prop34` fixes its exponent `K` before
the scale constants — the exponent `K` produced for a given `A` is required to be **bounded** by a
`K₀` produced before `A` (which is faithful: Peluse's exponent is `≪_ℓ 1`). -/
def PetChapter5 (P : Polynomial ℤ) : Prop :=
  ∃ D : IdxDatum, 2 ≤ Fintype.card (D.I (P.natDegree - 1)) ∧
  ∃ (Cne₀ K₀ : ℕ) (Cst₁ : ℝ), 1 ≤ Cne₀ ∧ 2 ≤ K₀ ∧ 1 ≤ Cst₁ ∧
  ∀ A : ℝ, 1 ≤ A → ∃ K : ℕ, 2 ≤ K ∧ K ≤ K₀ ∧ ∃ Cst₀ : ℝ, 1 ≤ Cst₀ ∧ Cst₀ ≤ Cst₁ ∧
    ∃ Cne : ℕ, 1 ≤ Cne ∧ (Cne : ℝ) ≤ (Cne₀ : ℝ) * A ∧
    ∀ (N M : ℕ) (F : Fin (P.natDegree + 1) → ℤ → ℂ) (γ δ' : ℝ),
      2 ≤ P.natDegree → 1 ≤ N → 1 ≤ M →
      (N : ℝ) ≤ A * (M : ℝ) ^ P.natDegree →
      (M : ℝ) ^ P.natDegree ≤ A * γ⁻¹ * (N : ℝ) →
      0 < γ → γ ≤ 1 → 0 < δ' → A * δ' ≤ γ ^ K →
      2 ≤ (⌊δ' * (M : ℝ)⌋).toNat →
      (∀ i x, ‖F i x‖ ≤ 1) → (∀ i, SupportIn (F i) N) →
      γ ≤ ‖LambdaMD N M P F‖ →
      ∃ (b : Fin (Fintype.card (D.I (P.natDegree - 1))) → Bool)
        (β : D.Idx P.natDegree → Fin (Fintype.card (D.I (P.natDegree - 1))) → ℤ),
        (∀ a ∈ D.parBox P.natDegree (⌊δ' * (M : ℝ)⌋).toNat,
            ∀ i : Fin (Fintype.card (D.I (P.natDegree - 1))), ∀ y ∈ Finset.Icc 1 M,
              |petDir D P.natDegree P.leadingCoeff a i * (y : ℤ) + β a i|
                ≤ (Cne : ℤ) * (N : ℤ)) ∧
        γ ^ K ≤ Cst₀ * linFamAvg D P.natDegree P.leadingCoeff N M (⌊δ' * (M : ℝ)⌋).toNat
          (F ⟨P.natDegree, Nat.lt_succ_self _⟩) b β

end

end Work.Peluse.UControl
