import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZDataMup.swCoreDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.H9

open _root_.SSGRoute

/-- The correction datum of the recursion depends on its group argument only through the functions
`g` and `z`: for fixed `Q` and `A` the three cases of its defining `if`-clause are decided by
`Q, A` alone, so conjugating the argument merely conjugates `g` and `z`. -/
theorem correctionDatum_conj_inv {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω]
    [Algebra k Ω] (K : IntermediateField k Ω) (g z : (Ω ≃ₐ[k] Ω) → ZMod p)
    (Q A : ValuationSubring Ω) {τ σ : Ω ≃ₐ[k] Ω}
    (hg : g (τ * σ * τ⁻¹) = g σ) (hz : z (τ * σ * τ⁻¹) = z σ) :
    Work.SSGRoute.ZDataMup.correctionDatum K g z Q A (τ * σ * τ⁻¹)
      = Work.SSGRoute.ZDataMup.correctionDatum K g z Q A σ := by
  unfold Work.SSGRoute.ZDataMup.correctionDatum
  by_cases h1 : Work.SSGRoute.gesKConj K Q A
  · rw [if_pos h1, if_pos h1, hg]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : SSGRoute.IsConjPlace k Q A
    · rw [if_pos h2, if_pos h2, hg, hz]
    · rw [if_neg h2, if_neg h2]

/-- The history datum `histDatum K y f A` is a finite sum of correction data, each of which is
invariant under conjugation by `τ` as soon as the two ingredient functions are.  The global datum
`½y` inherits this from `hgy`, and the level-`j` local datum from `hz`. -/
theorem swHistDatum_conj_inv {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    {n : ℕ} (f : Fin n → (ValuationSubring Ω × ((Ω ≃ₐ[k] Ω) → ZMod p)))
    (A : ValuationSubring Ω) (τ σ : Ω ≃ₐ[k] Ω) (hτ : τ ∈ K.fixingSubgroup)
    (hσ : σ ∈ K.fixingSubgroup)
    (hgy : ∀ s ∈ K.fixingSubgroup, y (τ * s * τ⁻¹) = y s)
    (hz : ∀ j, ∀ s ∈ K.fixingSubgroup, (f j).2 (τ * s * τ⁻¹) = (f j).2 s) :
    Work.SSGRoute.ZDataMup.histDatum K y f A (τ * σ * τ⁻¹)
      = Work.SSGRoute.ZDataMup.histDatum K y f A σ := by
  have _ := hτ
  unfold Work.SSGRoute.ZDataMup.histDatum
  apply Finset.sum_congr rfl
  intro j _
  exact correctionDatum_conj_inv K (fun s => (2 : ZMod p)⁻¹ * y s) ((f j).2) ((f j).1) A
    (by simp only [hgy σ hσ]) (by simp only [hz j σ hσ])

end Work.SSGRoute.H9
