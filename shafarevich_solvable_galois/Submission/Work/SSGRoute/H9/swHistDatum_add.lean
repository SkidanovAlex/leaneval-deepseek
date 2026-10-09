import Mathlib
import Submission.Work.SSGRoute.ZDataMup.swCoreDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.H9

open _root_.SSGRoute

theorem swHistDatum_add {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    {n : ℕ} (f : Fin n → (ValuationSubring Ω × ((Ω ≃ₐ[k] Ω) → ZMod p)))
    (hz : ∀ j, ∀ x ∈ K.fixingSubgroup, ∀ z ∈ K.fixingSubgroup,
      (f j).2 (x * z) = (f j).2 x + (f j).2 z)
    (A : ValuationSubring Ω) :
    ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ z ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
        Work.SSGRoute.ZDataMup.histDatum K y f A (x * z)
          = Work.SSGRoute.ZDataMup.histDatum K y f A x
            + Work.SSGRoute.ZDataMup.histDatum K y f A z := by
  intro x hx z hzA
  -- the global datum `½y` is additive on `K.fixingSubgroup`, like `y`
  have hg : ∀ a ∈ K.fixingSubgroup, ∀ b ∈ K.fixingSubgroup,
      (fun σ => (2 : ZMod p)⁻¹ * y σ) (a * b)
        = (fun σ => (2 : ZMod p)⁻¹ * y σ) a + (fun σ => (2 : ZMod p)⁻¹ * y σ) b := by
    intro a ha b hb
    simp only
    rw [hy a ha b hb]
    ring
  simp only [Work.SSGRoute.ZDataMup.histDatum]
  refine (Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) =>
    Work.SSGRoute.ZDataMup.correctionDatum_add K (fun σ => (2 : ZMod p)⁻¹ * y σ)
      (f j).2 (f j).1 A hg (hz j) x hx z hzA)).trans ?_
  exact Finset.sum_add_distrib

end Work.SSGRoute.H9
