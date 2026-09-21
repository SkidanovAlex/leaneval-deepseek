import Submission.Work.OddRadon.RadonInversion

/-!
# Injectivity of the odd-dimensional profile transform (`Work.OddRadon`, part 3e)
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace Pointwise Interval Topology

namespace Work.OddRadon

/-- **Injectivity of the odd-dimensional profile transform on even `C¹` profiles.**  If two even
profiles of class `C¹` on `[-1,1]` have the same spherical Radon transform on the whole
equatorial family `c ∈ (0,1)`, they agree on `(0,1)`. -/
theorem radonProfile_injective (n : ℕ) (hn : 1 ≤ n) {γ₁ γ₂ : ℝ → ℝ}
    (h₁ : ContDiffOn ℝ 1 γ₁ (Set.Icc (-1) 1)) (h₂ : ContDiffOn ℝ 1 γ₂ (Set.Icc (-1) 1))
    (he₁ : ∀ t, γ₁ (-t) = γ₁ t) (he₂ : ∀ t, γ₂ (-t) = γ₂ t)
    (h : Set.EqOn (radonProfile (2 * n + 1) γ₁) (radonProfile (2 * n + 1) γ₂)
      (Set.Ioo 0 1)) :
    Set.EqOn γ₁ γ₂ (Set.Ioo 0 1) := by
  intro u hu
  obtain ⟨c₀, huc₀, hc₀1⟩ := exists_between hu.2
  exact radonProfile_eqOn_of_eqOn n hn h₁ h₂ he₁ he₂ ⟨lt_trans hu.1 huc₀, hc₀1⟩
    (h.mono (Set.Ioo_subset_Ioo_right hc₀1.le)) ⟨hu.1, huc₀⟩

end Work.OddRadon
