import Mathlib
import Submission.Work.KMTAreas.A7.mStarF_plateau
import Submission.Work.KMTAreas.A7.periodize_mStarF_one

namespace Work.KMTAreas.A7

/-- `mStargF d u = η_{≤ -2du}` agrees with the first tensor factor `m_* = η_{≤ -2(d u)}`
evaluated at the integer scale `d * u`: the two defining exponents coincide. -/
private lemma mStargF_eq_mStarF (d u : ℕ) :
    Work.KMTAreas.A7.mStargF d u = Work.KMTAreas.A7.mStarF (d * u) := by
  have he : (-((d : ℤ) * 2 * (u : ℤ))) = -(2 * ((d * u : ℕ) : ℤ)) := by
    push_cast
    ring
  funext x
  simp only [Work.KMTAreas.A7.mStargF, Work.KMTAreas.A7.mStarF,
    Work.Analysis.IonescuWainger.etaCut, he]

theorem mStargF_band (d u : ℕ) (hdu : 1 ≤ d * u) :
    Work.KMTAreas.A7.mStargF d u = Work.KMTAreas.A7.mStarF (d * u) ∧
      (∀ x : ℝ, |x| ≤ (2 : ℝ) ^ (-(2 * ((d * u : ℕ) : ℤ)) - 1) → Work.KMTAreas.A7.mStargF d u x = 1) ∧
      (∀ x : ℝ, (2 : ℝ) ^ (-(2 * ((d * u : ℕ) : ℤ))) ≤ |x| → Work.KMTAreas.A7.mStargF d u x = 0) ∧
      (∀ θ : Work.Analysis.IonescuWainger.Circle,
        θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0
            ((2 : ℝ) ^ (-(2 * ((d * u : ℕ) : ℤ)) - 1)) →
          Work.Analysis.IonescuWainger.periodize (Work.KMTAreas.A7.mStargF d u) θ = 1) ∧
      (∀ (φ : ℝ → ℂ) (θ : Work.Analysis.IonescuWainger.Circle),
        Work.Analysis.IonescuWainger.periodize φ θ ≠ 0 →
          (∀ ξ : ℝ, φ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(2 * ((d * u : ℕ) : ℤ)) - 1)) →
          Work.Analysis.IonescuWainger.periodize (Work.KMTAreas.A7.mStargF d u) θ = 1) := by
  have heq := mStargF_eq_mStarF d u
  have hplat := Work.KMTAreas.A7.mStarF_plateau (d * u)
  have hper := Work.KMTAreas.A7.periodize_mStarF_one (d * u) hdu
  refine ⟨heq, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [heq]
    exact hplat.1 x hx
  · intro x hx
    rw [heq]
    exact hplat.2 x hx
  · intro θ hθ
    rw [heq]
    exact hper.1 θ hθ
  · intro φ θ hφ hsupp
    rw [heq]
    exact hper.2 φ θ hφ hsupp

end Work.KMTAreas.A7
