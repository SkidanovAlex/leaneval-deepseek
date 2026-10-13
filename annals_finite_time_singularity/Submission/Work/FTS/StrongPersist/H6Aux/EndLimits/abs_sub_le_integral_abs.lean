import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux.EndLimits

theorem abs_sub_le_integral_abs {F F' : ℝ → ℝ} {a b θ₁ θ₂ : ℝ}
    (hderiv : ∀ θ ∈ Set.Ioo a b, HasDerivAt F (F' θ) θ)
    (hint : IntervalIntegrable F' MeasureTheory.volume a b)
    (ha : a < θ₁) (h₁ : θ₁ ≤ θ₂) (h₂ : θ₂ < b) :
    |F θ₂ - F θ₁| ≤ ∫ x in a..b, |F' x| := by
  have hab : a ≤ b := le_of_lt (lt_trans ha (lt_of_le_of_lt h₁ h₂))
  have hsub : Set.Icc θ₁ θ₂ ⊆ Set.Ioo a b := fun y hy =>
    ⟨lt_of_lt_of_le ha hy.1, lt_of_le_of_lt hy.2 h₂⟩
  have hcont : ContinuousOn F (Set.Icc θ₁ θ₂) := fun y hy =>
    (hderiv y (hsub hy)).continuousAt.continuousWithinAt
  have hInt : IntervalIntegrable F' MeasureTheory.volume θ₁ θ₂ :=
    hint.mono_set (by
      rw [Set.uIcc_of_le h₁, Set.uIcc_of_le hab]
      exact fun y hy => ⟨le_trans (le_of_lt ha) hy.1, le_trans hy.2 (le_of_lt h₂)⟩)
  have hftc : ∫ x in θ₁..θ₂, F' x = F θ₂ - F θ₁ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h₁ hcont
      (fun y hy => hderiv y (hsub ⟨le_of_lt hy.1, le_of_lt hy.2⟩)) hInt
  calc |F θ₂ - F θ₁| = |∫ x in θ₁..θ₂, F' x| := by rw [hftc]
    _ ≤ ∫ x in θ₁..θ₂, |F' x| := intervalIntegral.abs_integral_le_integral_abs h₁
    _ ≤ ∫ x in a..b, |F' x| :=
        intervalIntegral.integral_mono_interval (le_of_lt ha) h₁ (le_of_lt h₂)
          (Filter.Eventually.of_forall (fun x => abs_nonneg _)) hint.abs

end Work.FTS.StrongPersist.H6Aux.EndLimits
