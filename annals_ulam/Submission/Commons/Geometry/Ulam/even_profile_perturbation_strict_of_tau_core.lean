import Mathlib
import Submission.Commons.Geometry.Ulam.even_profile_perturbation_strict_of_tau_core_heavy_core

namespace Commons.Geometry.Ulam

open MeasureTheory
open scoped ContDiff Pointwise RealInnerProductSpace

set_option autoImplicit false

lemma even_profile_perturbation_strict_of_tau_core (n : ℕ) (hn : 2 ≤ n) (τ : ℝ)
    (hτ0 : 0 < τ) (hτsmall : 2 * τ < 1) :
    ∃ h x y f : ℝ → ℝ,
      Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ) ∧
      (∃ s : ℝ, 0 < s ∧ h s ≠ 0) ∧
      ContDiffOn ℝ ∞ h Set.univ ∧
      Function.support f ⊆ Set.Icc (-1 : ℝ) 1 ∧
      ContDiffOn ℝ ∞ f (Set.Ioo (-1 : ℝ) 1) ∧
      StrictConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f ∧
      ContinuousOn f (Set.Icc (-1 : ℝ) 1) ∧
      f (-1) = 0 ∧ f 1 = 0 ∧
      (∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t) ∧
      (∀ s : ℝ, 0 < s →
        0 < x s ∧ 0 < y s ∧
        (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
        (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2) ∧
      (∃ t ∈ Set.Icc (-1 : ℝ) 1, f t ≠ f (-t)) ∧
      (∀ s : ℝ, 0 < s →
        (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ n) =
          (∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
            ((1 - t ^ 2) - (s * t) ^ 2) ^ n)) ∧
      (∀ s : ℝ, 0 < s →
        (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + deriv h s)) = 0) := by
  exact even_profile_perturbation_strict_of_tau_core_heavy_core n hn τ hτ0 hτsmall

end Commons.Geometry.Ulam
