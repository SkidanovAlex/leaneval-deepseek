import Mathlib
import Submission.Commons.Geometry.Ulam.even_profile_perturbation_strict_of_tau_core

namespace Commons.Geometry.Ulam

open MeasureTheory
open scoped ContDiff Pointwise RealInnerProductSpace

set_option autoImplicit false

lemma exists_even_floating_profile_data_strict_v4 (n : ℕ) (hn : 2 ≤ n) :
    ∃ h x y f : ℝ → ℝ,
      Function.support h ⊆ Set.Icc (1 - 2 * (1 / 10 : ℝ)) (1 - (1 / 10 : ℝ)) ∧
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
  obtain ⟨h, x, y, f, hh_supp, hh_ne, hh_smooth, hf_supp, hf_smooth, hf_strict,
    hf_cont, hf_left, hf_right, hf_pos, hxy, hne, hI, hJ⟩ :=
    even_profile_perturbation_strict_of_tau_core n hn (1 / 10 : ℝ) (by norm_num) (by norm_num)
  refine ⟨h, x, y, f, ?_, hh_ne, hh_smooth, hf_supp, hf_smooth, hf_strict,
    hf_cont, hf_left, hf_right, hf_pos, hxy, hne, hI, hJ⟩
  simpa using hh_supp

end Commons.Geometry.Ulam
