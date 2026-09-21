import Mathlib
import Submission.Commons.Geometry.Ulam.even_profile_perturbation_from_smooth_bump_core

namespace Commons.Geometry.Ulam

lemma even_profile_perturbation_from_smooth_bump (n : ℕ) (hn : 2 ≤ n) {c δ : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) (hδ0 : 0 < δ) (hδsmall : 2 * δ < c)
    (h : ℝ → ℝ)
    (hh_cont : ContDiffOn ℝ (⊤ : ℕ∞) h Set.univ)
    (hh_supp : Function.support h ⊆ Set.Icc (c - 2 * δ) (c - δ))
    (hh_ne : ∃ s : ℝ, 0 < s ∧ h s ≠ 0)
    (hh_flat : ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, c - 2 * δ ≤ s → s < c - 2 * δ + η → h s = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ x y f : ℝ → ℝ,
      Function.support f ⊆ Set.Icc (-1 : ℝ) 1 ∧
      ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioo (-1 : ℝ) 1) ∧
      StrictConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f ∧
      ContinuousOn f (Set.Icc (-1 : ℝ) 1) ∧
      f (-1) = 0 ∧ f 1 = 0 ∧
      (∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t) ∧
      (∀ s : ℝ, 0 < s →
        0 < x s ∧ 0 < y s ∧
        (f (y s)) ^ 2 = (s * y s + (ε • h) s) ^ 2 ∧
        (f (-x s)) ^ 2 = (s * (-x s) + (ε • h) s) ^ 2) ∧
      (∃ t ∈ Set.Icc (-1 : ℝ) 1, f t ≠ f (-t)) ∧
      (∀ s : ℝ, 0 < s →
        (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + (ε • h) s) ^ 2) ^ n) =
          (∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
            ((1 - t ^ 2) - (s * t) ^ 2) ^ n)) ∧
      (∀ s : ℝ, 0 < s →
        (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + (ε • h) s) ^ 2) ^ (n - 1) * (t + deriv (ε • h) s)) = 0) := by
  exact even_profile_perturbation_from_smooth_bump_core n hn hc0 hc1 hδ0 hδsmall h
    hh_cont hh_supp hh_ne hh_flat

end Commons.Geometry.Ulam
