import Mathlib
import Submission.Work.Smooth.JordanSeparation.Defs

namespace Work.Smooth.JordanSeparation

/-- The derivative of a `2π`-periodic function is again `2π`-periodic. -/
private theorem periodic_deriv {v : ℝ → ℂ} (hper : Function.Periodic v (2 * Real.pi)) :
    Function.Periodic (deriv v) (2 * Real.pi) := by
  intro t
  have hfun : (fun s : ℝ => v (s + 2 * Real.pi)) = v := funext fun s => hper s
  rw [← deriv_comp_add_const v (2 * Real.pi) t, hfun]

/-- A `C¹` `2π`-periodic function `ℝ → ℂ` has a globally bounded derivative: the derivative is
continuous and periodic, so its range is the image of the compact interval `[0, 2π]`. -/
theorem exists_bound_deriv_of_periodic_contDiff {v : ℝ → ℂ}
    (hper : Function.Periodic v (2 * Real.pi)) (hcd : ContDiff ℝ 1 v) :
    ∃ M : ℝ, ∀ t : ℝ, ‖deriv v t‖ ≤ M := by
  have hT : (0 : ℝ) < 2 * Real.pi := by positivity
  have hdper : Function.Periodic (deriv v) (2 * Real.pi) := periodic_deriv hper
  have hcont : Continuous (deriv v) := hcd.continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨C, fun t => ?_⟩
  have ht'0 : 0 ≤ t - (⌊t / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) := by
    have h1 := (le_div_iff₀ hT).mp (Int.floor_le (t / (2 * Real.pi)))
    linarith
  have ht'T : t - (⌊t / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) ≤ 2 * Real.pi := by
    have h1 := (div_lt_iff₀ hT).mp (Int.lt_floor_add_one (t / (2 * Real.pi)))
    linarith
  have hkey : deriv v t = deriv v (t - (⌊t / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi)) := by
    have h := hdper.int_mul ⌊t / (2 * Real.pi)⌋
      (t - (⌊t / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi))
    rw [show t - (⌊t / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi)
          + (⌊t / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) = t from by ring] at h
    exact h
  rw [hkey]
  exact hC _ ⟨ht'0, ht'T⟩

theorem exists_lipschitz_of_periodic_contDiff {v : ℝ → ℂ}
    (hper : Function.Periodic v (2 * Real.pi)) (hcd : ContDiff ℝ 1 v) :
    ∃ L : ℝ, 0 < L ∧ Work.Smooth.JordanSeparation.IsLipschitzField L v := by
  obtain ⟨C, hC⟩ := exists_bound_deriv_of_periodic_contDiff hper hcd
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right C 1), ?_⟩
  intro t t'
  have hbound : ∀ x ∈ (Set.univ : Set ℝ), ‖deriv v x‖ ≤ max C 1 :=
    fun x _ => le_trans (hC x) (le_max_left C 1)
  have hdiff : ∀ x ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ v x :=
    fun x _ => hcd.differentiable_one.differentiableAt
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := v) (s := Set.univ)
    hdiff hbound convex_univ (Set.mem_univ t') (Set.mem_univ t)
  rw [Real.norm_eq_abs] at h
  simpa [IsLipschitzField, abs_sub_comm] using h

end Work.Smooth.JordanSeparation
