import Mathlib
import Submission.Work.Smooth.JordanSeparation.Defs

namespace Work.Smooth.JordanSeparation

open Set

/-- Every real number is congruent modulo `2π` to a point of the fundamental interval
`[0, 2π]`. -/
private lemma exists_int_sub_mem_Icc (t : ℝ) :
    ∃ k : ℤ, t - (k : ℝ) * (2 * Real.pi) ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨⌊t / (2 * Real.pi)⌋, ?_⟩
  have h : t - (⌊t / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi)
      = Int.fract (t / (2 * Real.pi)) * (2 * Real.pi) := by
    rw [Int.fract]; field_simp
  rw [Set.mem_Icc, h]
  exact ⟨mul_nonneg (Int.fract_nonneg _) (le_of_lt hpos),
    by simpa using (mul_lt_mul_of_pos_right (Int.fract_lt_one _) hpos).le⟩

/-- The derivative of a `2π`-periodic `C¹` curve is `2π`-periodic. -/
private lemma periodic_deriv (c : Work.Smooth.Jordan.SmoothPlaneCurve) :
    Function.Periodic (deriv c.γ) (2 * Real.pi) := by
  intro t
  have hfun : (fun s : ℝ => c.γ (s + 2 * Real.pi)) = c.γ :=
    funext fun s => c.periodic_apply s
  have hh : deriv (fun s : ℝ => c.γ (s + 2 * Real.pi)) t
      = deriv c.γ (t + 2 * Real.pi) := deriv_comp_add_const c.γ (2 * Real.pi) t
  rw [← hh, hfun]

/-- **The norm of the derivative of an immersed closed curve is bounded above and below by
positive constants.**  Both bounds come from compactness of one period `[0, 2π]`: the derivative
is continuous there, so `‖γ'‖` is bounded above by some `M ≥ 0`; it never vanishes there
(the curve is an immersion), so the continuous function `‖γ'‖` attains a strictly positive
minimum `m` on that compact interval.  `2π`-periodicity of `γ'` transports both bounds to all
of `ℝ`. -/
theorem deriv_global_norm_bounds (c : Work.Smooth.Jordan.SmoothPlaneCurve)
    (h : c.IsImmersion) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ (∀ t : ℝ, m ≤ ‖deriv c.γ t‖) ∧
      (∀ t : ℝ, ‖deriv c.γ t‖ ≤ M) := by
  have hT : (0 : ℝ) < 2 * Real.pi := by positivity
  have hper : Function.Periodic (deriv c.γ) (2 * Real.pi) := periodic_deriv c
  -- An upper bound for `‖γ'‖` on one period.
  obtain ⟨M0, hM0⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * Real.pi))
    |>.exists_bound_of_continuousOn c.continuous_deriv.continuousOn
  -- The minimum of `‖γ'‖` on one period, attained because the interval is compact.
  obtain ⟨t0, _ht0, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * Real.pi))
    |>.exists_isMinOn ⟨0, ⟨le_refl 0, hT.le⟩⟩ (c.continuous_deriv.norm.continuousOn)
  have hm_pos : 0 < ‖deriv c.γ t0‖ := norm_pos_iff.mpr (h t0)
  refine ⟨‖deriv c.γ t0‖, max M0 1, hm_pos, lt_max_iff.mpr (Or.inr zero_lt_one), ?_, ?_⟩
  · intro t
    obtain ⟨k, hk⟩ := exists_int_sub_mem_Icc t
    have heq : deriv c.γ t = deriv c.γ (t - (k : ℝ) * (2 * Real.pi)) := by
      have hh := hper.int_mul k (t - (k : ℝ) * (2 * Real.pi))
      rwa [show t - (k : ℝ) * (2 * Real.pi) + (k : ℝ) * (2 * Real.pi) = t by ring] at hh
    rw [heq]
    exact hmin hk
  · intro t
    obtain ⟨k, hk⟩ := exists_int_sub_mem_Icc t
    have heq : deriv c.γ t = deriv c.γ (t - (k : ℝ) * (2 * Real.pi)) := by
      have hh := hper.int_mul k (t - (k : ℝ) * (2 * Real.pi))
      rwa [show t - (k : ℝ) * (2 * Real.pi) + (k : ℝ) * (2 * Real.pi) = t by ring] at hh
    rw [heq]
    exact le_trans (hM0 _ hk) (le_max_left _ _)

end Work.Smooth.JordanSeparation
