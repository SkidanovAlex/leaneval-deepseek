import Mathlib
import Submission.Work.ZeroDensity.Ingham.CritCommons

namespace Work.ZeroDensity.Ingham

/-- `‖ζ(1/2 + iτ)‖ ≤ C (3+|τ|)^4` for all real `τ`, with an absolute constant `C > 0`.
For `|τ| ≥ 1` this is `Commons.NumberTheory.Zeta.zeta_strip_polyGrowth` (`-1 ≤ σ ≤ 3`, degree 4).
For `|τ| ≤ 2` use continuity of `t ↦ ζ(1/2 + i t)` on the compact set `[-3,3]` (which avoids the
pole `1`), e.g. `IsCompact.exists_bound_of_continuousOn`; combine the two cases (taking
`C = max C₀ (M/81)`). -/
theorem zeta_halfLine_poly_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ,
      ‖riemannZeta ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ C * (3 + |τ|) ^ 4 := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Commons.NumberTheory.Zeta.zeta_strip_polyGrowth
  -- Continuity of `t ↦ ζ(1/2 + i t)` on the compact segment `[-3,3]`: the segment avoids the pole
  -- at `1`, where `ζ` is analytic (and in particular continuous).
  have hcont : ContinuousOn (fun t : ℝ => riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I))
      (Set.Icc (-3 : ℝ) 3) := by
    intro t _
    have hne : ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre
    have hf : ContinuousAt (fun t : ℝ => ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) t := by fun_prop
    exact ContinuousAt.continuousWithinAt (ContinuousAt.comp
      (f := fun t : ℝ => ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) (g := riemannZeta)
      (differentiableAt_riemannZeta hne).continuousAt hf)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C₀ (max M 0 / 81), lt_of_lt_of_le hC₀pos (le_max_left _ _), ?_⟩
  intro τ
  rcases le_or_gt 1 |τ| with h1 | h1
  · -- `|τ| ≥ 1`: the strip growth bound, evaluated at `σ = 1/2`.
    have hb := hC₀ (1 / 2) τ (by norm_num) (by norm_num) h1
    have hcast : ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I) = (((1 / 2 : ℝ) : ℂ) + Complex.I * (τ : ℂ)) := by
      rw [mul_comm]; norm_num
    rw [hcast]
    calc ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + Complex.I * (τ : ℂ))‖ ≤ C₀ * (|τ| + 3) ^ 4 := hb
      _ = C₀ * (3 + |τ|) ^ 4 := by rw [add_comm]
      _ ≤ max C₀ (max M 0 / 81) * (3 + |τ|) ^ 4 := by
          apply mul_le_mul_of_nonneg_right (le_max_left _ _)
          positivity
  · -- `|τ| ≤ 1`: the compactness bound, using `(3+|τ|)^4 ≥ 81`.
    have hτmem : τ ∈ Set.Icc (-3 : ℝ) 3 := by
      constructor
      · have := neg_abs_le τ; linarith
      · have := le_abs_self τ; linarith
    have hb := hM τ hτmem
    have hMle : M ≤ (max M 0 / 81) * (3 + |τ|) ^ 4 := by
      have hpow : (81 : ℝ) ≤ (3 + |τ|) ^ 4 := by
        have h3 : (3 : ℝ) ≤ 3 + |τ| := by linarith [abs_nonneg τ]
        have h4 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) h3 4
        norm_num at h4
        exact h4
      have h2' : (max M 0 / 81) * 81 ≤ (max M 0 / 81) * (3 + |τ|) ^ 4 :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      have h1' : (max M 0 / 81) * 81 = max M 0 := by ring
      linarith [le_max_left M (0 : ℝ)]
    calc ‖riemannZeta ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ M := hb
      _ ≤ (max M 0 / 81) * (3 + |τ|) ^ 4 := hMle
      _ ≤ max C₀ (max M 0 / 81) * (3 + |τ|) ^ 4 :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end Work.ZeroDensity.Ingham
