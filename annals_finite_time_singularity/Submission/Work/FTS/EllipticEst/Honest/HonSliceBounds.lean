import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.sliceLimitLeftExists
import Submission.Work.FTS.EllipticEst.absLeMulOfDerivBoundOpen
import Submission.Work.FTS.EllipticEst.Honest.slice_bdd_of_sq_mul_sEta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

theorem HonSliceBounds (u : ℝ → ℝ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (hcont : ContinuousOn u (Set.Icc 0 (Real.pi / 2)))
    (h0 : u 0 = 0) (h1 : u (Real.pi / 2) = 0)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ) :
    ∃ M K : ℝ, 0 ≤ M ∧ 0 ≤ K ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv u θ| ≤ M) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |u θ| ≤ M * θ ∧ |u θ| ≤ M * (Real.pi / 2 - θ)) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |u θ| ≤ K * Real.cos θ) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |u θ / Real.cos θ| ≤ K) := by
  -- The weighted `L²`-bound on `u''` (weight `σ = sin(2θ)^{-η} ≥ 1`) already gives a
  -- constant `C` bounding both `u` and `u'` on the open interval.
  obtain ⟨C, hC0, hC⟩ :=
    Work.FTS.EllipticEst.Honest.slice_bdd_of_sq_mul_sEta (hsm 2) hint
  have hdiff : DifferentiableOn ℝ u (Set.Ioo 0 (Real.pi / 2)) :=
    (hsm 1).differentiableOn (by norm_num)
  -- The mean-value bound at the two endpoints: `|u θ| ≤ C·θ` and `|u θ| ≤ C·(π/2 - θ)`.
  have hmvt := Work.FTS.EllipticEst.absLeMulOfDerivBoundOpen hdiff hcont h0 h1
    (fun x hx => (hC x hx).2)
  have hmvtL : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |u θ| ≤ C * θ := fun θ hθ => by
    have := hmvt.1 θ hθ; rwa [mul_comm] at this
  have hmvtR : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |u θ| ≤ C * (Real.pi / 2 - θ) :=
    fun θ hθ => by have := hmvt.2 θ hθ; rwa [mul_comm] at this
  -- Jordan's inequality for `sin` on `[0, π/2]`, transported to `cos` via `cos θ = sin(π/2-θ)`.
  have hcosine : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      Real.pi / 2 - θ ≤ (Real.pi / 2) * Real.cos θ := by
    intro θ hθ
    have ht0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
    have ht1 : Real.pi / 2 - θ ≤ Real.pi / 2 := by linarith [hθ.1]
    have hj := Real.mul_le_sin ht0 ht1
    rw [Real.sin_pi_div_two_sub] at hj
    have hj' := mul_le_mul_of_nonneg_left hj (show (0 : ℝ) ≤ Real.pi / 2 by positivity)
    have hc : (Real.pi / 2) * (2 / Real.pi * (Real.pi / 2 - θ)) = Real.pi / 2 - θ := by
      field_simp
    rwa [hc] at hj'
  refine ⟨C, C * (Real.pi / 2), hC0, mul_nonneg hC0 (by positivity), ?_, ?_, ?_, ?_⟩
  · intro θ hθ; exact (hC θ hθ).2
  · intro θ hθ
    exact ⟨hmvtL θ ⟨hθ.1.le, hθ.2.le⟩, hmvtR θ ⟨hθ.1.le, hθ.2.le⟩⟩
  · intro θ hθ
    have hθc : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hθ.1.le, hθ.2.le⟩
    calc |u θ| ≤ C * (Real.pi / 2 - θ) := hmvtR θ hθc
      _ ≤ C * ((Real.pi / 2) * Real.cos θ) := mul_le_mul_of_nonneg_left (hcosine θ hθc) hC0
      _ = C * (Real.pi / 2) * Real.cos θ := by ring
  · intro θ hθ
    have hθc : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hθ.1.le, hθ.2.le⟩
    have hcospos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    rw [abs_div, abs_of_pos hcospos]
    calc |u θ| / Real.cos θ ≤ (C * (Real.pi / 2 - θ)) / Real.cos θ :=
          div_le_div_of_nonneg_right (hmvtR θ hθc) hcospos.le
      _ ≤ (C * ((Real.pi / 2) * Real.cos θ)) / Real.cos θ :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hcosine θ hθc) hC0) hcospos.le
      _ = C * (Real.pi / 2) := by
          rw [div_eq_iff (ne_of_gt hcospos)]; ring

end Work.FTS.EllipticEst.Honest
