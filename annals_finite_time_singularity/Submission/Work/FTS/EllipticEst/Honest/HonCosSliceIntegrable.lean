import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Real

namespace Work.FTS.EllipticEst.Honest

/-- The slice `θ ↦ (u θ / cos θ)²` is integrable on `(0, π/2)` for a continuous `u` on
`[0, π/2]` with `u (π/2) = 0` and a bounded derivative.

Indeed, the mean value theorem gives `|u θ| ≤ M (π/2 - θ)` and Jordan's inequality gives
`cos θ ≥ (2/π) (π/2 - θ)`, so the quotient `u θ / cos θ` is bounded by `M π / 2` on the whole
interval; a bounded measurable function is integrable on a set of finite measure. -/
theorem HonCosSliceIntegrable {u : ℝ → ℝ} {M : ℝ}
    (hcont : ContinuousOn u (Set.Icc (0:ℝ) (Real.pi / 2)))
    (h1 : u (Real.pi / 2) = 0)
    (hderiv : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), HasDerivAt u (deriv u θ) θ)
    (hM : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), |deriv u θ| ≤ M) :
    MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2)
      (Set.Ioo (0:ℝ) (Real.pi / 2)) := by
  -- `M` is nonnegative, since `(0, π/2)` is nonempty.
  have hMnn : 0 ≤ M := by
    have hmem : Real.pi / 4 ∈ Set.Ioo (0:ℝ) (Real.pi / 2) :=
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    exact (abs_nonneg (deriv u (Real.pi / 4))).trans (hM (Real.pi / 4) hmem)
  -- Mean value theorem: `|u θ| ≤ M * (π/2 - θ)` on the interval.
  have hmvt : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), |u θ| ≤ M * (Real.pi / 2 - θ) := by
    intro θ hθ
    obtain ⟨c, hc, hceq⟩ := exists_deriv_eq_slope u hθ.2
      (hcont.mono fun x hx => ⟨le_trans hθ.1.le hx.1, hx.2⟩)
      (fun x hx => (hderiv x ⟨lt_trans hθ.1 hx.1, hx.2⟩).differentiableAt.differentiableWithinAt)
    have hcx : c ∈ Set.Ioo (0:ℝ) (Real.pi / 2) := ⟨lt_trans hθ.1 hc.1, hc.2⟩
    have hd : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
    have hdc : deriv u c = (-u θ) / (Real.pi / 2 - θ) := by
      rw [hceq, h1, zero_sub]
    have heq : |u θ| = |deriv u c| * (Real.pi / 2 - θ) := by
      rw [hdc, abs_div, abs_neg, abs_of_pos hd, div_mul_cancel₀ _ (ne_of_gt hd)]
    calc |u θ| = |deriv u c| * (Real.pi / 2 - θ) := heq
      _ ≤ M * (Real.pi / 2 - θ) := mul_le_mul_of_nonneg_right (hM c hcx) hd.le
  -- Jordan's inequality: `(2/π) * (π/2 - θ) ≤ cos θ`.
  have hcos : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      (2 / Real.pi) * (Real.pi / 2 - θ) ≤ Real.cos θ := by
    intro θ hθ
    have hx0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
    have hx1 : Real.pi / 2 - θ ≤ Real.pi / 2 := by linarith [hθ.1]
    have h := Real.mul_le_sin hx0 hx1
    rwa [Real.sin_pi_div_two_sub] at h
  -- Pointwise bound on the integrand.
  have hpt : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      (u θ / Real.cos θ) ^ 2 ≤ (M * Real.pi / 2) ^ 2 := by
    intro θ hθ
    have hd : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
    have hcosθ := hcos θ hθ
    have hcpos : 0 < Real.cos θ := lt_of_lt_of_le (mul_pos (by positivity) hd) hcosθ
    have hMeq : (M * Real.pi / 2) * (2 / Real.pi) = M := by field_simp
    have h2 : M * (Real.pi / 2 - θ) ≤ (M * Real.pi / 2) * Real.cos θ := by
      have hstep : M * (Real.pi / 2 - θ)
          = (M * Real.pi / 2) * ((2 / Real.pi) * (Real.pi / 2 - θ)) := by
        rw [← mul_assoc, hMeq]
      exact hstep.le.trans (mul_le_mul_of_nonneg_left hcosθ
        (div_nonneg (mul_nonneg hMnn Real.pi_pos.le) (by norm_num)))
    have hdiv : |u θ / Real.cos θ| ≤ M * Real.pi / 2 := by
      rw [abs_div, abs_of_pos hcpos, div_le_iff₀ hcpos]
      exact (hmvt θ hθ).trans h2
    have h3 := abs_le.mp hdiv
    exact sq_le_sq' h3.1 h3.2
  -- Continuity (hence measurability) of the integrand on the open interval.
  have hcontF : ContinuousOn (fun θ => (u θ / Real.cos θ) ^ 2)
      (Set.Ioo (0:ℝ) (Real.pi / 2)) := by
    have hdivC : ContinuousOn (fun θ => u θ / Real.cos θ) (Set.Ioo (0:ℝ) (Real.pi / 2)) :=
      ContinuousOn.div (hcont.mono fun x hx => ⟨hx.1.le, hx.2.le⟩) Real.continuous_cos.continuousOn
        (fun x hx => ne_of_gt (Real.cos_pos_of_mem_Ioo
          ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2]⟩))
    exact (hdivC.mul hdivC).congr (fun θ _ => by simp [pow_two])
  -- A bounded, measurable function on a finite measure set is integrable.
  refine MeasureTheory.IntegrableOn.of_bound (μ := volume) (s := Set.Ioo (0:ℝ) (Real.pi / 2))
    measure_Ioo_lt_top ?_ ((M * Real.pi / 2) ^ 2) ?_
  · exact hcontF.aestronglyMeasurable measurableSet_Ioo
  · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt θ hθ

end Work.FTS.EllipticEst.Honest
