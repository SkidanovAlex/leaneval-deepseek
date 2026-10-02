import Mathlib
import Submission.Work.LinnikAreas.zeta_logDeriv_negHalf_bound
import Submission.Work.LinnikAreas.tentPhi_leftEdge_norm_bound
import Submission.Work.LinnikAreas.integrable_leftEdge_kernel
import Submission.Work.LinnikAreas.integral_leftEdge_kernel_le

/-!
# The `ζ` tent integral on the left edge `Re s = -1/2`

We bound the tent explicit-formula integral of `ζ'/ζ` along the line `Re s = -1/2` by
`q ^ (-(147/20)) / log q`, uniformly in the height.

The two ingredients are the pointwise bound `‖ζ'/ζ(-1/2 + i t)‖ ≤ C (1 + log(|t| + 2))`
(`Work.LinnikAreas.zeta_logDeriv_negHalf_bound`) and the decay of the tent kernel
`Work.LinnikAreas.tentPhi_leftEdge_norm_bound`
`‖tentPhi (11/2) (3/10) q (-1/2 + it)‖ ≤ 4 q ^ (-(147/20)) / ((log q)^2 (9/4 + t^2))`,
together with the Lorentz-type integral estimate
`Work.LinnikAreas.integral_leftEdge_kernel_le`.
-/

open MeasureTheory
open scoped Real Topology

namespace Work.LinnikAreas

noncomputable section

private lemma const_bound {Cz R x : ℝ} (hCz : 0 < Cz) (hR : 0 ≤ R) (hx : 1 / 2 ≤ x) :
    (1 / (2 * Real.pi)) * ((4 * Cz * R * (x ^ 2)⁻¹) * 80)
      ≤ (100000 * Cz) * (x⁻¹ * R * (1 + x)) := by
  have hx0 : 0 < x := by linarith
  have hCz0 : 0 ≤ Cz := le_of_lt hCz
  have hpi : (1 : ℝ) / (2 * Real.pi) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [Real.pi_gt_three]
  have h80 : 0 ≤ (4 * Cz * R * (x ^ 2)⁻¹) * 80 := by positivity
  have hstep : (1 / (2 * Real.pi)) * ((4 * Cz * R * (x ^ 2)⁻¹) * 80)
      ≤ (4 * Cz * R * (x ^ 2)⁻¹) * 80 := by
    calc (1 / (2 * Real.pi)) * ((4 * Cz * R * (x ^ 2)⁻¹) * 80)
        ≤ 1 * ((4 * Cz * R * (x ^ 2)⁻¹) * 80) := mul_le_mul_of_nonneg_right hpi h80
      _ = (4 * Cz * R * (x ^ 2)⁻¹) * 80 := by ring
  refine le_trans hstep ?_
  have htarget : (320 : ℝ) ≤ 100000 * ((1 + x) * x) := by nlinarith [hx]
  have h2 : (320 : ℝ) * (x ^ 2)⁻¹ ≤ 100000 * (x⁻¹ * (1 + x)) := by
    have hx2pos : 0 < x ^ 2 := by positivity
    have e1 : (320 : ℝ) * (x ^ 2)⁻¹ = 320 / x ^ 2 := by rw [div_eq_mul_inv]
    have e2 : (100000 : ℝ) * (x⁻¹ * (1 + x)) = 100000 * (1 + x) / x := by
      rw [div_eq_mul_inv]; ring
    rw [e1, e2, div_le_div_iff₀ hx2pos hx0]
    have h3 := mul_le_mul_of_nonneg_right htarget hx0.le
    nlinarith [h3]
  calc (4 * Cz * R * (x ^ 2)⁻¹) * 80 = 320 * (Cz * R) * (x ^ 2)⁻¹ := by ring
    _ ≤ 100000 * (Cz * R) * (x⁻¹ * (1 + x)) := by
        have := mul_le_mul_of_nonneg_right h2 (mul_nonneg hCz0 hR)
        nlinarith [this]
    _ = (100000 * Cz) * (x⁻¹ * R * (1 + x)) := by ring

theorem tent_zeta_leftEdge_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q →
      ‖(1 / (2 * Real.pi)) * ∫ t : ℝ,
          logDeriv riemannZeta ((-(1 / 2) : ℂ) + (t : ℂ) * Complex.I) *
            Commons.NumberTheory.Linnik.tentPhi (11 / 2) (3 / 10) q
              ((-(1 / 2) : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * ((Real.log (q : ℝ))⁻¹ * ((q : ℝ) ^ (-(147 : ℝ) / 20)) * (1 + Real.log (q : ℝ))) := by
  obtain ⟨Cz, hCzpos, hCzb⟩ := zeta_logDeriv_negHalf_bound
  refine ⟨100000 * Cz, by positivity, ?_⟩
  intro q hq
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hApos : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hAhalf : (1 : ℝ) / 2 ≤ Real.log (q : ℝ) := by
    have h2 : Real.log 2 ≤ Real.log (q : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hq)
    linarith [Real.log_two_gt_d9]
  have hR0 : 0 ≤ (q : ℝ) ^ (-(147 : ℝ) / 20) :=
    Real.rpow_nonneg (by positivity) _
  have hpoint : ∀ t : ℝ,
      ‖logDeriv riemannZeta ((-(1 / 2) : ℂ) + (t : ℂ) * Complex.I) *
        Commons.NumberTheory.Linnik.tentPhi (11 / 2) (3 / 10) q
          ((-(1 / 2) : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ (4 * Cz * ((q : ℝ) ^ (-(147 : ℝ) / 20)) * ((Real.log (q : ℝ)) ^ 2)⁻¹) *
          ((1 + Real.log (|t| + 2)) / (9 / 4 + t ^ 2)) := by
    intro t
    rw [norm_mul]
    have h1 := hCzb t
    have h2 := tentPhi_leftEdge_norm_bound q hq t
    have h3 : 0 ≤ Cz * (1 + Real.log (|t| + 2)) := by
      have : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
      positivity
    refine le_trans (mul_le_mul h1 h2 (norm_nonneg _) h3) (le_of_eq ?_)
    have hAne : Real.log (q : ℝ) ≠ 0 := hApos.ne'
    field_simp
  have hmajint : Integrable (fun t : ℝ =>
      (4 * Cz * ((q : ℝ) ^ (-(147 : ℝ) / 20)) * ((Real.log (q : ℝ)) ^ 2)⁻¹) *
        ((1 + Real.log (|t| + 2)) / (9 / 4 + t ^ 2))) :=
    integrable_leftEdge_kernel.const_mul _
  have key1 : ‖∫ t : ℝ, logDeriv riemannZeta ((-(1 / 2) : ℂ) + (t : ℂ) * Complex.I) *
        Commons.NumberTheory.Linnik.tentPhi (11 / 2) (3 / 10) q
          ((-(1 / 2) : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ ∫ t : ℝ,
          (4 * Cz * ((q : ℝ) ^ (-(147 : ℝ) / 20)) * ((Real.log (q : ℝ)) ^ 2)⁻¹) *
            ((1 + Real.log (|t| + 2)) / (9 / 4 + t ^ 2)) := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    exact integral_mono_of_nonneg (ae_of_all _ fun t => norm_nonneg _) hmajint (ae_of_all _ hpoint)
  have key2 : (∫ t : ℝ,
          (4 * Cz * ((q : ℝ) ^ (-(147 : ℝ) / 20)) * ((Real.log (q : ℝ)) ^ 2)⁻¹) *
            ((1 + Real.log (|t| + 2)) / (9 / 4 + t ^ 2)))
      ≤ (4 * Cz * ((q : ℝ) ^ (-(147 : ℝ) / 20)) * ((Real.log (q : ℝ)) ^ 2)⁻¹) * 80 := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left integral_leftEdge_kernel_le (by positivity)
  have hnorm : ‖(1 / (2 * Real.pi)) * ∫ t : ℝ,
        logDeriv riemannZeta ((-(1 / 2) : ℂ) + (t : ℂ) * Complex.I) *
          Commons.NumberTheory.Linnik.tentPhi (11 / 2) (3 / 10) q
            ((-(1 / 2) : ℂ) + (t : ℂ) * Complex.I)‖
      = (1 / (2 * Real.pi)) * ‖∫ t : ℝ,
        logDeriv riemannZeta ((-(1 / 2) : ℂ) + (t : ℂ) * Complex.I) *
          Commons.NumberTheory.Linnik.tentPhi (11 / 2) (3 / 10) q
            ((-(1 / 2) : ℂ) + (t : ℂ) * Complex.I)‖ := by
    have hsc : ‖(1 : ℂ) / (2 * (Real.pi : ℂ))‖ = 1 / (2 * Real.pi) := by
      have hcast : (1 : ℂ) / (2 * (Real.pi : ℂ)) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
        push_cast; ring
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [norm_mul, hsc]
  rw [hnorm]
  refine le_trans (mul_le_mul_of_nonneg_left (le_trans key1 key2) (by positivity)) ?_
  exact const_bound hCzpos hR0 hAhalf

end

end Work.LinnikAreas
