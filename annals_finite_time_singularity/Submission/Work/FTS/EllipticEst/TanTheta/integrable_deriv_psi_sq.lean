import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.TanTheta.Basic
import Submission.Work.FTS.H2.STBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TanTheta

set_option autoImplicit false

/-- `sin (2θ) > 0` on `(0, π/2)`. -/
private lemma sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- If `ψ'` is bounded by `D` on `(0, π/2)` then `(ψ')² sin(2θ)^{-η}` is integrable there,
for `η < 1` (the integrability of `sin(2θ)^{-η}` on `(0, π/2)` is exactly
`Work.FTS.H2.intervalIntegrable_sin_rpow (-η) (by linarith)`, which lives in
`Submission/Work/FTS/H2/STBasic.lean` and can be imported; transport it with
`intervalIntegrable_iff_integrableOn_Ioo_of_le`).

Route: `Integrable.mono'` with the majorant `fun θ => D ^ 2 * sin (2θ) ^ (-η)`; the
measurability of `deriv (psi u)` is free from `measurable_deriv`. -/
theorem integrable_deriv_psi_sq (η : ℝ) (hη1 : η < 1) (u : ℝ → ℝ) (D : ℝ)
    (hD : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      ‖deriv (Work.FTS.EllipticEst.TanTheta.psi u) θ‖ ≤ D) :
    MeasureTheory.IntegrableOn
      (fun θ => (deriv (Work.FTS.EllipticEst.TanTheta.psi u) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-η)) (Set.Ioo 0 (Real.pi / 2)) := by
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  -- Integrability of the majorant weight `sin (2θ)^(-η)` on `(0, π/2)`.
  have hbase : MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-η))
      (Set.Ioo 0 (Real.pi / 2)) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le hle]
    exact Work.FTS.H2.intervalIntegrable_sin_rpow (-η) (by linarith)
  refine MeasureTheory.Integrable.mono' (hbase.const_mul (D ^ 2)) ?_ ?_
  · -- measurability of the integrand: `deriv (psi u)` is measurable by
    -- `measurable_deriv`, and the `rpow` factor because `MeasurablePow ℝ ℝ` holds
    apply Measurable.aestronglyMeasurable
    fun_prop
  · -- pointwise domination on `(0, π/2)`
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hs : (0 : ℝ) < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
    have hsp : 0 ≤ (Real.sin (2 * θ)) ^ (-η) := Real.rpow_nonneg hs.le _
    have h1 : |deriv (Work.FTS.EllipticEst.TanTheta.psi u) θ| ≤ D := by
      simpa only [Real.norm_eq_abs] using hD θ hθ
    have h2 : (deriv (Work.FTS.EllipticEst.TanTheta.psi u) θ) ^ 2 ≤ D ^ 2 :=
      sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hsp)]
    exact mul_le_mul_of_nonneg_right h2 hsp

end Work.FTS.EllipticEst.TanTheta
