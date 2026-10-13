import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.EllipticEst.ModalSolution.Lzero1_energy_cos_correct
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.H2.ModalSolR

/-- On `Iθ = [0, π/2]` the integrand `(v θ / cos θ)² · cos θ` is nonnegative — `cos ≥ 0`
on `Iθ` and the square factor is a square — hence so is its integral. -/
private theorem integral_div_cos_sq_nonneg (v : ℝ → ℝ) :
    0 ≤ ∫ θ in Work.Spaces.Iθ, (v θ / Real.cos θ) ^ 2 * Real.cos θ := by
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hrew : (∫ θ in Work.Spaces.Iθ, (v θ / Real.cos θ) ^ 2 * Real.cos θ)
      = ∫ θ in (0 : ℝ)..(Real.pi / 2), (v θ / Real.cos θ) ^ 2 * Real.cos θ := by
    rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle]
  rw [hrew]
  exact intervalIntegral.integral_nonneg hle fun θ hθ =>
    mul_nonneg (sq_nonneg _)
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)

theorem energyToDeriv {v : ℝ → ℝ}
    (hv : ContDiffOn ℝ 2 v (Set.Icc 0 (Real.pi / 2)))
    (h0 : v 0 = 0) (h1 : v (Real.pi / 2) = 0)
    (hI1 : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 v θ * v θ * Real.cos θ) Work.Spaces.Iθ)
    (hI2 : MeasureTheory.IntegrableOn (fun θ => (deriv v θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ)
    (hI3 : MeasureTheory.IntegrableOn
      (fun θ => (v θ / Real.cos θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ)
    (hI4 : MeasureTheory.IntegrableOn (fun θ => v θ ^ 2 * Real.cos θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, (deriv v θ) ^ 2 * Real.cos θ)
      ≤ 6 * (∫ θ in Work.Spaces.Iθ, v θ ^ 2 * Real.cos θ)
          + (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1 v θ * v θ * Real.cos θ) := by
  -- the `cos`-weighted energy identity for the angular operator `Lzero1`:
  -- `∫ (Lzero1 v)·v·cos = ∫ (v')²cos + ∫ (v/cos)²cos - 6∫ v²cos`
  have hE :=
    Work.EllipticEst.ModalSolution.Lzero1_energy_cos_correct v hv h0 h1 hI1 hI2 hI3 hI4
  -- the middle term is nonnegative, so it can be dropped from the identity
  have hB := integral_div_cos_sq_nonneg v
  linarith

end Work.FTS.H2.ModalSolR
