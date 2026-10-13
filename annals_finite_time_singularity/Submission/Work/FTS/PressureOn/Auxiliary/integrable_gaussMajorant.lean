import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Submission.Work.FTS.PressureOn.Auxiliary.HeatKernel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Auxiliary

open MeasureTheory

set_option linter.unusedVariables false

/-- A quadratic (in fact polynomial) growth factor is integrable against a Gaussian
`exp (-(c ‖z‖²))` on `ℝ³` with `c > 0`: `z ↦ (a + b‖z‖²) exp (-(c ‖z‖²)) ∈ L¹(ℝ³)`.

This is the standard Gauss majorant estimate; it is used to dominate the Newtonian
kernel and its gradients far away from the origin.

The proof passes to polar coordinates in `EuclideanSpace ℝ (Fin 3)` with
`MeasureTheory.integrable_fun_norm_addHaar`, which reduces the claim to the integrability
on `(0,∞)` of `y ^ (2 + k) * exp (-c y²)` (`k = 0, 2`), i.e. to
`integrableOn_rpow_mul_exp_neg_mul_sq` with exponent `s = 2` resp. `s = 4`. -/
theorem integrable_gaussMajorant (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) :
    MeasureTheory.Integrable (fun z : Work.FTS.PressureOn.R3 =>
      (a + b * ‖z‖ ^ 2) * Real.exp (-(c * ‖z‖ ^ 2))) := by
  rw [MeasureTheory.integrable_fun_norm_addHaar
    (μ := (MeasureTheory.volume : MeasureTheory.Measure Work.FTS.PressureOn.R3))
    (f := fun y : ℝ => (a + b * y ^ 2) * Real.exp (-(c * y ^ 2)))]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  have h2 : IntegrableOn (fun y : ℝ => y ^ (((2 : ℕ)) : ℝ) * Real.exp (-c * y ^ 2))
      (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq hc (by norm_num)
  have h4 : IntegrableOn (fun y : ℝ => y ^ (((4 : ℕ)) : ℝ) * Real.exp (-c * y ^ 2))
      (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq hc (by norm_num)
  have hsum : IntegrableOn
      (fun y : ℝ => a * (y ^ (((2 : ℕ)) : ℝ) * Real.exp (-c * y ^ 2))
        + b * (y ^ (((4 : ℕ)) : ℝ) * Real.exp (-c * y ^ 2))) (Set.Ioi 0) :=
    (h2.const_mul a).add (h4.const_mul b)
  exact MeasureTheory.IntegrableOn.congr_fun hsum (fun y hy => by
    have hy0 : 0 ≤ y := le_of_lt hy
    rw [Real.rpow_natCast, Real.rpow_natCast]
    norm_num
    rw [← neg_mul]
    ring) measurableSet_Ioi

end Work.FTS.PressureOn.Auxiliary
