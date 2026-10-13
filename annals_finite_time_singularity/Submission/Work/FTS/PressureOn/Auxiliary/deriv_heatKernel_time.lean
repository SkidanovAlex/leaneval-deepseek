import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Submission.Work.FTS.PressureOn.Auxiliary.HeatKernel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The time derivative of the heat kernel

`∂_t γ_t(z) = (4πt)^{-3/2} (‖z‖²/(4t²) - 3/(2t)) exp(-‖z‖²/(4t))` for `t > 0`, where
`γ_t(z) = heatKernel t z = (4πt)^{-3/2} exp(-‖z‖²/(4t))`.

The computation is the product rule applied to the two factors

* `t ↦ (4πt)^{-3/2}`, whose derivative is `-(3/(2t)) (4πt)^{-3/2}`
  (the shift of the exponent `-(3/2) - 1` is handled by `Real.rpow_add`/`Real.rpow_neg_one`),
* `t ↦ exp(-‖z‖²/(4t))`, whose derivative is `(‖z‖²/(4t²)) exp(-‖z‖²/(4t))`.
-/

namespace Work.FTS.PressureOn.Auxiliary

/-- Derivative of the normalising factor `t ↦ (4πt)^{-3/2}` of the heat kernel. -/
lemma hasDerivAt_heatPrefactor (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => (4 * Real.pi * s) ^ (-(3 / 2 : ℝ)))
      (-(3 / (2 * t)) * (4 * Real.pi * t) ^ (-(3 / 2 : ℝ))) t := by
  have h1 : HasDerivAt (fun s : ℝ => 4 * Real.pi * s) (4 * Real.pi) t := by
    simpa using (hasDerivAt_id t).const_mul (4 * Real.pi)
  refine (h1.rpow_const (Or.inl (by positivity))).congr_deriv ?_
  have hP : (4 * Real.pi * t) ^ (-(3 / 2 : ℝ) - 1)
      = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (4 * Real.pi * t)⁻¹ := by
    rw [show -(3 / 2 : ℝ) - 1 = -(3 / 2 : ℝ) + (-1) by ring, Real.rpow_add (by positivity),
      Real.rpow_neg_one]
  rw [hP]
  have key : 4 * (Real.pi : ℝ) * (-(3 / 2 : ℝ)) * (4 * Real.pi * t)⁻¹ = -(3 / (2 * t)) := by
    field_simp
  rw [show 4 * (Real.pi : ℝ) * (-(3 / 2 : ℝ)) *
        ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (4 * Real.pi * t)⁻¹)
      = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
          (4 * (Real.pi : ℝ) * (-(3 / 2 : ℝ)) * (4 * Real.pi * t)⁻¹) by ring]
  rw [key]
  ring

/-- Derivative of the Gaussian factor `t ↦ exp(-‖z‖²/(4t))` of the heat kernel. -/
lemma hasDerivAt_heatGauss (t : ℝ) (ht : 0 < t) (z : R3) :
    HasDerivAt (fun s : ℝ => Real.exp (-(‖z‖ ^ 2 / (4 * s))))
      (Real.exp (-(‖z‖ ^ 2 / (4 * t))) * (‖z‖ ^ 2 / (4 * t ^ 2))) t := by
  have hb : HasDerivAt (fun s : ℝ => 4 * s) (4 : ℝ) t := by
    simpa using (hasDerivAt_id t).const_mul (4 : ℝ)
  have h2 : HasDerivAt (fun s : ℝ => (4 * s)⁻¹) (-(4 : ℝ) / (4 * t) ^ 2) t :=
    hb.inv (by positivity)
  have h3 : HasDerivAt (fun s : ℝ => ‖z‖ ^ 2 * (4 * s)⁻¹)
      (‖z‖ ^ 2 * (-(4 : ℝ) / (4 * t) ^ 2)) t := h2.const_mul (‖z‖ ^ 2)
  refine (h3.neg).exp.congr_deriv ?_
  simp only [Pi.neg_apply, div_eq_mul_inv]
  field_simp

theorem deriv_heatKernel_time (t : ℝ) (ht : 0 < t) (z : Work.FTS.PressureOn.R3) :
    deriv (fun s : ℝ => Work.FTS.PressureOn.Auxiliary.heatKernel s z) t
      = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (‖z‖ ^ 2 / (4 * t ^ 2) - 3 / (2 * t)) *
          Real.exp (-(‖z‖ ^ 2 / (4 * t))) := by
  simp only [heatKernel_apply]
  have hprod : HasDerivAt (fun s : ℝ => (4 * Real.pi * s) ^ (-(3 / 2 : ℝ)) *
      Real.exp (-(‖z‖ ^ 2 / (4 * s))))
      (-(3 / (2 * t)) * (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
          Real.exp (-(‖z‖ ^ 2 / (4 * t))) +
        (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
          (Real.exp (-(‖z‖ ^ 2 / (4 * t))) * (‖z‖ ^ 2 / (4 * t ^ 2)))) t :=
    (hasDerivAt_heatPrefactor t ht).mul (hasDerivAt_heatGauss t ht z)
  rw [hprod.deriv]
  ring

end Work.FTS.PressureOn.Auxiliary
