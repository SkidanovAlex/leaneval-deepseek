import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PressureOn.Auxiliary.HeatKernel
import Submission.Work.FTS.PressureOn.Auxiliary.deriv_heatKernel_time

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The heat equation for the heat kernel: `∂_t γ_t(z) = Δ_z γ_t(z)`

`heatKernel t z = (4πt)^{-3/2} exp(-‖z‖²/(4t))` satisfies the heat equation in the strong
(derivative) form: for every `t > 0` and every `z : ℝ³`,

`HasDerivAt (fun s => heatKernel s z) (laplaceTrace (heatKernel t) z) t`,

where `laplaceTrace φ z = ∑ᵢ ∂ᵢ∂ᵢ φ(z)` is the Euclidean Laplacian in the *spatial* variable
(so the right-hand side is `Δ_z γ_t(z)`).

The two computations are:

* **spatial**, `Δ_z γ_t(z) = (4πt)^{-3/2} (‖z‖²/(4t²) - 3/(2t)) exp(-‖z‖²/(4t))`: split off the
  constant prefactor `A = (4πt)^{-3/2}` (`laplaceTrace` is `ℝ`-homogeneous, `laplaceTrace_const_mul`)
  and use `Green.laplaceTrace_exp_neg_mul_normSq`, the Laplacian of a Gaussian
  `Δ exp(-c‖y‖²) = (4c²‖y‖² - 6c) exp(-c‖y‖²)`;
* **temporal**, `∂_t γ_t(z) = (4πt)^{-3/2} (‖z‖²/(4t²) - 3/(2t)) exp(-‖z‖²/(4t))`: the product rule
  applied to `t ↦ (4πt)^{-3/2}` and `t ↦ exp(-‖z‖²/(4t))`
  (`hasDerivAt_heatPrefactor` and `hasDerivAt_heatGauss`).

The two values are equal by elementary algebra, which is the content of the theorem. -/

open Work.FTS.PressureOn (laplaceTrace)

namespace Work.FTS.PressureOn.Auxiliary

/-- `laplaceTrace` is homogeneous under multiplication by a constant: for `φ` of class `C²`,
`laplaceTrace (fun y => c * φ y) x = c * laplaceTrace φ x`.

(Unfolding the definition, both `fderiv`s in the chain are linear in the constant: the first
derivative of `c * φ` is `c • fderiv φ`, and then the second derivative of
`w ↦ c * (fderiv φ w (eᵢ))` is `c •` that of `w ↦ fderiv φ w (eᵢ)`.  Both applications of
`fderiv_const_mul` need the differentiability of the differentiated function, which is supplied by
`hφ` and by `hφ.fderiv_right`.) -/
lemma laplaceTrace_const_mul (c : ℝ) (φ : Work.FTS.PressureOn.R3 → ℝ)
    (hφ : ContDiff ℝ 2 φ) (x : Work.FTS.PressureOn.R3) :
    laplaceTrace (fun y => c * φ y) x = c * laplaceTrace φ x := by
  have hd1 : ∀ w, DifferentiableAt ℝ φ w := fun w => hφ.differentiable (by norm_num) w
  have hd2 : ∀ (i : Fin 3) (w : Work.FTS.PressureOn.R3),
      DifferentiableAt ℝ (fun w' : Work.FTS.PressureOn.R3 =>
        fderiv ℝ φ w' (FiniteTimeSingularity.e i)) w := by
    intro i w
    have h1 : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (m := 1) (by norm_num)
    have h2 : ContDiff ℝ 1 (fun w' : Work.FTS.PressureOn.R3 =>
        fderiv ℝ φ w' (FiniteTimeSingularity.e i)) :=
      (ContinuousLinearMap.apply ℝ ℝ (FiniteTimeSingularity.e i)).contDiff.comp h1
    exact h2.differentiable (by norm_num) w
  unfold laplaceTrace
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hA : (fun w : Work.FTS.PressureOn.R3 =>
        fderiv ℝ (fun y => c * φ y) w (FiniteTimeSingularity.e i))
      = (fun w : Work.FTS.PressureOn.R3 =>
          c * (fderiv ℝ φ w (FiniteTimeSingularity.e i))) := by
    funext w
    rw [fderiv_const_mul (hd1 w) c]
    simp
  rw [hA, fderiv_const_mul (hd2 i x) c]
  simp

/-- **The Laplacian of the heat kernel** in the spatial variable:
`Δ_z γ_t(z) = (4πt)^{-3/2} (4(4t)^{-2}‖z‖² - 6(4t)^{-1}) exp(-(4t)^{-1}‖z‖²)`.

The factor `(4t)^{-1}` is the Gaussian parameter `c` of `heatKernel t`, i.e.
`heatKernel t y = (4πt)^{-3/2} exp(-c‖y‖²)`; the statement is the homogeneity
`laplaceTrace_const_mul` applied to `Green.laplaceTrace_exp_neg_mul_normSq`. -/
lemma laplaceTrace_heatKernel (t : ℝ) (z : Work.FTS.PressureOn.R3) :
    laplaceTrace (Work.FTS.PressureOn.Auxiliary.heatKernel t) z
      = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
          ((4 * (4 * t)⁻¹ ^ 2 * ‖z‖ ^ 2 - 6 * (4 * t)⁻¹) *
            Real.exp (-((4 * t)⁻¹ * ‖z‖ ^ 2))) := by
  have hc : ContDiff ℝ 2 (fun y : Work.FTS.PressureOn.R3 =>
      Real.exp (-((4 * t)⁻¹ * ‖y‖ ^ 2))) :=
    (((contDiff_const.mul (contDiff_norm_sq ℝ)).neg).exp)
  have hfun : Work.FTS.PressureOn.Auxiliary.heatKernel t
      = fun y : Work.FTS.PressureOn.R3 =>
          (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-((4 * t)⁻¹ * ‖y‖ ^ 2)) := by
    funext y
    rw [Work.FTS.PressureOn.Auxiliary.heatKernel_apply]
    simp only [div_eq_inv_mul]
  rw [hfun, laplaceTrace_const_mul _ _ hc z,
    Work.FTS.PressureOn.Green.laplaceTrace_exp_neg_mul_normSq]

/-- **The heat equation for the heat kernel**: for `t > 0`, the time derivative at `t` of the
spatial profile `z ↦ γ_t(z)` is the Laplacian of the profile at time `t`, evaluated at `z`, i.e.
`∂_t γ_t(z) = Δ_z γ_t(z)`.

`HasDerivAt` is computed by the product rule (`hasDerivAt_heatPrefactor`,
`hasDerivAt_heatGauss`), the Laplacian by `laplaceTrace_heatKernel`; the two values coincide
because `4(4t)^{-2} = 1/(4t²)` and `6(4t)^{-1} = 3/(2t)`. -/
theorem hasDerivAt_heatKernel_time (t : ℝ) (ht : 0 < t) (z : Work.FTS.PressureOn.R3) :
    HasDerivAt (fun s : ℝ => Work.FTS.PressureOn.Auxiliary.heatKernel s z)
      (Work.FTS.PressureOn.laplaceTrace (Work.FTS.PressureOn.Auxiliary.heatKernel t) z) t := by
  -- The time derivative of the heat kernel, by the product rule.
  have h := (Work.FTS.PressureOn.Auxiliary.hasDerivAt_heatPrefactor t ht).mul
    (Work.FTS.PressureOn.Auxiliary.hasDerivAt_heatGauss t ht z)
  have h1 : (-(3 / (2 * t)) * (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
        Real.exp (-(‖z‖ ^ 2 / (4 * t))) +
        (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
          (Real.exp (-(‖z‖ ^ 2 / (4 * t))) * (‖z‖ ^ 2 / (4 * t ^ 2))))
      = ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (‖z‖ ^ 2 / (4 * t ^ 2) - 3 / (2 * t)) *
          Real.exp (-(‖z‖ ^ 2 / (4 * t)))) := by
    ring
  have h2 := h.congr_deriv h1
  have hfun : ((fun s : ℝ => (4 * Real.pi * s) ^ (-(3 / 2 : ℝ))) *
        fun s : ℝ => Real.exp (-(‖z‖ ^ 2 / (4 * s))))
      = (fun s : ℝ => Work.FTS.PressureOn.Auxiliary.heatKernel s z) := by
    funext s
    simp only [Pi.mul_apply, Work.FTS.PressureOn.Auxiliary.heatKernel_apply]
  have hderiv : HasDerivAt (fun s : ℝ => Work.FTS.PressureOn.Auxiliary.heatKernel s z)
      ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (‖z‖ ^ 2 / (4 * t ^ 2) - 3 / (2 * t)) *
        Real.exp (-(‖z‖ ^ 2 / (4 * t)))) t := by
    simpa only [hfun] using h2
  -- Replace the target value by the explicit Laplacian and compare the two expressions.
  rw [laplaceTrace_heatKernel t z]
  refine hderiv.congr_deriv ?_
  have hexp : Real.exp (-(‖z‖ ^ 2 / (4 * t))) = Real.exp (-((4 * t)⁻¹ * ‖z‖ ^ 2)) := by
    congr 1
    rw [div_eq_inv_mul, mul_comm]
  have hcoef : 4 * (4 * t)⁻¹ ^ 2 * ‖z‖ ^ 2 - 6 * (4 * t)⁻¹
      = ‖z‖ ^ 2 / (4 * t ^ 2) - 3 / (2 * t) := by
    field_simp
    ring
  rw [hexp, hcoef]
  ring

end Work.FTS.PressureOn.Auxiliary
