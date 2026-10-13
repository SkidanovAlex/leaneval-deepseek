import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

theorem ibpZ (σ φ : ℝ → ℝ) (hσ : ContDiffOn ℝ 2 σ (Set.Ioi 0)) (hφ : ContDiffOn ℝ 2 φ (Set.Ioi 0)) (hi1 : MeasureTheory.IntegrableOn (fun z => z * σ z * φ z * deriv φ z) (Set.Ioi 0)) (hi2 : MeasureTheory.IntegrableOn (fun z => deriv (fun z => z * σ z) z * (φ z) ^ 2) (Set.Ioi 0)) (h0 : Filter.Tendsto (fun z => z * σ z * (φ z) ^ 2) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) (hT : Filter.Tendsto (fun z => z * σ z * (φ z) ^ 2) Filter.atTop (nhds 0)) : (∫ z in Set.Ioi 0, σ z * (z * deriv φ z) * φ z) = -(1 / 2) * (∫ z in Set.Ioi 0, deriv (fun z => z * σ z) z * (φ z) ^ 2) := by
  -- One-dimensional integration by parts on `(0, ∞)`, applied to `u = z * σ z`,
  -- `v = (φ z)^2`, with the boundary terms vanishing by `h0` and `hT`.
  have hσ_diff : ∀ x ∈ Set.Ioi (0:ℝ), DifferentiableAt ℝ σ x := fun x hx =>
    (hσ.differentiableOn (by norm_num)).differentiableAt (Ioi_mem_nhds hx)
  have hφ_diff : ∀ x ∈ Set.Ioi (0:ℝ), DifferentiableAt ℝ φ x := fun x hx =>
    (hφ.differentiableOn (by norm_num)).differentiableAt (Ioi_mem_nhds hx)
  -- derivative of `φ ^ 2` is `2 * φ * φ'`
  have hderiv_phi2 : ∀ x ∈ Set.Ioi (0:ℝ), deriv (fun z => φ z ^ 2) x = 2 * φ x * deriv φ x := by
    intro x hx
    have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * φ x) (φ x) :=
      (hasDerivAt_pow 2 (φ x)).congr_deriv (by norm_num)
    have hc : HasDerivAt ((fun y : ℝ => y ^ 2) ∘ φ) ((2 * φ x) * deriv φ x) x :=
      hsq.comp x (hφ_diff x hx).hasDerivAt
    exact hc.deriv
  have hu : ∀ x ∈ Set.Ioi (0:ℝ), HasDerivAt (fun z => z * σ z) (deriv (fun z => z * σ z) x) x :=
    fun x hx => (differentiableAt_id.mul (hσ_diff x hx)).hasDerivAt
  have hv : ∀ x ∈ Set.Ioi (0:ℝ), HasDerivAt (fun z => φ z ^ 2) (deriv (fun z => φ z ^ 2) x) x :=
    fun x hx => ((hφ_diff x hx).pow 2).hasDerivAt
  -- integrability of `(z σ z) * (φ^2)'` follows from `hi1` by the pointwise identity above
  have huv' : MeasureTheory.IntegrableOn (fun x => (x * σ x) * deriv (fun z => φ z ^ 2) x)
      (Set.Ioi 0) := by
    have h2 : MeasureTheory.IntegrableOn (fun x => 2 * (x * σ x * φ x * deriv φ x)) (Set.Ioi 0) :=
      hi1.const_mul 2
    refine h2.congr_fun ?_ measurableSet_Ioi
    intro x hx
    show 2 * (x * σ x * φ x * deriv φ x) = (x * σ x) * deriv (fun z => φ z ^ 2) x
    rw [hderiv_phi2 x hx]; ring
  have hIBP := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := (0:ℝ)) (b' := (0:ℝ))
      (u := fun z => z * σ z) (v := fun z => φ z ^ 2)
      (u' := fun z => deriv (fun z => z * σ z) z) (v' := fun z => deriv (fun z => φ z ^ 2) z)
      hu hv huv' hi2 h0 hT
  -- `∫ (z σ z) (φ^2)' = 2 * ∫ σ (z φ') φ`
  have hL : (∫ x in Set.Ioi 0, (x * σ x) * deriv (fun z => φ z ^ 2) x)
      = 2 * (∫ z in Set.Ioi 0, σ z * (z * deriv φ z) * φ z) := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => by
      show (x * σ x) * deriv (fun z => φ z ^ 2) x = 2 * (σ x * (x * deriv φ x) * φ x)
      rw [hderiv_phi2 x hx]; ring)]
    rw [MeasureTheory.integral_const_mul]
  have hkey : 2 * (∫ z in Set.Ioi 0, σ z * (z * deriv φ z) * φ z)
      = -(∫ z in Set.Ioi 0, deriv (fun z => z * σ z) z * (φ z) ^ 2) := by
    rw [← hL, hIBP]; ring
  linarith [hkey]

end Work.FTS.EllipticEst.remov
