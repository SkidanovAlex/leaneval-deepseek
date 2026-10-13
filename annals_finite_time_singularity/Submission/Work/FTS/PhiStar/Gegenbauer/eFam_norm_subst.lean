/-
# `eFam_norm_subst` — the `u = sin θ` form of the weight-`cos θ` norm of `eFam`

`eFam m θ = cos θ · gC (2m+1) (sin θ)`, so substituting `u = sin θ`
(`cos θ dθ = du`, `θ ∈ (0, π/2) ↦ u ∈ (0, 1)`) and using `cos²θ = 1 - sin²θ` gives

  `∫_θ eFam m θ ^ 2 · cos θ dθ = ∫_0^1 (1 - u²) · gC (2m+1) u ^ 2 du`

(the index `2m+1` of the Gegenbauer factor is untouched by the substitution).
The proof is the change of variables `intervalIntegral.integral_comp_mul_deriv` with
`f = sin`, applied to `G u = (1 - u²)·gC (2m+1) u ^ 2`, together with the identification of
the set integral over `Iθ = Icc 0 (π/2)` with the interval integral over `0..π/2`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory

namespace Work.FTS.PhiStar.Gegenbauer

set_option autoImplicit false

theorem eFam_norm_subst (m : ℕ) :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
      = ∫ u in (0 : ℝ)..1,
          (1 - u ^ 2) * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) u ^ 2 := by
  set G : ℝ → ℝ := fun u => (1 - u ^ 2) * gC (2 * m + 1) u ^ 2 with hG
  have hGcont : Continuous G := by
    rw [hG]
    exact (continuous_const.sub (continuous_id.pow 2)).mul
      ((contDiff_gC (2 * m + 1)).continuous.pow 2)
  -- the set integral over `Iθ = Icc 0 (π/2)` is the interval integral over `0..π/2`
  have hIθ : (∫ θ in Work.Spaces.Iθ, eFam m θ ^ 2 * Real.cos θ)
      = ∫ θ in (0 : ℝ)..(Real.pi / 2), eFam m θ ^ 2 * Real.cos θ := by
    rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]
  -- substitute `u = sin θ`
  have hsub := intervalIntegral.integral_comp_mul_deriv
    (a := (0 : ℝ)) (b := Real.pi / 2) (f := Real.sin) (f' := Real.cos) (g := G)
    (fun x _ => Real.hasDerivAt_sin x) Real.continuous_cos.continuousOn hGcont
  rw [Real.sin_zero, Real.sin_pi_div_two] at hsub
  -- the integrand `eFam m θ ^ 2 * cos θ` is `G (sin θ) * cos θ`
  have hcongr : (∫ θ in (0 : ℝ)..(Real.pi / 2), eFam m θ ^ 2 * Real.cos θ)
      = ∫ θ in (0 : ℝ)..(Real.pi / 2), (G ∘ Real.sin) θ * Real.cos θ := by
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [Function.comp_apply, hG, eFam]
    rw [← Real.cos_sq']
    ring
  rw [hIθ, hcongr, hsub, hG]

end Work.FTS.PhiStar.Gegenbauer
