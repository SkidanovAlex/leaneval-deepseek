import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.gam_rad_integral_le
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.Norm

/-- **The angular factor of the `ℋⁿ`-integrand of `Γ(θ)·r(z)` is `θ`-integrable with an
`α`-uniform bound.**

The angular weight that appears when the sharp profile `G θ = sin(2θ)^{α/5}` is folded into the
heavy weight `τ = sin(2θ)^{-γ}` is

  `smE θ + 4·(10^5 α)²·sin(2θ)^{2(α/5) - γ}`,

with `smE θ = sin(2θ)^{-η}` (`η = 99/100`) and `γ = 1 + α/10`.  Both exponents
`-η ∈ (-1,0)` and `2α/5 - γ = -1 + 3α/10 ∈ (-1,0)` for `α ∈ (0,1]` are `> -1`, so each
summand is integrable on `Iθ`; quantitatively `sin_two_rpow` gives

  `∫_{Iθ} sin(2θ)^{-η} ≤ 10^4`  and  `∫_{Iθ} sin(2θ)^{2α/5-γ} ≤ 10^3/(3α)`,

and the second bound, whose divergence as `α → 0⁺` is `~ 1/α`, is multiplied by the `α²` of
the coefficient `4·(10^5 α)²` and by `α ≤ 1`, giving the `α`-independent constant `K`.

This is the `RintN = 1` (trivial radial density) case of `E2norm.gam_rad_integral_le`. -/
theorem ang_fac_integrable_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
      MeasureTheory.IntegrableOn (fun θ : ℝ =>
          Work.FTS.Nonlinear.RadialProd.smE θ
            + 4 * (100000 * α) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ,
          (Work.FTS.Nonlinear.RadialProd.smE θ
            + 4 * (100000 * α) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α))) ≤ K := by
  refine ⟨10000 + 40000000000000 / 3, by norm_num, ?_⟩
  intro α hα hα1
  -- Integrability of the two summands.
  have hIe : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.Nonlinear.RadialProd.smE θ)
      Work.Spaces.Iθ := by
    have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
      (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_pos])).1
    simpa [Work.FTS.Nonlinear.RadialProd.smE] using h
  have hp1 : -1 < 2 * (α / 5) - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hp2 : 2 * (α / 5) - Work.Spaces.gam α ≤ 0 := by rw [Work.Spaces.gam]; linarith
  have hIex : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)) Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow _ hp1 hp2).1
  constructor
  · exact hIe.add (hIex.const_mul _)
  · -- The two numerical bounds for the `θ`-integrals.
    have hIe_le : (∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.RadialProd.smE θ) ≤ 10000 := by
      have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
        (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_pos])).2
      have hexp : -(Work.Spaces.eta) + 1 = (1 : ℝ) / 100 := by rw [Work.Spaces.eta]; norm_num
      rw [hexp] at h
      have h2 : (100 : ℝ) / ((1 : ℝ) / 100) = 10000 := by norm_num
      rw [h2] at h
      simpa [Work.FTS.Nonlinear.RadialProd.smE] using h
    have hIex_le : (∫ θ in Work.Spaces.Iθ,
        (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)) ≤ 1000 / (3 * α) := by
      have h := (Work.Spaces.sin_two_rpow _ hp1 hp2).2
      have hexp : 2 * (α / 5) - Work.Spaces.gam α + 1 = 3 * α / 10 := by
        rw [Work.Spaces.gam]; ring
      rw [hexp] at h
      have heq : (100 : ℝ) / (3 * α / 10) = 1000 / (3 * α) := by
        have h1 : (3 : ℝ) * α ≠ 0 := by positivity
        have h2 : (3 : ℝ) * α / 10 ≠ 0 := by positivity
        field_simp
        ring
      calc (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α))
          ≤ 100 / (3 * α / 10) := h
        _ = 1000 / (3 * α) := heq
    have h4 : (0 : ℝ) ≤ 4 * (100000 * α) ^ 2 := by positivity
    have hkey : 10000 + 4 * (100000 * α) ^ 2 * (1000 / (3 * α))
        ≤ 10000 + 40000000000000 / 3 := by
      have heq : 4 * (100000 * α) ^ 2 * (1000 / (3 * α)) = (40000000000000 / 3) * α := by
        have h1 : α ≠ 0 := ne_of_gt hα
        field_simp
        ring
      rw [heq]
      nlinarith [hα1]
    have hsplit : (∫ θ in Work.Spaces.Iθ,
          (Work.FTS.Nonlinear.RadialProd.smE θ
            + 4 * (100000 * α) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)))
        = (∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.RadialProd.smE θ)
          + 4 * (100000 * α) ^ 2
            * ∫ θ in Work.Spaces.Iθ,
                (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α) := by
      rw [MeasureTheory.integral_add hIe (hIex.const_mul _), MeasureTheory.integral_const_mul]
    rw [hsplit]
    linarith [hIe_le, mul_le_mul_of_nonneg_left hIex_le h4, hkey]

end Work.FTS.GalFields.Norm
