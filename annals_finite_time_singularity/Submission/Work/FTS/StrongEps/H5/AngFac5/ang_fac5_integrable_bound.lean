import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.GalFields.Norm.ang_fac_integrable_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5.AngFac5

/-- Same statement as `Work.FTS.GalFields.Norm.ang_fac_integrable_bound` but with the
coefficient `5` in place of `4` in front of the singular angular factor
`(100000·α)²·sin(2θ)^{2α/5-γ}`.  The proof is the same computation: `sin_two_rpow` gives
`∫_{Iθ} sin(2θ)^{-η} ≤ 10⁴` and `∫_{Iθ} sin(2θ)^{2α/5-γ} ≤ 1000/(3α)`, and the `α²` of the
coefficient together with `α ≤ 1` turns the `1/α` divergence into an `α`-independent
constant. -/
theorem ang_fac5_integrable_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.Nonlinear.RadialProd.smE θ
        + 5 * (100000 * α) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α))
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Work.FTS.Nonlinear.RadialProd.smE θ
        + 5 * (100000 * α) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α))) ≤ K := by
  refine ⟨10000 + 50000000000000 / 3, by norm_num, ?_⟩
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
    have h5 : (0 : ℝ) ≤ 5 * (100000 * α) ^ 2 := by positivity
    have hkey : 10000 + 5 * (100000 * α) ^ 2 * (1000 / (3 * α))
        ≤ 10000 + 50000000000000 / 3 := by
      have heq : 5 * (100000 * α) ^ 2 * (1000 / (3 * α)) = (50000000000000 / 3) * α := by
        have h1 : α ≠ 0 := ne_of_gt hα
        field_simp
        ring
      rw [heq]
      nlinarith [hα1]
    have hsplit : (∫ θ in Work.Spaces.Iθ,
          (Work.FTS.Nonlinear.RadialProd.smE θ
            + 5 * (100000 * α) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)))
        = (∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.RadialProd.smE θ)
          + 5 * (100000 * α) ^ 2
            * ∫ θ in Work.Spaces.Iθ,
                (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α) := by
      rw [MeasureTheory.integral_add hIe (hIex.const_mul _), MeasureTheory.integral_const_mul]
    rw [hsplit]
    linarith [hIe_le, mul_le_mul_of_nonneg_left hIex_le h5, hkey]

end Work.FTS.StrongEps.H5.AngFac5
