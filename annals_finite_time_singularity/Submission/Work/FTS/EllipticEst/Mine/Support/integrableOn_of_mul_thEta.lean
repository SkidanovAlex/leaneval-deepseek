import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Mine.Support

open MeasureTheory

/-- **Removing the angular weight `sin(2θ)^{-η}`.**  If `f` is continuous and nonnegative on
`(0, π/2)` and `f · thEta` is integrable on `Iθ = [0, π/2]` (where
`thEta θ = sin(2θ)^{-η}`, `η = 99/100`), then `f` is integrable on `Iθ` (with an honest, non-junk
integral) and `∫_{Iθ} f ≤ ∫_{Iθ} f · thEta`, because `thEta ≥ 1` on `(0,π/2)` while `{0, π/2}` is
null.  Route: `Integrable.mono'` with `g := f * thEta` on `volume.restrict Iθ`, using
`ContinuousOn.aestronglyMeasurable` transported from the measurable set `Ioo 0 (π/2)` (a.e. equal to
`Iθ`), and `setIntegral_mono_ae` for the integral comparison. -/
theorem integrableOn_of_mul_thEta {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioo 0 (Real.pi / 2)))
    (hnn : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ f θ)
    (h : MeasureTheory.IntegrableOn (fun θ => f θ * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn f Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, f θ)
        ≤ ∫ θ in Work.Spaces.Iθ, f θ * Work.FTS.EllipticEst.thEta θ := by
  -- `(0, π/2)` and `Iθ = [0, π/2]` differ by the null set `{0, π/2}`, so they carry the same
  -- restricted measure.
  have hIoo_eq : Set.Ioo (0 : ℝ) (Real.pi / 2) =ᵐ[volume] Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Ioo_ae_eq_Icc
  have hres : volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set hIoo_eq
  -- `thEta ≥ 1` on `(0, π/2)`.
  have hone : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      1 ≤ Work.FTS.EllipticEst.thEta θ := by
    intro θ hθ
    have h1 : 0 < Real.sin (2 * θ) := Work.FTS.EllipticEst.sin_two_pos hθ
    have h2 : Real.sin (2 * θ) ≤ 1 := Work.FTS.EllipticEst.sin_two_le_one θ
    have h3 : (Real.sin (2 * θ)) ^ (0 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      Real.rpow_le_rpow_of_exponent_ge h1 h2 (by linarith [Work.Spaces.eta_nonneg])
    simpa [Work.FTS.EllipticEst.thEta, Real.rpow_zero] using h3
  -- A.e. strong measurability of `f`, transported from the open interval.
  have haesm : AEStronglyMeasurable f (volume.restrict Work.Spaces.Iθ) := by
    rw [← hres]
    exact hf.aestronglyMeasurable measurableSet_Ioo
  -- The a.e. domination `‖f‖ ≤ f · thEta`.
  have hbound : ∀ᵐ θ ∂volume.restrict Work.Spaces.Iθ,
      ‖f θ‖ ≤ f θ * Work.FTS.EllipticEst.thEta θ := by
    rw [← hres]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hfθ : 0 ≤ f θ := hnn θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg hfθ]
    exact le_mul_of_one_le_right hfθ (hone θ hθ)
  have hf_int : Integrable f (volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.Integrable.mono' h haesm hbound
  -- The a.e. comparison `f ≤ f · thEta` for the integrals.
  have hle_ae : f ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => f θ * Work.FTS.EllipticEst.thEta θ) := by
    rw [← hres]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hfθ : 0 ≤ f θ := hnn θ hθ
    exact le_mul_of_one_le_right hfθ (hone θ hθ)
  exact ⟨hf_int, MeasureTheory.setIntegral_mono_ae_restrict hf_int h hle_ae⟩

end Work.FTS.EllipticEst.Mine.Support
