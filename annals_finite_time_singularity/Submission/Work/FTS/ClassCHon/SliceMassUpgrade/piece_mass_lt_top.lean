import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassCHon.SliceMassUpgrade.sliceMass_lintegral_up_gen
import Submission.Work.FTS.ClassCHon.SliceMassUpgrade.ofReal_sliceMass_pointwise
import Submission.Work.FTS.ClassCHon.SliceMassUpgrade.ofReal_sliceMass_pointwise_gen
import Submission.Work.FTS.ClassCHon.SliceMassUpgrade.sliceMass_dz_comparison
import Submission.Work.FTS.ClassCHon.SliceMassUpgrade.sliceMass_dz_comparison_gen
import Submission.Work.FTS.ClassCHon.SliceMassUpgrade.sliceMass_ae_finite_upgrade
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

namespace Work.FTS.ClassCHon.SliceMassUpgrade

/-! ## The measurability of a `τ`-weighted slice density

The up-estimate `sliceMass_lintegral_up_gen` and the a.e.-finiteness upgrade both need the
almost-everywhere measurability of `(z,θ) ↦ ofReal (τ θ · X(z,θ)²)` for the product measure
`(volume ↾ (0,∞)) ⊗ (volume ↾ (0,π/2))`, where `τ` is only assumed `ContinuousOn (0,π/2)`
(not globally measurable) and `X` is continuous on the open quadrant.  Both functions are
continuous on the open quadrant — `τ` because the second coordinate stays inside `(0,π/2)` —
and the product measure is the restriction of the planar Lebesgue measure to the quadrant, so
continuity on a measurable set gives a.e.-strong-measurability. -/

theorem aemeasurable_tau_mul_sq {X : ℝ → ℝ → ℝ} {τ : ℝ → ℝ}
    (hX : ContinuousOn (fun p : ℝ × ℝ => X p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hτc : ContinuousOn τ (Set.Ioo 0 (π / 2))) :
    AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (τ p.2 * (X p.1 p.2) ^ 2))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2)))) := by
  have hQ0 : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  -- the product of the two restricted Lebesgue measures *is* the planar Lebesgue measure
  -- restricted to the open quadrant
  have hvol : ((volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
      = (volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2))) := by
    show (volume.prod volume).restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))
      = (volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2)))
    rw [Measure.prod_restrict]
  have hXaesm : AEStronglyMeasurable (fun p : ℝ × ℝ => X p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2)))) :=
    hvol ▸ hX.aestronglyMeasurable hQ0
  have hτcont : ContinuousOn (fun p : ℝ × ℝ => τ p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hτc.comp continuous_snd.continuousOn (fun p hp => hp.2)
  have hτaesm : AEStronglyMeasurable (fun p : ℝ × ℝ => τ p.2)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2)))) :=
    hvol ▸ (hτcont.aestronglyMeasurable hQ0)
  have hXsq : AEMeasurable (fun p : ℝ × ℝ => (X p.1 p.2) ^ 2)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2)))) :=
    hXaesm.aemeasurable.pow aemeasurable_const
  have hprod : AEMeasurable (fun p : ℝ × ℝ => τ p.2 * (X p.1 p.2) ^ 2)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2)))) :=
    hτaesm.aemeasurable.mul hXsq
  exact hprod.ennreal_ofReal

/-! ## The every-`z` finiteness of the `τ`-weighted slice mass

This is the `τ`-weighted analogue of `sliceMass_lintegral_lt_top_of_outer`, with `hmeas` /
`hmeasmine` replaced by the measurability supplied by the continuity of `τ`
(`aemeasurable_tau_mul_sq`). -/

theorem piece_mass_lt_top {g : ℝ → ℝ → ℝ} {τ : ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hτc : ContinuousOn τ (Set.Ioo 0 (π / 2)))
    (hτ : ∀ θ ∈ Set.Ioo 0 (π / 2), 0 ≤ τ θ)
    (hO0 : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (τ θ * (g z θ) ^ 2)) < ⊤)
    (hO1 : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (τ θ * (z * Work.Spaces.pz g z θ) ^ 2)) < ⊤) :
    ∀ z ∈ Set.Ioi 0,
      (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (τ θ * (g z θ) ^ 2)) < ⊤ := by
  intro z hz
  have hzpos : 0 < z := hz
  -- the two a.e.-measurabilities (of the `g`-density and of the `z ∂_z g`-density)
  have hmeas_pz : AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (τ p.2 * (Work.Spaces.pz g p.1 p.2) ^ 2))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2)))) :=
    aemeasurable_tau_mul_sq (hg.pz).continuousOn hτc
  have hmeas_g : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (τ p.2 * (g p.1 p.2) ^ 2))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2)))) :=
    aemeasurable_tau_mul_sq hg.continuousOn hτc
  have hmeasmine : AEMeasurable (fun z => ∫⁻ θ in Set.Ioo 0 (π / 2),
      ENNReal.ofReal (τ θ * (g z θ) ^ 2)) (volume.restrict (Set.Ioi 0)) :=
    hmeas_g.lintegral_prod_right'
  -- a.e. finiteness of the slice mass from the outer bound `hO0`
  have haefin : ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)),
      (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (τ θ * (g t θ) ^ 2)) < ⊤ :=
    MeasureTheory.ae_lt_top' hmeasmine (ne_of_lt hO0)
  have hpos : 0 < z / 2 := by linarith
  have hlt : z / 2 < z := by linarith
  have hae0 : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioi (0 : ℝ) →
      (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (τ θ * (g t θ) ^ 2)) < ⊤ :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mp haefin
  have hae_sub : ∀ᵐ t ∂(volume.restrict (Set.Ioo (z / 2) z)),
      (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (τ θ * (g t θ) ^ 2)) < ⊤ := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hae0] with t ht htm
    exact ht (lt_of_lt_of_le hpos (le_of_lt htm.1))
  -- a good (finite) radius `z₁ ∈ (z/2, z)`
  obtain ⟨z₁, hz₁mem, hz₁fin⟩ := exists_lt_top_of_ae_lt_top hlt hae_sub
  have hz₁pos : 0 < z₁ := by linarith [hz₁mem.1]
  have hz₁le : z₁ ≤ z := le_of_lt hz₁mem.2
  -- the up-estimate at `(z₁, z)`, with the pointwise Cauchy–Schwarz bound and the
  -- `∂_z`-mass comparison both for the general weight `τ`
  refine lt_of_le_of_lt (sliceMass_lintegral_up_gen hg hτ hmeas_pz
    (fun z₁ z₂ θ hz₁ hz₁₂ hθ => ?_) (fun z₁ s hz₁ hz₁s => ?_) hz₁pos hz₁le) ?_
  · simpa only [mul_assoc] using ofReal_sliceMass_pointwise_gen hg hτ hz₁ hz₁₂ hθ
  · exact sliceMass_dz_comparison_gen hz₁ hz₁s
  · refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
    · exact ENNReal.mul_lt_top (by norm_num) hz₁fin
    · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hO1

end Work.FTS.ClassCHon.SliceMassUpgrade
