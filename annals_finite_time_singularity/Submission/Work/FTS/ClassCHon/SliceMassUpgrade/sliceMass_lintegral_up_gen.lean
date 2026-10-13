import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.ClassCHon.SliceMassUpgrade

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

namespace Work.FTS.ClassCHon.SliceMassUpgrade

/-- The general form of the slice-mass up-estimate.  The pointwise estimate `hpt` (an
`ofReal`-level AM–GM Cauchy–Schwarz bound on the slice), the sliver comparison `hcmp`
(which converts the `∂_z`-mass over a sliver into the `D_z`-mass) and the a.e.-measurability
of the `τ`-weighted `∂_z`-density are hypotheses; the weight `τ` itself need *not* be
measurable, which is why the integral of the sum in `hpt` is split on the **second** summand
(whose a.e.-measurability follows from `hmeas` through Tonelli). -/
theorem sliceMass_lintegral_up_gen {F : ℝ → ℝ → ℝ} {τ : ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hτ : ∀ θ ∈ Set.Ioo 0 (π / 2), 0 ≤ τ θ)
    (hmeas : AEMeasurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal (τ p.2 * (Work.Spaces.pz F p.1 p.2) ^ 2))
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod (MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2)))))
    (hpt : ∀ z₁ z₂ θ : ℝ, 0 < z₁ → z₁ ≤ z₂ → θ ∈ Set.Ioo 0 (π / 2) →
      ENNReal.ofReal (τ θ * (F z₂ θ) ^ 2)
        ≤ ENNReal.ofReal 2 * ENNReal.ofReal (τ θ * (F z₁ θ) ^ 2)
          + ENNReal.ofReal 2 * (ENNReal.ofReal (τ θ)
              * (ENNReal.ofReal (z₂ - z₁)
                * ∫⁻ s in Set.Ioo z₁ z₂, ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2))))
    (hcmp : ∀ z₁ s : ℝ, 0 < z₁ → z₁ ≤ s →
      (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2))
        ≤ (ENNReal.ofReal (z₁ ^ 2))⁻¹
          * ∫⁻ θ in Set.Ioo 0 (π / 2),
              ENNReal.ofReal (τ θ * (s * Work.Spaces.pz F s θ) ^ 2))
    {z₁ z₂ : ℝ} (hz₁ : 0 < z₁) (hz₁₂ : z₁ ≤ z₂) :
    (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (τ θ * (F z₂ θ) ^ 2))
      ≤ 2 * (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (τ θ * (F z₁ θ) ^ 2))
        + ENNReal.ofReal (2 * (z₂ - z₁) / z₁ ^ 2)
          * (∫⁻ s in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
              ENNReal.ofReal (τ θ * (s * Work.Spaces.pz F s θ) ^ 2)) := by
  have hz1ne : ENNReal.ofReal (z₁ ^ 2) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero]; linarith [sq_pos_of_pos hz₁]
  -- (0) a.e.-measurability of the `τ`-weighted `∂_z`-density on the sliver `Ioo z₁ z₂`
  have hAEM : AEMeasurable (Function.uncurry (fun s θ : ℝ =>
      ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2)))
      ((volume.restrict (Set.Ioo z₁ z₂)).prod (volume.restrict (Set.Ioo 0 (π / 2)))) := by
    have hle : (volume.restrict (Set.Ioo z₁ z₂)).prod
          (volume.restrict (Set.Ioo 0 (π / 2)))
        ≤ (volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2))) := by
      rw [Measure.prod_restrict, Measure.prod_restrict]
      refine Measure.restrict_mono ?_ le_rfl
      exact Set.prod_mono (fun x hx => lt_of_lt_of_le hz₁ (le_of_lt hx.1)) (subset_refl _)
    exact AEMeasurable.mono_measure hmeas hle
  -- (0') the inner `s`-integral is a.e.-measurable as a function of `θ`
  have hJ' : AEMeasurable (fun θ : ℝ => ∫⁻ s in Set.Ioo z₁ z₂,
      ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2))
      (volume.restrict (Set.Ioo 0 (π / 2))) := hAEM.lintegral_prod_left'
  -- (1) the pointwise identity moving `ofReal ∘ τ` inside the sliver integral
  have hpt_id : ∀ θ ∈ Set.Ioo 0 (π / 2),
      ENNReal.ofReal (τ θ) * (∫⁻ s in Set.Ioo z₁ z₂,
          ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2))
        = ∫⁻ s in Set.Ioo z₁ z₂,
            ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2) := by
    intro θ hθ
    rw [(lintegral_const_mul' (ENNReal.ofReal (τ θ))
      (fun s : ℝ => ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2))
      ENNReal.ofReal_ne_top).symm]
    exact lintegral_congr_ae (Filter.Eventually.of_forall fun s =>
      (ENNReal.ofReal_mul (hτ θ hθ)).symm)
  -- (2) a.e.-measurability of the second summand (`hmeas` + Tonelli; `τ` itself is not
  -- assumed measurable, so this is the only way to split the sum)
  have hb : AEMeasurable (fun θ : ℝ => ENNReal.ofReal 2 * (ENNReal.ofReal (τ θ)
      * (ENNReal.ofReal (z₂ - z₁)
        * ∫⁻ s in Set.Ioo z₁ z₂, ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2))))
      (volume.restrict (Set.Ioo 0 (π / 2))) := by
    have hbase : AEMeasurable (fun θ : ℝ => ENNReal.ofReal 2 * (ENNReal.ofReal (z₂ - z₁)
        * (∫⁻ s in Set.Ioo z₁ z₂,
            ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2))))
        (volume.restrict (Set.Ioo 0 (π / 2))) :=
      AEMeasurable.const_mul
        (AEMeasurable.const_mul hJ' (ENNReal.ofReal (z₂ - z₁))) (ENNReal.ofReal 2)
    refine hbase.congr ?_
    show ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))),
      ENNReal.ofReal 2 * (ENNReal.ofReal (z₂ - z₁)
          * (∫⁻ s in Set.Ioo z₁ z₂,
              ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2)))
        = ENNReal.ofReal 2 * (ENNReal.ofReal (τ θ) * (ENNReal.ofReal (z₂ - z₁)
            * ∫⁻ s in Set.Ioo z₁ z₂, ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2)))
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact Filter.Eventually.of_forall fun θ hθ => by
      show ENNReal.ofReal 2 * (ENNReal.ofReal (z₂ - z₁)
          * (∫⁻ s in Set.Ioo z₁ z₂,
              ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2)))
        = ENNReal.ofReal 2 * (ENNReal.ofReal (τ θ) * (ENNReal.ofReal (z₂ - z₁)
            * ∫⁻ s in Set.Ioo z₁ z₂, ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2)))
      rw [show ENNReal.ofReal (z₂ - z₁)
            * (∫⁻ s in Set.Ioo z₁ z₂,
                ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2))
          = ENNReal.ofReal (τ θ) * (ENNReal.ofReal (z₂ - z₁)
              * ∫⁻ s in Set.Ioo z₁ z₂, ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2)) from by
        rw [← hpt_id θ hθ]; ring]
  -- (3) pointwise bound under the lintegral
  have hstep1 : (∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (τ θ * (F z₂ θ) ^ 2))
      ≤ ∫⁻ θ in Set.Ioo 0 (π / 2),
          (ENNReal.ofReal 2 * ENNReal.ofReal (τ θ * (F z₁ θ) ^ 2)
            + ENNReal.ofReal 2 * (ENNReal.ofReal (τ θ)
              * (ENNReal.ofReal (z₂ - z₁)
                * ∫⁻ s in Set.Ioo z₁ z₂,
                    ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2)))) := by
    refine lintegral_mono_ae ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact Filter.Eventually.of_forall fun θ hθ => hpt z₁ z₂ θ hz₁ hz₁₂ hθ
  -- (4) split the sum (on the second summand) and pull the constants out
  have hsplit : (∫⁻ θ in Set.Ioo 0 (π / 2),
          (ENNReal.ofReal 2 * ENNReal.ofReal (τ θ * (F z₁ θ) ^ 2)
            + ENNReal.ofReal 2 * (ENNReal.ofReal (τ θ)
              * (ENNReal.ofReal (z₂ - z₁)
                * ∫⁻ s in Set.Ioo z₁ z₂,
                    ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2)))))
      = ENNReal.ofReal 2 * (∫⁻ θ in Set.Ioo 0 (π / 2),
          ENNReal.ofReal (τ θ * (F z₁ θ) ^ 2))
        + (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal 2
            * (ENNReal.ofReal (τ θ)
              * (ENNReal.ofReal (z₂ - z₁)
                * ∫⁻ s in Set.Ioo z₁ z₂,
                    ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2)))) := by
    rw [lintegral_add_right' _ hb, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- (5) the second summand: normalise, pull the constants, pull `ofReal ∘ τ` inside
  have hsecond : (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal 2
        * (ENNReal.ofReal (τ θ)
          * (ENNReal.ofReal (z₂ - z₁)
            * ∫⁻ s in Set.Ioo z₁ z₂, ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2))))
      = ENNReal.ofReal 2 * (ENNReal.ofReal (z₂ - z₁)
          * (∫⁻ θ in Set.Ioo 0 (π / 2), ∫⁻ s in Set.Ioo z₁ z₂,
              ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2))) := by
    rw [show (fun θ : ℝ => ENNReal.ofReal 2
          * (ENNReal.ofReal (τ θ)
            * (ENNReal.ofReal (z₂ - z₁)
              * ∫⁻ s in Set.Ioo z₁ z₂, ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2))))
        = fun θ : ℝ => ENNReal.ofReal 2 * (ENNReal.ofReal (z₂ - z₁)
            * (ENNReal.ofReal (τ θ)
              * (∫⁻ s in Set.Ioo z₁ z₂, ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2))))
        from by funext θ; ring]
    have hinner : (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (τ θ)
          * (∫⁻ s in Set.Ioo z₁ z₂, ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2)))
        = (∫⁻ θ in Set.Ioo 0 (π / 2), ∫⁻ s in Set.Ioo z₁ z₂,
            ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2)) := by
      refine lintegral_congr_ae ?_
      show ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))),
        ENNReal.ofReal (τ θ)
            * (∫⁻ s in Set.Ioo z₁ z₂, ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2))
          = ∫⁻ s in Set.Ioo z₁ z₂,
              ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2)
      rw [ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall fun θ hθ => hpt_id θ hθ
    rw [lintegral_const_mul' (ENNReal.ofReal 2) _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' (ENNReal.ofReal (z₂ - z₁)) _ ENNReal.ofReal_ne_top, hinner]
  -- (6) Tonelli
  have hthird : (∫⁻ s in Set.Ioo z₁ z₂, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2))
      = (∫⁻ θ in Set.Ioo 0 (π / 2), ∫⁻ s in Set.Ioo z₁ z₂,
          ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2)) :=
    lintegral_lintegral_swap (μ := volume.restrict (Set.Ioo z₁ z₂))
      (ν := volume.restrict (Set.Ioo 0 (π / 2))) hAEM
  -- (7) bound by the `D_z`-mass
  have hbound : (∫⁻ s in Set.Ioo z₁ z₂, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2))
      ≤ (ENNReal.ofReal (z₁ ^ 2))⁻¹
        * (∫⁻ s in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
            ENNReal.ofReal (τ θ * (s * Work.Spaces.pz F s θ) ^ 2)) := by
    have h1 : (∫⁻ s in Set.Ioo z₁ z₂, ∫⁻ θ in Set.Ioo 0 (π / 2),
          ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2))
        ≤ ∫⁻ s in Set.Ioo z₁ z₂, (ENNReal.ofReal (z₁ ^ 2))⁻¹
            * (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (τ θ
                * (s * Work.Spaces.pz F s θ) ^ 2)) := by
      refine lintegral_mono_ae ?_
      rw [ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall fun s hs => hcmp z₁ s hz₁ (le_of_lt hs.1)
    refine le_trans h1 ?_
    rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hz1ne)]
    exact mul_le_mul_right (lintegral_mono_set
      (fun x hx => lt_of_lt_of_le hz₁ (le_of_lt hx.1))) _
  have hconv : (2 : ℝ≥0∞) * (ENNReal.ofReal (z₂ - z₁)
        * ((ENNReal.ofReal (z₁ ^ 2))⁻¹
          * (∫⁻ s in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
              ENNReal.ofReal (τ θ * (s * Work.Spaces.pz F s θ) ^ 2))))
      = ENNReal.ofReal (2 * (z₂ - z₁) / z₁ ^ 2)
        * (∫⁻ s in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
            ENNReal.ofReal (τ θ * (s * Work.Spaces.pz F s θ) ^ 2)) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity : (0:ℝ) < z₁ ^ 2),
      ENNReal.div_eq_inv_mul, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
      show ENNReal.ofReal (2:ℝ) = (2 : ℝ≥0∞) from by norm_num]
    ring
  refine le_trans hstep1 ?_
  rw [hsplit, hsecond, ← hthird]
  rw [show ENNReal.ofReal (2:ℝ) = (2 : ℝ≥0∞) from by norm_num]
  refine add_le_add le_rfl ?_
  calc (2 : ℝ≥0∞) * (ENNReal.ofReal (z₂ - z₁)
        * (∫⁻ s in Set.Ioo z₁ z₂, ∫⁻ θ in Set.Ioo 0 (π / 2),
            ENNReal.ofReal (τ θ * (Work.Spaces.pz F s θ) ^ 2)))
      ≤ (2 : ℝ≥0∞) * (ENNReal.ofReal (z₂ - z₁)
          * ((ENNReal.ofReal (z₁ ^ 2))⁻¹
            * (∫⁻ s in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
                ENNReal.ofReal (τ θ * (s * Work.Spaces.pz F s θ) ^ 2)))) :=
        mul_le_mul_right (mul_le_mul_right hbound (ENNReal.ofReal (z₂ - z₁))) (2 : ℝ≥0∞)
    _ = ENNReal.ofReal (2 * (z₂ - z₁) / z₁ ^ 2)
          * (∫⁻ s in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
              ENNReal.ofReal (τ θ * (s * Work.Spaces.pz F s θ) ^ 2)) := hconv

end Work.FTS.ClassCHon.SliceMassUpgrade
