import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.pairMassB_defs
import Submission.Work.BoseFixB1.perBoxF_flat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

/-- **Domination of the renormalised fibre quotient by the numerator.**

For a numerator `f` supported in `ball 0 R` with `R ≤ (ℓd)/16` (so that the small-scale
denominator `(χ_M⋆χ_M)(·/(ℓd))` is `≥ smallConvLower M` on the support,
`Work.SmallBoxSliding.abs_wSmallScaled_le`) and `R ≤ ℓ·chiR0` (so that the `ℓ`-scale denominator
`(χ⋆χ)(·/ℓ)` is `≥ 1/2` on the support, `Submission.BoseGases.abs_inv_convScale_le_two`),

  `|f z / ((χ_M⋆χ_M)(z/(ℓd))·(χ⋆χ)(z/ℓ))| ≤ (2/smallConvLower M)·|f z|`. -/
lemma abs_div_convScaleSmall_mul_convScale_le {M : ℕ} (hM : 1 ≤ M) {ℓ d R : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) (hR : R ≤ ℓ * d / 16)
    (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hfsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → f z = 0)
    (z : EuclideanSpace ℝ (Fin 3)) :
    |f z / (Submission.BoseGases.convScaleSmall M (ℓ * d) z * Submission.BoseGases.convScale ℓ z)|
      ≤ (2 / Work.SmallBoxSliding.smallConvLower M) * |f z| := by
  rw [← Work.BoseFixB1.wSmallScaled_div_convScale_eq M ℓ d f z]
  by_cases hf : f z = 0
  · have hw : Submission.BoseGases.wSmallScaled M (ℓ * d) f z = 0 := by
      simp [Submission.BoseGases.wSmallScaled, hf]
    rw [hw, hf]
    simp
  · have hlt : ‖z‖ < R := by
      by_contra hcon
      exact hf (hfsupp z (le_of_not_gt hcon))
    have hcpos : 0 < ℓ * d := mul_pos hℓ hd
    have h1 : |Submission.BoseGases.wSmallScaled M (ℓ * d) f z|
        ≤ |f z| / Work.SmallBoxSliding.smallConvLower M :=
      Work.SmallBoxSliding.abs_wSmallScaled_le hM hcpos hfsupp hR z
    have h2 : |(Submission.BoseGases.convScale ℓ z)⁻¹| ≤ 2 :=
      Submission.BoseGases.abs_inv_convScale_le_two hℓ hRχ (le_of_lt hlt)
    have hSlpos : 0 < Work.SmallBoxSliding.smallConvLower M :=
      Work.SmallBoxSliding.smallConvLower_pos M
    rw [div_eq_mul_inv, abs_mul]
    calc |Submission.BoseGases.wSmallScaled M (ℓ * d) f z| * |(Submission.BoseGases.convScale ℓ z)⁻¹|
        ≤ (|f z| / Work.SmallBoxSliding.smallConvLower M) * 2 :=
          mul_le_mul h1 h2 (abs_nonneg _) (div_nonneg (abs_nonneg _) hSlpos.le)
      _ = (2 / Work.SmallBoxSliding.smallConvLower M) * |f z| := by ring

/-- **Pointwise domination of the lag-variable localised pair kernel.**

`|χ_{B(u)}(x)·(v z/E z)·χ_{B(u)}(x−z)| ≤ |χ_{B(u)}(x)| · ((2/smallConvLower M)·chiSupAbs·
chiSmallDecay M · |v z|)`: the first cutoff factor is kept (it is the integrable function of `x`),
the second is bounded by its sup `chiSupAbs·chiSmallDecay M`
(`Work.SmallBoxSliding.abs_chiSmallB_le` + `Submission.BoseGases.chiSmall_decay_coord_le_decay`),
and the quotient by the renormalisation denominators by
`abs_div_convScaleSmall_mul_convScale_le`. -/
lemma abs_psiPairKernel_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ} {M : ℕ} (hM : 1 ≤ M)
    {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hR : R0 ≤ ℓ * d / 16)
    (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0) (u : EuclideanSpace ℝ (Fin 3))
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0)
    (p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    ‖Work.BoseFixB1.psiPairKernel M ℓ d u v p‖
      ≤ |Submission.BoseGases.chiSmallB M ℓ d u p.1| *
        (((2 / Work.SmallBoxSliding.smallConvLower M) *
          (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)) * |v p.2|) := by
  obtain ⟨x, z⟩ := p
  have hsupnn : 0 ≤ Submission.BoseGases.chiSupAbs := Submission.BoseGases.chiSupAbs_nonneg
  have hDecnn : 0 ≤ Submission.BoseGases.chiSmallDecay M :=
    Submission.BoseGases.chiSmallDecay_nonneg M
  have hSlpos : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  have hfsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R0 ≤ ‖z‖ → v z = 0 :=
    fun z hz => Work.SmallBoxSliding.eq_zero_of_tsupport_subset_ball hv_supp hz
  rw [Work.BoseFixB1.psiPairKernel_apply, Real.norm_eq_abs, abs_mul, abs_mul]
  have hB : |v z / (Submission.BoseGases.convScaleSmall M (ℓ * d) z *
        Submission.BoseGases.convScale ℓ z)| ≤
      (2 / Work.SmallBoxSliding.smallConvLower M) * |v z| :=
    abs_div_convScaleSmall_mul_convScale_le hM hℓ hd hR hRχ hfsupp z
  have hC : |Submission.BoseGases.chiSmallB M ℓ d u (x - z)| ≤
      Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M := by
    refine le_trans (Work.SmallBoxSliding.abs_chiSmallB_le hM u (x - z)) ?_
    exact mul_le_mul_of_nonneg_left
      (le_trans (le_abs_self _) (Submission.BoseGases.chiSmall_decay_coord_le_decay hM _)) hsupnn
  have hBnn : 0 ≤ (2 / Work.SmallBoxSliding.smallConvLower M) * |v z| :=
    mul_nonneg (div_nonneg (by norm_num) hSlpos.le) (abs_nonneg _)
  have hstep : |v z / (Submission.BoseGases.convScaleSmall M (ℓ * d) z *
        Submission.BoseGases.convScale ℓ z)| *
        |Submission.BoseGases.chiSmallB M ℓ d u (x - z)|
      ≤ ((2 / Work.SmallBoxSliding.smallConvLower M) * |v z|) *
        (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) :=
    mul_le_mul hB hC (abs_nonneg _) hBnn
  calc (|Submission.BoseGases.chiSmallB M ℓ d u x| *
          |v z / (Submission.BoseGases.convScaleSmall M (ℓ * d) z *
            Submission.BoseGases.convScale ℓ z)|) *
          |Submission.BoseGases.chiSmallB M ℓ d u (x - z)|
      = |Submission.BoseGases.chiSmallB M ℓ d u x| *
          (|v z / (Submission.BoseGases.convScaleSmall M (ℓ * d) z *
            Submission.BoseGases.convScale ℓ z)| *
            |Submission.BoseGases.chiSmallB M ℓ d u (x - z)|) := by ring
    _ ≤ |Submission.BoseGases.chiSmallB M ℓ d u x| *
          (((2 / Work.SmallBoxSliding.smallConvLower M) * |v z|) *
            (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)) :=
        mul_le_mul_of_nonneg_left hstep (abs_nonneg _)
    _ = |Submission.BoseGases.chiSmallB M ℓ d u x| *
          (((2 / Work.SmallBoxSliding.smallConvLower M) *
            (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)) * |v z|) := by
        ring

/-- Intended module `Submission.Work.BoseFixB1.integrable_psiPairKernel`, namespace `Work.BoseFixB1`.
The substituted (lag-variable) localised pair kernel with numerator `v` is integrable on the
product measure `volume.prod volume`.  Route: `Work.SmallBoxSliding.abs_chiSmallB_le` bounds
`|chiB x| ≤ chiSupAbs * chiSmall M ((ℓd)⁻¹ • x - u)` and `|chiB (x-z)| ≤ chiSupAbs * chiSmallDecay M`;
`Work.SmallBoxSliding.abs_wSmallScaled_le` + `Submission.BoseGases.abs_inv_convScale_le_two` bound
`|v z / E z| ≤ 2|v z| / smallConvLower M` (with `E z = convScaleSmall M (ℓd) z * convScale ℓ z`);
then `Integrable.mul_prod` of the two one-variable majorants (the first is continuous with compact
support, the second comes from `hv1` via `MeasureTheory.memLp_one_iff_integrable`), and
`MeasureTheory.Integrable.mono'`. -/
theorem integrable_psiPairKernel {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ} (hR0 : 0 < R0)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0)
    (hv1 : MeasureTheory.MemLp v 1) {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.Integrable (Work.BoseFixB1.psiPairKernel M ℓ d u v)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  have hvint : MeasureTheory.Integrable v
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
    MeasureTheory.memLp_one_iff_integrable.mp hv1
  -- the one-variable majorant in the `x`-slot: the cutoff, continuous with compact support
  have hχBint : MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin 3) => |Submission.BoseGases.chiSmallB M ℓ d u x|)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
    ((Submission.BoseGases.chiSmallB_continuous hM hℓ hd u).integrable_of_hasCompactSupport
      (Submission.BoseGases.chiSmallB_hasCompactSupport hM hℓ u)).abs
  -- the one-variable majorant in the `z`-slot: a multiple of `|v|`
  have hKint : MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) =>
        ((2 / Work.SmallBoxSliding.smallConvLower M) *
          (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)) * |v z|)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
    hvint.abs.const_mul _
  have hdom : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        |Submission.BoseGases.chiSmallB M ℓ d u p.1| *
          (((2 / Work.SmallBoxSliding.smallConvLower M) *
            (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)) * |v p.2|))
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        MeasureTheory.volume) :=
    hχBint.mul_prod hKint
  -- AE strong measurability of the kernel
  have hmeas : MeasureTheory.AEStronglyMeasurable (Work.BoseFixB1.psiPairKernel M ℓ d u v)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        MeasureTheory.volume) := by
    have h1 : AEMeasurable
        (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.chiSmallB M ℓ d u p.1)
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          MeasureTheory.volume) :=
      ((Submission.BoseGases.chiSmallB_continuous hM hℓ hd u).comp
        continuous_fst).aemeasurable
    have h3 : AEMeasurable
        (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.chiSmallB M ℓ d u (p.1 - p.2))
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          MeasureTheory.volume) :=
      ((Submission.BoseGases.chiSmallB_continuous hM hℓ hd u).comp
        (continuous_fst.sub continuous_snd)).aemeasurable
    have h2 : AEMeasurable
        (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          v p.2 / (Submission.BoseGases.convScaleSmall M (ℓ * d) p.2 *
            Submission.BoseGases.convScale ℓ p.2))
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          MeasureTheory.volume) := by
      have hv : AEMeasurable
          (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => v p.2)
          ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
            MeasureTheory.volume) :=
        hv1.aestronglyMeasurable.comp_snd.aemeasurable
      have hE : AEMeasurable
          (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
            Submission.BoseGases.convScaleSmall M (ℓ * d) p.2 *
              Submission.BoseGases.convScale ℓ p.2)
          ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
            MeasureTheory.volume) := by
        have hc1 : Continuous
            (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
              Submission.BoseGases.convScaleSmall M (ℓ * d) p.2) := by
          have hcont : Continuous
              (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
                (ℓ * d)⁻¹ • p.2) := continuous_snd.const_smul ((ℓ * d)⁻¹)
          simpa only [Submission.BoseGases.convScaleSmall, Function.comp_def] using
            (Submission.BoseGases.conv3Small_continuous hM).comp hcont
        have hc2 : Continuous
            (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
              Submission.BoseGases.convScale ℓ p.2) := by
          have hcont : Continuous
              (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
                ℓ⁻¹ • p.2) := continuous_snd.const_smul (ℓ⁻¹)
          simpa only [Submission.BoseGases.convScale, Function.comp_def] using
            (Submission.BoseGases.conv_contDiff.continuous).comp hcont
        exact (hc1.mul hc2).aemeasurable
      exact hv.div hE
    exact ((h1.mul h2).mul h3).aestronglyMeasurable
  refine MeasureTheory.Integrable.mono' hdom hmeas ?_
  filter_upwards with p
  exact abs_psiPairKernel_le hM hℓ hd hR hRχ u hv_supp p

end Work.BoseFixB1
