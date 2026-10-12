import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.wSmallPair_integral_eq_autocorr
import Submission.Work.BoseFixB3.CS.Pieces.convScale_ge_of_norm_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B

open MeasureTheory Metric
open scoped Real BigOperators ENNReal Topology

/-- `wSmall1Pair` with numerator `g₀ v h` is *by definition* `wSmallPair` with numerator
`g₀ v h`; recorded so that the two spellings can be interchanged by rewriting. -/
private lemma wSmall1Pair_eq_wSmallPair {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) (M : ℕ) (ℓ d : ℝ) (u x y : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.wSmall1Pair h M ℓ d u x y
      = Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) x y := rfl

/-- **Integrability of the lag-variable localised kernel** with numerator `g₀ v h`, in the regime
`R ≤ ℓd/16`, `R ≤ ℓ/16` (no `chiR0` hypothesis), at an *arbitrary* sliding position `u`.

This is the `u`-general form of the private `integrable_psiPairKernel_g0` of
`Submission/Work/BoseFixB1S/w1MassB_zero_eq_single.lean`; the pointwise domination uses only the
`u`-general bound `Work.SmallBoxSliding.abs_chiSmallB_le hM u`.

The pointwise domination is `|χ_{B(u)}(x)·(g₀ z / E z)·χ_{B(u)}(x−z)| ≤ |χ_{B(u)}(x)|·(C·|g₀ z|)`
with `C = ((smallConvLower M)·c₀)⁻¹·(chiSupAbs·chiSmallDecay M)`, where `c₀` is the `ℓ`-uniform
lower bound for `convScale ℓ` on `ball 0 (ℓ/8)` and `smallConvLower M` the (coordinate-polydisc)
lower bound of `(χ_M⋆χ_M)`; the majorant is the product of an integrable function of `x`
(the compactly supported cutoff) and an integrable multiple of `|g₀|`. -/
private lemma integrable_psiPairKernel_g0_gen {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR1 : R ≤ ℓ * d / 16) (hR2 : R ≤ ℓ / 16) (u : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.Integrable
      (Work.BoseFixB1.psiPairKernel M ℓ d u (Submission.BoseGases.g0 v h))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  obtain ⟨c₀, hc₀pos, hc₀⟩ := Work.BoseFixB3.CS.Pieces.convScale_ge_of_norm_le
  have hsmallpos : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  -- the `(ℓd)`-scale denominator on the support of `g₀`
  have hSM : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ R →
      Work.SmallBoxSliding.smallConvLower M ≤ Submission.BoseGases.convScaleSmall M (ℓ * d) z := by
    intro z hz
    have hcpos : 0 < ℓ * d := mul_pos hℓ hd
    have hnorm : ‖(ℓ * d)⁻¹ • z‖ ≤ 1 / 16 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcpos)]
      have h1 : (ℓ * d)⁻¹ * ‖z‖ ≤ (ℓ * d)⁻¹ * R :=
        mul_le_mul_of_nonneg_left hz (inv_pos.mpr hcpos).le
      have h2 : (ℓ * d)⁻¹ * R ≤ (ℓ * d)⁻¹ * ((ℓ * d) / 16) :=
        mul_le_mul_of_nonneg_left hR1 (inv_pos.mpr hcpos).le
      have h3 : (ℓ * d)⁻¹ * ((ℓ * d) / 16) = 1 / 16 := by field_simp
      linarith [h1, h2, h3]
    exact Work.SmallBoxSliding.conv3Small_coord_lower hM _
      (fun j => le_trans (Submission.BoseGases.coord_abs_le_norm _ j) hnorm)
  -- the `ℓ`-scale denominator on the support of `g₀`
  have hCV : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ R →
      c₀ ≤ Submission.BoseGases.convScale ℓ z := by
    intro z hz
    refine hc₀ ℓ hℓ z (le_trans hz ?_)
    linarith
  -- the pointwise quotient bound
  have hquot : ∀ z : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.g0 v h z /
        (Submission.BoseGases.convScaleSmall M (ℓ * d) z * Submission.BoseGases.convScale ℓ z)|
      ≤ (Work.SmallBoxSliding.smallConvLower M * c₀)⁻¹ * |Submission.BoseGases.g0 v h z| := by
    intro z
    by_cases hz : ‖z‖ ≤ R
    · have h1 := hSM z hz
      have h2 := hCV z hz
      have h1nn : 0 ≤ Submission.BoseGases.convScaleSmall M (ℓ * d) z := le_trans hsmallpos.le h1
      have h2nn : 0 ≤ Submission.BoseGases.convScale ℓ z := le_trans hc₀pos.le h2
      have hden : Work.SmallBoxSliding.smallConvLower M * c₀
          ≤ Submission.BoseGases.convScaleSmall M (ℓ * d) z * Submission.BoseGases.convScale ℓ z :=
        mul_le_mul h1 h2 hc₀pos.le h1nn
      have hdpos : 0 < Work.SmallBoxSliding.smallConvLower M * c₀ := mul_pos hsmallpos hc₀pos
      rw [abs_div, abs_of_nonneg (le_trans hdpos.le hden), inv_mul_eq_div]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hdpos hden
    · have hz0 : Submission.BoseGases.g0 v h z = 0 :=
        Submission.BoseGases.g0_zero_of_norm_ge hv_supp (le_of_lt (lt_of_not_ge hz)) h
      simp [hz0]
  -- the pointwise kernel domination
  have hker : ∀ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
      ‖Work.BoseFixB1.psiPairKernel M ℓ d u (Submission.BoseGases.g0 v h) p‖
        ≤ |Submission.BoseGases.chiSmallB M ℓ d u p.1| *
            (((Work.SmallBoxSliding.smallConvLower M * c₀)⁻¹ *
              (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)) *
              |Submission.BoseGases.g0 v h p.2|) := by
    intro p
    obtain ⟨x, z⟩ := p
    have hsupnn : 0 ≤ Submission.BoseGases.chiSupAbs := Submission.BoseGases.chiSupAbs_nonneg
    have hB := hquot z
    have hC : |Submission.BoseGases.chiSmallB M ℓ d u (x - z)| ≤
        Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M := by
      refine le_trans (Work.SmallBoxSliding.abs_chiSmallB_le hM u (x - z)) ?_
      exact mul_le_mul_of_nonneg_left
        (le_trans (le_abs_self _) (Submission.BoseGases.chiSmall_decay_coord_le_decay hM _)) hsupnn
    rw [Work.BoseFixB1.psiPairKernel_apply, Real.norm_eq_abs, abs_mul, abs_mul]
    have hBnn : 0 ≤ (Work.SmallBoxSliding.smallConvLower M * c₀)⁻¹ *
        |Submission.BoseGases.g0 v h z| :=
      mul_nonneg (inv_nonneg.mpr (mul_pos (Work.SmallBoxSliding.smallConvLower_pos M) hc₀pos).le)
        (abs_nonneg _)
    have hstep : |Submission.BoseGases.g0 v h z /
          (Submission.BoseGases.convScaleSmall M (ℓ * d) z * Submission.BoseGases.convScale ℓ z)| *
          |Submission.BoseGases.chiSmallB M ℓ d u (x - z)|
        ≤ ((Work.SmallBoxSliding.smallConvLower M * c₀)⁻¹ * |Submission.BoseGases.g0 v h z|) *
          (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) :=
      mul_le_mul hB hC (abs_nonneg _) hBnn
    calc |Submission.BoseGases.chiSmallB M ℓ d u x| *
            |Submission.BoseGases.g0 v h z /
              (Submission.BoseGases.convScaleSmall M (ℓ * d) z * Submission.BoseGases.convScale ℓ z)| *
            |Submission.BoseGases.chiSmallB M ℓ d u (x - z)|
        = |Submission.BoseGases.chiSmallB M ℓ d u x| *
            (|Submission.BoseGases.g0 v h z /
              (Submission.BoseGases.convScaleSmall M (ℓ * d) z * Submission.BoseGases.convScale ℓ z)| *
              |Submission.BoseGases.chiSmallB M ℓ d u (x - z)|) := by ring
      _ ≤ |Submission.BoseGases.chiSmallB M ℓ d u x| *
            (((Work.SmallBoxSliding.smallConvLower M * c₀)⁻¹ * |Submission.BoseGases.g0 v h z|) *
              (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)) :=
          mul_le_mul_of_nonneg_left hstep (abs_nonneg _)
      _ = |Submission.BoseGases.chiSmallB M ℓ d u x| *
            (((Work.SmallBoxSliding.smallConvLower M * c₀)⁻¹ *
              (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)) *
              |Submission.BoseGases.g0 v h z|) := by ring
  -- the majorant is integrable
  have hχBint : MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin 3) => |Submission.BoseGases.chiSmallB M ℓ d u x|)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
    ((Submission.BoseGases.chiSmallB_continuous hM hℓ hd u).integrable_of_hasCompactSupport
      (Submission.BoseGases.chiSmallB_hasCompactSupport hM hℓ u)).abs
  have hKint : MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) =>
        ((Work.SmallBoxSliding.smallConvLower M * c₀)⁻¹ *
          (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)) *
          |Submission.BoseGases.g0 v h z|)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
    ((Submission.BoseGases.g0_integrable hR hv_supp h).abs).const_mul _
  have hdom : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        |Submission.BoseGases.chiSmallB M ℓ d u p.1| *
          (((Work.SmallBoxSliding.smallConvLower M * c₀)⁻¹ *
            (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)) *
            |Submission.BoseGases.g0 v h p.2|))
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        MeasureTheory.volume) :=
    hχBint.mul_prod hKint
  -- AE strong measurability of the kernel
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (Work.BoseFixB1.psiPairKernel M ℓ d u (Submission.BoseGases.g0 v h))
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        MeasureTheory.volume) := by
    have h1 : AEMeasurable
        (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.chiSmallB M ℓ d u p.1)
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          MeasureTheory.volume) :=
      ((Submission.BoseGases.chiSmallB_continuous hM hℓ hd u).comp continuous_fst).aemeasurable
    have h3 : AEMeasurable
        (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.chiSmallB M ℓ d u (p.1 - p.2))
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          MeasureTheory.volume) :=
      ((Submission.BoseGases.chiSmallB_continuous hM hℓ hd u).comp
        (continuous_fst.sub continuous_snd)).aemeasurable
    have h2 : AEMeasurable
        (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.g0 v h p.2 / (Submission.BoseGases.convScaleSmall M (ℓ * d) p.2 *
            Submission.BoseGases.convScale ℓ p.2))
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          MeasureTheory.volume) := by
      have hg : AEMeasurable
          (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
            Submission.BoseGases.g0 v h p.2)
          ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
            MeasureTheory.volume) :=
        (Submission.BoseGases.g0_integrable hR hv_supp h).aestronglyMeasurable.comp_snd.aemeasurable
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
      exact hg.div hE
    exact AEMeasurable.aestronglyMeasurable ((h1.mul h2).mul h3)
  refine MeasureTheory.Integrable.mono' hdom hmeas ?_
  filter_upwards with p
  exact hker p

-- The general-`u` version of `Work.BoseFixB1S.w1MassB_zero_eq_single`. The proof is a
-- verbatim copy of the private `integrable_psiPairKernel_g0` in
-- `Submission/Work/BoseFixB1S/w1MassB_zero_eq_single.lean` with the sliding position `u`
-- kept general (its pointwise domination only changes `chiSmallB M ℓ d 0` to `chiSmallB M ℓ d u`,
-- for which `Work.SmallBoxSliding.abs_chiSmallB_le hM u` is the u-general form), followed by
-- `Work.BoseFixB1.wSmallPair_integral_eq_autocorr` and `rfl` (`wSmall1Pair = wSmallPair (g0 v h)`).
theorem w1MassB_eq_autocorr_gen {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR1 : R ≤ ℓ * d / 16) (hR2 : R ≤ ℓ / 16) (u : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixB1.w1MassB h M ℓ d u
      = ∫ z : EuclideanSpace ℝ (Fin 3),
          (Submission.BoseGases.g0 v h z
              / (Submission.BoseGases.convScaleSmall M (ℓ * d) z
                  * Submission.BoseGases.convScale ℓ z))
            * Work.BoseFixB1.autocorr (M := M) ℓ d u z := by
  have hI : MeasureTheory.Integrable
      (Work.BoseFixB1.psiPairKernel M ℓ d u (Submission.BoseGases.g0 v h))
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    integrable_psiPairKernel_g0_gen (v := v) (R := R) h hR hv_supp (M := M) hM (ℓ := ℓ) (d := d)
      hℓ hd hR1 hR2 u
  have hdef : Work.BoseFixB1.w1MassB h M ℓ d u
      = ∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) x y := rfl
  rw [hdef, Work.BoseFixB1.wSmallPair_integral_eq_autocorr (M := M) (ℓ := ℓ) (d := d)
    (f := Submission.BoseGases.g0 v h) (u := u) hI]

end Work.BoseFixB1B
