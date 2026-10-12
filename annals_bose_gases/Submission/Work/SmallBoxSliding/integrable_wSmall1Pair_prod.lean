import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.SmallBoxSliding.abs_wSmall1Pair_le
import Submission.Work.SmallBoxSliding.integrable_mul_prod_restrict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxSliding

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open MeasureTheory
open Submission.BoseGases

theorem integrable_wSmall1Pair_prod {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ (ℓ * d) / 16) (hRχ : R0 ≤ ℓ * chiR0) (z : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.wSmall1Pair h M ℓ d p.1 z p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ))) := by
  have hg0 : Integrable (g0 v h) (volume : Measure ℝ³) := g0_integrable hR0 hv_supp h
  have hGint : Integrable (fun u : ℝ³ => chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • z - u))
      (volume : Measure ℝ³) :=
    (integrable_chiSmall_shift hM ((ℓ * d)⁻¹ • z)).const_mul chiSupAbs
  have hHint : Integrable
      (fun y : ℝ³ => (2 * (chiSupAbs * chiSmallDecay M) * |g0 v h (z - y)|) / smallConvLower M)
      (volume : Measure ℝ³) := by
    have h0 : Integrable (fun y : ℝ³ => (2 * (chiSupAbs * chiSmallDecay M)) * |g0 v h (z - y)|)
        (volume : Measure ℝ³) :=
      (hg0.abs.comp_sub_left z).const_mul (2 * (chiSupAbs * chiSmallDecay M))
    exact h0.div_const (smallConvLower M)
  have hdom' := integrable_mul_prod_restrict (μ := (volume : Measure ℝ³)) (ν := (volume : Measure ℝ³))
    (s := Set.univ) (t := acube ℓ) hGint hHint
  have hdom : Integrable (fun p : ℝ³ × ℝ³ =>
      (chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • z - p.1)) *
        ((2 * (chiSupAbs * chiSmallDecay M) * |g0 v h (z - p.2)|) / smallConvLower M))
      ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).restrict (acube ℓ))) := by
    simpa [Measure.restrict_univ] using hdom'
  have hnum : AEMeasurable (fun y : ℝ³ => g0 v h (z - y))
      ((volume : Measure ℝ³).restrict (acube ℓ)) :=
    ((hg0.comp_sub_left z).integrableOn (s := acube ℓ)).aemeasurable
  have hden : Continuous (fun y : ℝ³ => convScaleSmall M (ℓ * d) (z - y)) := by
    have hcont : Continuous (fun y : ℝ³ => (ℓ * d)⁻¹ • (z - y)) :=
      (continuous_const.sub continuous_id).const_smul ((ℓ * d)⁻¹)
    have h3 : Continuous (fun y : ℝ³ => conv3Small M ((ℓ * d)⁻¹ • (z - y))) :=
      (conv3Small_continuous hM).comp hcont
    simpa [convScaleSmall] using h3
  have hW : AEStronglyMeasurable
      (fun y : ℝ³ => wSmallScaled M (ℓ * d) (g0 v h) (z - y))
      ((volume : Measure ℝ³).restrict (acube ℓ)) := by
    have hq : AEMeasurable
        (fun y : ℝ³ => g0 v h (z - y) / convScaleSmall M (ℓ * d) (z - y))
        ((volume : Measure ℝ³).restrict (acube ℓ)) :=
      hnum.div hden.aemeasurable
    simpa [wSmallScaled] using hq.aestronglyMeasurable
  have hWc : AEStronglyMeasurable
      (fun p : ℝ³ × ℝ³ => wSmallScaled M (ℓ * d) (g0 v h) (z - p.2)
        / convScale ℓ (z - p.2))
      ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).restrict (acube ℓ))) := by
    have hcv : AEMeasurable (fun p : ℝ³ × ℝ³ => convScale ℓ (z - p.2))
        ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).restrict (acube ℓ))) :=
      ((convScale_continuous ℓ).comp (continuous_const.sub continuous_snd)).aemeasurable
    exact ((hW.comp_snd).aemeasurable.div hcv).aestronglyMeasurable
  have hA : Continuous (fun p : ℝ³ × ℝ³ => chiSmallB M ℓ d p.1 z) := by
    have h2 : Continuous (fun p : ℝ³ × ℝ³ => chiSmall M ((ℓ * d)⁻¹ • z - p.1)) :=
      (chiSmall_continuous hM).comp (continuous_const.sub continuous_fst)
    exact continuous_const.mul h2
  have hC : Continuous (fun p : ℝ³ × ℝ³ => chiSmallB M ℓ d p.1 p.2) := by
    have h1 : Continuous (fun p : ℝ³ × ℝ³ => chiScale ℓ p.2) :=
      (chiScale_continuous ℓ).comp continuous_snd
    have h2 : Continuous (fun p : ℝ³ × ℝ³ => chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1)) :=
      (chiSmall_continuous hM).comp
        ((continuous_snd.const_smul ((ℓ * d)⁻¹)).sub continuous_fst)
    have hgoal : (fun p : ℝ³ × ℝ³ => chiSmallB M ℓ d p.1 p.2)
        = fun p : ℝ³ × ℝ³ => chiScale ℓ p.2 * chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1) := rfl
    rw [hgoal]
    exact h1.mul h2
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ³ × ℝ³ => wSmall1Pair h M ℓ d p.1 z p.2)
      ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).restrict (acube ℓ))) := by
    have hmain : AEStronglyMeasurable
        (fun p : ℝ³ × ℝ³ => chiSmallB M ℓ d p.1 z
          * (wSmallScaled M (ℓ * d) (g0 v h) (z - p.2) / convScale ℓ (z - p.2))
          * chiSmallB M ℓ d p.1 p.2)
        ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).restrict (acube ℓ))) :=
      (hA.aestronglyMeasurable.mul hWc).mul hC.aestronglyMeasurable
    have hgoal : (fun p : ℝ³ × ℝ³ => wSmall1Pair h M ℓ d p.1 z p.2)
        = fun p : ℝ³ × ℝ³ => chiSmallB M ℓ d p.1 z
            * (wSmallScaled M (ℓ * d) (g0 v h) (z - p.2) / convScale ℓ (z - p.2))
            * chiSmallB M ℓ d p.1 p.2 := rfl
    rw [hgoal]
    exact hmain
  refine Integrable.mono' hdom hmeas ?_
  filter_upwards with p
  rw [Real.norm_eq_abs]
  calc |wSmall1Pair h M ℓ d p.1 z p.2|
      ≤ chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • z - p.1)
          * (2 * (chiSupAbs * chiSmallDecay M) * |g0 v h (z - p.2)|) / smallConvLower M :=
        abs_wSmall1Pair_le hv_supp hR0 h hM hℓ hd hR hRχ p.1 z p.2
    _ = chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • z - p.1)
          * (2 * (chiSupAbs * chiSmallDecay M) * |g0 v h (z - p.2)| / smallConvLower M) := by ring

end Work.SmallBoxSliding
