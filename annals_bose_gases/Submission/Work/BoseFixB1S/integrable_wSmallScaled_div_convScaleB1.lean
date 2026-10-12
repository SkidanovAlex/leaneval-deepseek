import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.chiSmallB_contDiff_two
import Submission.Work.BoseFixB1S.abs_wSmallScaled_div_convScale_le
import Submission.Work.BoseFixB1S.boxM1Info
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

theorem integrable_wSmallScaled_div_convScaleB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR0 : 0 < R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hR : R ≤ ℓ * d / 16)
    (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0) (h : Work.UBB.ScatSol v) :
    MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z
        / Submission.BoseGases.convScale ℓ z) := by
  have hSpos : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  -- the big-box denominator is `≥ 1/2` on the support of `g₀`
  have hconv : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ R →
      1 / 2 ≤ Submission.BoseGases.convScale ℓ z :=
    fun z hz => Submission.BoseGases.convScale_ge_half_ball hℓ hR0.le hRχ hz
  -- `g₀` vanishes outside `ball 0 R`
  have hsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ →
      Submission.BoseGases.g0 v h z = 0 :=
    fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
  -- `g₀` is integrable
  have hgi : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR0 hv_supp h
  set W : EuclideanSpace ℝ (Fin 3) → ℝ := fun z =>
    Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z
      / Submission.BoseGases.convScale ℓ z with hWdef
  -- pointwise domination by a multiple of `|g₀|`
  have hpt : ∀ z, |W z| ≤
      (2 / Work.SmallBoxSliding.smallConvLower M) * |Submission.BoseGases.g0 v h z| := by
    intro z
    have h1 := abs_wSmallScaled_div_convScale_le (M := M) (R := R) (ℓ := ℓ) (d := d)
      hM hℓ hd hR0 hR hconv h hsupp z
    rw [hWdef]
    refine h1.trans_eq ?_
    ring
  have hcint : MeasureTheory.Integrable
      (fun z => (2 / Work.SmallBoxSliding.smallConvLower M) * |Submission.BoseGases.g0 v h z|) :=
    hgi.abs.const_mul _
  have hmeas : AEMeasurable W MeasureTheory.volume := by
    have hc : Continuous (fun x : EuclideanSpace ℝ (Fin 3) => (ℓ * d)⁻¹ • x) := by fun_prop
    have h1 : AEMeasurable (Submission.BoseGases.convScaleSmall M (ℓ * d)) MeasureTheory.volume :=
      ((Submission.BoseGases.conv3Small_continuous hM).comp hc).aemeasurable
    have h2 : AEMeasurable (Submission.BoseGases.convScale ℓ) MeasureTheory.volume :=
      (Submission.BoseGases.convScale_continuous ℓ).aemeasurable
    have h3 : AEMeasurable (Submission.BoseGases.g0 v h) MeasureTheory.volume :=
      hgi.aestronglyMeasurable.aemeasurable
    rw [hWdef]
    simp only [Submission.BoseGases.wSmallScaled]
    exact (h3.div h1).div h2
  exact MeasureTheory.Integrable.mono' hcint hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall hpt)

end Work.BoseFixB1S
