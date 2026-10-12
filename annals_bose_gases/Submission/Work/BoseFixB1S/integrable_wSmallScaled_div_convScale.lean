import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxSliding.qLHSBAux
import Submission.Work.SmallBoxSliding.wSmall1Pair_mass_nonneg
import Submission.Work.UBB.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory

/-- The scaled self-convolution denominator `convScaleSmall M c` is continuous
(it is `conv3Small M` composed with `x ↦ c⁻¹ • x`). -/
lemma continuous_convScaleSmall (M : ℕ) (hM : 1 ≤ M) (c : ℝ) :
    Continuous (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.convScaleSmall M c z) := by
  unfold Submission.BoseGases.convScaleSmall
  exact (Submission.BoseGases.conv3Small_continuous hM).comp (by fun_prop)

/-- The product of the two renormalisation denominators
`convScaleSmall M (ℓ*d) · convScale ℓ` is continuous. -/
lemma continuous_convScaleSmall_mul_convScale {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ) :
    Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.convScaleSmall M (ℓ * d) z * Submission.BoseGases.convScale ℓ z) :=
  (continuous_convScaleSmall M hM (ℓ * d)).mul (Submission.BoseGases.convScale_continuous ℓ)

/-- The renormalised kernel `wSmallScaled M (ℓ*d) (g0 v h)` is a.e. strongly measurable
whenever `g0 v h` is integrable (the denominator is continuous, hence measurable). -/
lemma aestronglyMeasurable_wSmallScaled_g0 {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {ℓ d : ℝ} {M : ℕ} (hM : 1 ≤ M) (h : Work.UBB.ScatSol v)
    (hGint : MeasureTheory.Integrable (Submission.BoseGases.g0 v h)) :
    MeasureTheory.AEStronglyMeasurable
      (fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z) := by
  have hnum : AEMeasurable (Submission.BoseGases.g0 v h)
      (volume : Measure (EuclideanSpace ℝ (Fin 3))) := hGint.aemeasurable
  have hden : AEMeasurable
      (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.convScaleSmall M (ℓ * d) z)
      (volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
    (continuous_convScaleSmall M hM (ℓ * d)).aemeasurable
  have hquot : AEMeasurable
      (fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.g0 v h z / Submission.BoseGases.convScaleSmall M (ℓ * d) z)
      (volume : Measure (EuclideanSpace ℝ (Fin 3))) := hnum.div hden
  simpa only [Submission.BoseGases.wSmallScaled] using hquot.aestronglyMeasurable

theorem integrable_wSmallScaled_div_convScale {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ d c : ℝ} {M : ℕ}
    (hM : 1 ≤ M) (hℓ : 0 < ℓ) (hd : 0 < d) (h : Work.UBB.ScatSol v)
    (hGint : MeasureTheory.Integrable (Submission.BoseGases.g0 v h))
    (hdle : ∀ z : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z
          / Submission.BoseGases.convScale ℓ z| ≤ c * |Submission.BoseGases.g0 v h z|)
    (hc : 0 ≤ c) :
    MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z
        / Submission.BoseGases.convScale ℓ z) := by
  -- a.e. strong measurability of the quotient: numerator a.e. measurable, denominator continuous
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z
          / Submission.BoseGases.convScale ℓ z) := by
    have hden : AEMeasurable
        (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.convScale ℓ z)
        (volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
      (Submission.BoseGases.convScale_continuous ℓ).aemeasurable
    have hquot : AEMeasurable
        (fun z : EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z
            / Submission.BoseGases.convScale ℓ z)
        (volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
      (aestronglyMeasurable_wSmallScaled_g0 (ℓ := ℓ) (d := d) hM h hGint).aemeasurable.div hden
    exact hquot.aestronglyMeasurable
  -- the dominating integrable function `c * ‖g₀‖`
  have hbound : MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => c * ‖Submission.BoseGases.g0 v h z‖) :=
    hGint.norm.const_mul c
  refine hbound.mono' haesm ?_
  filter_upwards with z
  simpa only [Real.norm_eq_abs] using hdle z

end Work.BoseFixB1S
