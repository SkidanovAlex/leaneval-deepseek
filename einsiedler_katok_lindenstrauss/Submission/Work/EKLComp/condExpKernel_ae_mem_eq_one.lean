import Mathlib
import Submission.Work.EKLComp.LeafDefs

namespace Work.EKLComp

open MeasureTheory

/-- The conditional kernel `condExpKernel μ 𝔪.m` is carried by the `𝔪.m`-measurable set `B`,
almost everywhere on `B`.

Indeed `μ[1_B | 𝔪.m] = 1_B` because `1_B` is `𝔪.m`-measurable and `μ` is finite, and
`condExp_ae_eq_integral_condExpKernel` identifies `μ[1_B | 𝔪.m] x` with `∫ y, 1_B y ∂(κ x)`,
i.e. with `(κ x).real B`.  On `B` this is `1`, so `(κ x) B = 1`. -/
theorem condExpKernel_ae_mem_eq_one (𝔪 : Work.EKLComp.SigAlg)
    [StandardBorelSpace Work.EKLContract.X3] (hm : 𝔪.m ≤ Work.EKLComp.borelX3)
    (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsFiniteMeasure μ]
    {B : Set Work.EKLContract.X3} (hB : @MeasurableSet Work.EKLContract.X3 𝔪.m B) :
    ∀ᵐ x ∂μ, x ∈ B → ProbabilityTheory.condExpKernel μ 𝔪.m x B = 1 := by
  -- `B` is Borel since `𝔪.m ≤ borel X₃` and the ambient σ-algebra is the Borel one.
  have hBmeas : MeasurableSet B := hm B hB
  -- The indicator of `B`, an integrable `𝔪.m`-measurable function.
  have hf_int : Integrable (B.indicator (1 : Work.EKLContract.X3 → ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator hBmeas
  have hf_sm : StronglyMeasurable[𝔪.m] (B.indicator (1 : Work.EKLContract.X3 → ℝ)) :=
    (measurable_const.indicator hB).stronglyMeasurable
  -- Conditional expectation of an `𝔪.m`-measurable function is the function itself.
  have h1 := MeasureTheory.condExp_of_stronglyMeasurable (μ := μ) hm hf_sm hf_int
  -- The conditional expectation is the integral against the conditional kernel.
  have h2 := ProbabilityTheory.condExp_ae_eq_integral_condExpKernel (μ := μ) hm hf_int
  filter_upwards [h2] with x hx2
  intro hxB
  -- On `B` the integral `∫ y, 1_B y ∂(κ x)` equals `1`.
  have hxval : (B.indicator (1 : Work.EKLContract.X3 → ℝ)) x = 1 := by
    rw [Set.indicator_of_mem hxB]; rfl
  have hint : ∫ y, (B.indicator (1 : Work.EKLContract.X3 → ℝ)) y
      ∂(ProbabilityTheory.condExpKernel μ 𝔪.m x) = 1 := by
    rw [← hx2, h1, hxval]
  -- That integral is `(κ x).real B`, so `(κ x).real B = 1`, hence `(κ x) B = 1`.
  have hreal : (ProbabilityTheory.condExpKernel μ 𝔪.m x).real B = 1 :=
    (MeasureTheory.integral_indicator_one hBmeas).symm.trans hint
  rw [MeasureTheory.Measure.real_def] at hreal
  exact (ENNReal.toReal_eq_one_iff _).mp hreal

end Work.EKLComp
