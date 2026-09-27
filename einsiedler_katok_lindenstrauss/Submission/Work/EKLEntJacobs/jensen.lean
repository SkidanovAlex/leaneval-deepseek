import Mathlib
import Submission.Work.EKLComp.EntJacobsAux
import Submission.Work.EKLEntJacobs.Hcond_kernel

/-!
# Jensen's inequality for the conditional entropy (the `Hcond ≤ H` direction)

For a probability measure `μ` on a standard Borel space, a self-map `T`, and a finite family `A`
of measurable sets, the conditional entropy of `A` given the σ-algebra `invariants T` is at most
the unconditional entropy `Hfam μ A`:

`∫ x, ∑ i, negMulLog ((condExpKernel μ (invariants T) x) (A i)).toReal ∂μ ≤ Hfam μ A`.

The proof combines four standard ingredients:

* `ProbabilityTheory.condExpKernel_ae_eq_condExp` (via the already verified identity
  `Work.EKLEntJacobs.Hcond_kernel`), rewriting the kernel integral as the integral of the
  conditional expectations `μ⟦1_{A i} | invariants T⟧`;
* `Real.concaveOn_negMulLog` together with `ConcaveOn.le_map_integral` (Jensen's inequality),
  applied to each part `A i` separately;
* `MeasureTheory.integral_condExp` (the law of total expectation) to identify
  `∫ x, μ⟦1_{A i} | invariants T⟧ x ∂μ = (μ (A i)).toReal`;
* `MeasureTheory.integral_finsetSum`, to exchange the integral with the finite sum.

Nothing here uses any property of `T` beyond `invariants T ≤ mX`; in particular `T` is not
required to be measurable or measure preserving.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

namespace Work.EKLEntJacobs

/-- The entropy function composed with the conditional expectation of the indicator of a
measurable set `A` is integrable: the conditional expectation is a.e. in `[0,1]`, where
`negMulLog` is bounded by `1`. -/
private theorem integrable_negMulLog_condExp_indicator {X : Type} [mX : MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (T : X → X) {A : Set X} (hA : MeasurableSet A) :
    Integrable (fun x => Real.negMulLog (condExp (MeasurableSpace.invariants T) μ
      ((A.indicator fun _ => (1 : ℝ))) x)) μ := by
  have hm : MeasurableSpace.invariants T ≤ mX := MeasurableSpace.invariants_le T
  have hgint : Integrable ((A.indicator fun _ => (1 : ℝ))) μ :=
    (integrable_indicator_iff (μ := μ) hA).2 integrableOn_const
  have hg0 : 0 ≤ᵐ[μ] ((A.indicator fun _ => (1 : ℝ))) :=
    Filter.Eventually.of_forall (Set.indicator_nonneg fun _ _ => zero_le_one)
  have hg1 : ((A.indicator fun _ => (1 : ℝ))) ≤ᵐ[μ] (fun _ => (1 : ℝ)) :=
    Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]; exact zero_le_one
  have hce0 : 0 ≤ᵐ[μ] (fun x => condExp (MeasurableSpace.invariants T) μ
      ((A.indicator fun _ => (1 : ℝ))) x) :=
    condExp_nonneg hg0
  have hce1 : (fun x => condExp (MeasurableSpace.invariants T) μ
      ((A.indicator fun _ => (1 : ℝ))) x) ≤ᵐ[μ] (fun _ => (1 : ℝ)) := by
    have h := condExp_mono (m := MeasurableSpace.invariants T) (μ := μ)
      hgint (integrable_const (1 : ℝ)) hg1
    simpa [condExp_const hm (1 : ℝ)] using h
  have hceint : Integrable (fun x => condExp (MeasurableSpace.invariants T) μ
      ((A.indicator fun _ => (1 : ℝ))) x) μ :=
    integrable_condExp
  refine Integrable.of_bound ?_ 1 ?_
  · exact Real.continuous_negMulLog.comp_aestronglyMeasurable hceint.aestronglyMeasurable
  · filter_upwards [hce0, hce1] with x h0 h1
    simp only [Pi.zero_apply] at h0
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.negMulLog_nonneg h0 h1)]
    linarith [Real.negMulLog_le_one_sub_self h0]

/-- Jensen's inequality for the entropy function evaluated at the conditional expectation of the
indicator of a measurable set: the mean of `negMulLog` of the conditional probability of `A` is at
most `negMulLog` of the unconditional probability of `A`. -/
private theorem integral_negMulLog_condExp_indicator_le {X : Type} [mX : MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (T : X → X) {A : Set X} (hA : MeasurableSet A) :
    ∫ x, Real.negMulLog (condExp (MeasurableSpace.invariants T) μ
        ((A.indicator fun _ => (1 : ℝ))) x) ∂μ
      ≤ Real.negMulLog ((μ A).toReal) := by
  have hm : MeasurableSpace.invariants T ≤ mX := MeasurableSpace.invariants_le T
  have hgint : Integrable ((A.indicator fun _ => (1 : ℝ))) μ :=
    (integrable_indicator_iff (μ := μ) hA).2 integrableOn_const
  have hg0 : 0 ≤ᵐ[μ] ((A.indicator fun _ => (1 : ℝ))) :=
    Filter.Eventually.of_forall (Set.indicator_nonneg fun _ _ => zero_le_one)
  have hce0 : 0 ≤ᵐ[μ] (fun x => condExp (MeasurableSpace.invariants T) μ
      ((A.indicator fun _ => (1 : ℝ))) x) :=
    condExp_nonneg hg0
  have hceint : Integrable (fun x => condExp (MeasurableSpace.invariants T) μ
      ((A.indicator fun _ => (1 : ℝ))) x) μ :=
    integrable_condExp
  have hcomp : Integrable (fun x => Real.negMulLog (condExp (MeasurableSpace.invariants T) μ
      ((A.indicator fun _ => (1 : ℝ))) x)) μ :=
    integrable_negMulLog_condExp_indicator μ T hA
  calc ∫ x, Real.negMulLog (condExp (MeasurableSpace.invariants T) μ
          ((A.indicator fun _ => (1 : ℝ))) x) ∂μ
      ≤ Real.negMulLog (∫ x, condExp (MeasurableSpace.invariants T) μ
          ((A.indicator fun _ => (1 : ℝ))) x ∂μ) :=
        ConcaveOn.le_map_integral Real.concaveOn_negMulLog
          Real.continuous_negMulLog.continuousOn isClosed_Ici hce0 hceint hcomp
    _ = Real.negMulLog (∫ x, (A.indicator fun _ => (1 : ℝ)) x ∂μ) := by rw [integral_condExp hm]
    _ = Real.negMulLog ((μ A).toReal) := by
        rw [integral_indicator (μ := μ) hA, setIntegral_const, smul_eq_mul, mul_one]
        rfl

/-- The conditional entropy of a finite family of measurable sets given the σ-algebra of
`T`-invariant sets is at most its unconditional entropy `Hfam`. -/
private theorem HcondFam_le_Hfam {X : Type} [mX : MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (T : X → X) {ι : Type*} [Fintype ι] {A : ι → Set X} (hA : ∀ i, MeasurableSet (A i)) :
    Work.EKLComp.HcondFam μ A (MeasurableSpace.invariants T) ≤ Work.EKLContract.Hfam μ A := by
  rw [Work.EKLComp.HcondFam, Work.EKLContract.Hfam]
  have hint : ∀ i, Integrable
      (fun x => Real.negMulLog (condExp (MeasurableSpace.invariants T) μ
        ((A i).indicator fun _ => (1 : ℝ)) x)) μ :=
    fun i => integrable_negMulLog_condExp_indicator μ T (hA i)
  rw [integral_finsetSum Finset.univ fun i _ => hint i]
  exact Finset.sum_le_sum fun i _ => integral_negMulLog_condExp_indicator_le μ T (hA i)

/-- **Jensen's inequality for the conditional entropy.** For a probability measure `μ` on a
standard Borel space, an arbitrary self-map `T`, and a finite family `A` of measurable sets, the
integral of the Shannon entropy of the conditional measure of `x` on the parts `A i` is at most
the unconditional entropy `Hfam μ A`. -/
theorem jensen {X : Type} [mX : MeasurableSpace X] [StandardBorelSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (T : X → X) {ι : Type*} [Fintype ι] {A : ι → Set X} (hA : ∀ i, MeasurableSet (A i)) :
    ∫ x, ∑ i, Real.negMulLog (((ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) (A i)).toReal) ∂μ
      ≤ Work.EKLContract.Hfam μ A := by
  rw [← Hcond_kernel μ T hA]
  exact HcondFam_le_Hfam μ T hA

end Work.EKLEntJacobs
