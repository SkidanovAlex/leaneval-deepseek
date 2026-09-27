import Mathlib
import Submission.Work.EKLC6Core.Hcond_mono
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLGen.tendsto_Hcond_iSup_univ

/-!
# Nonnegativity of the conditional entropy `Hcond`

`Hcond μ P m = ∫ ∑ᵢ -𝔼[1_{Pᵢ}|m] log 𝔼[1_{Pᵢ}|m] dμ` is the conditional entropy of the finite
partition `P` given the σ-algebra `m`.  As an entropy it is nonnegative: the integrand is a sum
of the terms `-p log p` with `p = 𝔼[1_{Pᵢ}|m] ∈ [0,1]` almost everywhere, each of which is
nonnegative.

**Formalisation note.**  The statement binds the conditioning σ-algebra `m` *after* the ambient
instance `mX`.  Lean's typeclass search treats a local hypothesis of class type as an instance
candidate and the most recently introduced one wins, so inside the proof the ambient instance is
re-established with `letI` in order to refer to the ambient `Measure X` structure.
-/

open MeasureTheory Filter

set_option linter.style.haveILetI false

namespace Work.EKLC6Core

/-- The integral of `-𝔼[f|m] log 𝔼[f|m]` is nonnegative for `f` a.e. in `[0,1]`. -/
lemma integral_negMulLog_condExp_nonneg {X : Type*} {m : MeasurableSpace X}
    [mX : MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ}
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (hf1 : ∀ᵐ x ∂μ, f x ≤ 1) (hfi : Integrable f μ) :
    0 ≤ ∫ x, Real.negMulLog (condExp m μ f x) ∂μ := by
  refine MeasureTheory.integral_nonneg_of_ae ?_
  by_cases hm : m ≤ mX
  · filter_upwards [condExp_mem_Icc (μ := μ) (m := m) hm hf0 hf1 hfi] with x hx
    exact Real.negMulLog_nonneg hx.1 hx.2
  · have h0 : condExp m μ f = 0 := condExp_of_not_le hm
    filter_upwards with x
    rw [h0]
    simp

/-- The conditional entropy of a finite partition given an arbitrary σ-algebra is nonnegative. -/
theorem Hcond_nonneg {X : Type*} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] (P : Work.EKLContract.FinPart X) (m : MeasurableSpace X) :
    0 ≤ @Work.EKLContract.Hcond X mX μ P m := by
  letI : MeasurableSpace X := mX
  rw [Hcond_eq_sum_integral (μ := μ) (m := m) P]
  refine Finset.sum_nonneg (fun i _ => ?_)
  exact integral_negMulLog_condExp_nonneg (μ := μ) (m := m)
    (Filter.Eventually.of_forall fun x => (indicator_mem_Icc (P.parts i) x).1)
    (Filter.Eventually.of_forall fun x => (indicator_mem_Icc (P.parts i) x).2)
    ((integrable_const (1 : ℝ)).indicator (P.measurable i))

end Work.EKLC6Core
