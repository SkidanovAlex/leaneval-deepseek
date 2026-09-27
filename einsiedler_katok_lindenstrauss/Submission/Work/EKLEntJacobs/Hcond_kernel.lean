import Mathlib
import Submission.Work.EKLComp.EntJacobsAux

/-!
# `HcondFam` as an integral against the conditional expectation kernel

For the invariant σ-algebra `invariants T`, the conditional expectation of the indicator of a
measurable set `s` agrees almost everywhere with the evaluation of the conditional expectation
kernel `condExpKernel μ (invariants T) x` on `s` (`ProbabilityTheory.condExpKernel_ae_eq_condExp`).
Summing over the finite family and integrating gives the stated identity.

The hypothesis `StandardBorelSpace X` is exactly what is needed to have the kernel at hand; `T`
itself is not used (`invariants T ≤ mX` holds for every `T`).

The file records this rewriting so that downstream work can replace the abstract conditional
expectation in `HcondFam` by the explicit kernel integral.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

namespace Work.EKLEntJacobs

/-- `HcondFam` w.r.t. `invariants T` equals the integral of the entropy of the conditional
measure of `x` on the atoms `A i`. -/
theorem Hcond_kernel {X : Type} [mX : MeasurableSpace X] [StandardBorelSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (T : X → X) {ι : Type*} [Fintype ι] {A : ι → Set X} (hA : ∀ i, MeasurableSet (A i)) :
    Work.EKLComp.HcondFam μ A (MeasurableSpace.invariants T)
      = ∫ x, ∑ i, Real.negMulLog
          (((ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) (A i)).toReal) ∂μ := by
  rw [Work.EKLComp.HcondFam]
  refine integral_congr_ae ?_
  have h : ∀ i, (fun x => MeasureTheory.condExp (MeasurableSpace.invariants T) μ
        ((A i).indicator (fun _ => (1 : ℝ))) x) =ᵐ[μ]
      (fun x => ((ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) (A i)).toReal) := by
    intro i
    have hi := ProbabilityTheory.condExpKernel_ae_eq_condExp (μ := μ)
      (m := MeasurableSpace.invariants T) (MeasurableSpace.invariants_le T) (hA i)
    simpa only [MeasureTheory.Measure.real] using hi.symm
  filter_upwards [Filter.eventually_all.2 h] with x hx
  refine Finset.sum_congr rfl fun i _ => ?_
  exact congrArg Real.negMulLog (hx i)

end Work.EKLEntJacobs
