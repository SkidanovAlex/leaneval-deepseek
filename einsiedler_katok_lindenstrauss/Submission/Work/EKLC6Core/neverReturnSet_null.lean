import Mathlib
import Submission.Work.EKLC6Core.towerDefs

namespace Work.EKLC6Core

open MeasureTheory Set
open Work.EKLContract

/-- **Poincaré recurrence, quantitative form.** The set of points of `Ω` whose forward orbit
never returns to `Ω` is `μ`-null, for any `μ`-preserving self-map of `X₃` (here `x ↦ aDiag t • x`).

This is the standard Poincaré recurrence statement: the never-returning set is
`{x ∈ Ω | ∀ m ≥ 1, T^[m] x ∉ Ω}`, whose `μ`-measure vanishes by
`MeasureTheory.Conservative.measure_mem_forall_ge_image_notMem_eq_zero`. -/
theorem neverReturnSet_null {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ}
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    {Ω : Set Work.EKLContract.X3} (hΩ : MeasurableSet Ω) :
    μ (Work.EKLC6Core.neverReturnSet t Ω) = 0 := by
  have hcons : MeasureTheory.Conservative
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ :=
    hmp.conservative
  have h := hcons.measure_mem_forall_ge_image_notMem_eq_zero hΩ.nullMeasurableSet 1
  have heq : neverReturnSet t Ω =
      {x : Work.EKLContract.X3 | x ∈ Ω ∧ ∀ m : ℕ, 1 ≤ m →
        ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[m]) x ∉ Ω} := by
    ext x
    simp only [neverReturnSet, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter,
      Set.mem_compl_iff, Set.mem_ofPred_eq]
  rw [heq]
  simpa using h

end Work.EKLC6Core
