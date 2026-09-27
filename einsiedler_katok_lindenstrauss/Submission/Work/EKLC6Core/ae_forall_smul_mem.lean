import Mathlib
import Submission.Work.EKLC6Core.Basic

namespace Work.EKLC6Core

/-- **Countable intersections of conull sets under a measure-preserving `A`-action.**

Since `IsAInvariant μ` says that every diagonal flow `x ↦ aDiag t • x` is measure preserving,
the preimage of the conull set `X' ∩ X''` under any such flow is again conull; a countable union
of null sets is null, so a.e. `x` lies simultaneously, for every `j`, in `X' ∩ X''` along the
orbit `j • t`. -/
theorem ae_forall_smul_mem {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    (hAinv : Work.EKLContract.IsAInvariant μ) (t : Fin 3 → ℝ)
    {X' X'' : Set Work.EKLContract.X3} (hX' : μ X'ᶜ = 0) (hX'' : μ X''ᶜ = 0) :
    ∀ᵐ x ∂μ, ∀ j : ℕ, Work.EKLContract.aDiag ((j : ℝ) • t) • x ∈ X' ∩ X'' := by
  -- `X' ∩ X''` is conull.
  have hS : μ (X' ∩ X'')ᶜ = 0 := by
    rw [Set.compl_inter]
    exact MeasureTheory.measure_union_null hX' hX''
  -- Reformulate the "for all `j`" event as a countable intersection of preimages.
  rw [MeasureTheory.ae_iff]
  have hset : {x : Work.EKLContract.X3 |
        ¬ (∀ j : ℕ, Work.EKLContract.aDiag ((j : ℝ) • t) • x ∈ X' ∩ X'')}
      = ⋃ j : ℕ,
          (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag ((j : ℝ) • t) • x) ⁻¹'
            (X' ∩ X'')ᶜ := by
    ext x
    simp [Set.mem_iUnion]
  rw [hset]
  -- Each preimage is null because `aDiag (j • t)` is measure preserving.
  exact MeasureTheory.measure_iUnion_null
    (fun j => (hAinv ((j : ℝ) • t)).preimage_null hS)

end Work.EKLC6Core
