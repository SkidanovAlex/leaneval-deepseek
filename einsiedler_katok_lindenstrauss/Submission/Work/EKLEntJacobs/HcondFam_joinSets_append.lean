import Mathlib
import Submission.Work.EKLComp.Hcond
import Submission.Work.EKLComp.Entropy

namespace Work.EKLEntJacobs

open MeasureTheory

/-- Splitting the conditional entropy of the join at a time cut: for the join partition
`joinSets T Q (m+n)` of the finite partition `Q` over the first `m+n` iterates of `T`, the
conditional entropy given the σ-algebra of `B` equals the conditional entropy of the family
indexed by pairs `(u, v)` of words with atoms `joinSets T Q m u ∩ T^[m] ⁻¹' joinSets T Q n v`
(which is the image of the former under `Fin.appendEquiv` and `joinSets_append`). -/
theorem HcondFam_joinSets_append {X : Type} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] (T : X → X) (Q : Work.EKLContract.FinPart X)
    {κ : Type} [Fintype κ] {B : κ → Set X} (hB : Work.EKLComp.Core.IsMPart B) (m n : ℕ) :
    Work.EKLComp.Core.HcondFam X μ (Work.EKLContract.joinSets T Q (m + n))
        (Work.EKLComp.Core.partSigmaFam B) =
      Work.EKLComp.Core.HcondFam X μ
        (fun p : (Fin m → Fin Q.n) × (Fin n → Fin Q.n) =>
          Work.EKLContract.joinSets T Q m p.1 ∩
            T^[m] ⁻¹' Work.EKLContract.joinSets T Q n p.2)
        (Work.EKLComp.Core.partSigmaFam B) := by
  classical
  -- The conditional entropy is the integral of the sum over the atoms of `negMulLog` of the
  -- conditional expectation of the indicator.  Reindexing the index set of the join along
  -- `Fin.appendEquiv` and using `joinSets_append` identifies the two integrands pointwise.
  unfold Work.EKLComp.Core.HcondFam
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [← Equiv.sum_comp (Fin.appendEquiv (α := Fin Q.n) m n)
    (fun i => Real.negMulLog (MeasureTheory.condExp (Work.EKLComp.Core.partSigmaFam B) μ
      ((Work.EKLContract.joinSets T Q (m + n) i).indicator (fun _ => (1 : ℝ))) x))]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have hset : Work.EKLContract.joinSets T Q (m + n) ((Fin.appendEquiv (α := Fin Q.n) m n) p) =
      Work.EKLContract.joinSets T Q m p.1 ∩ T^[m] ⁻¹' Work.EKLContract.joinSets T Q n p.2 :=
    Work.EKLComp.Core.joinSets_append T Q m n p.1 p.2
  rw [hset]

end Work.EKLEntJacobs
