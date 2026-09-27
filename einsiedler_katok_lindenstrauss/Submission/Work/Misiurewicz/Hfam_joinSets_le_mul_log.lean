import Mathlib
import Submission.Work.EKLComp.Entropy

/-!
# `Hfam` of a join along `n` iterates is at most `n log |P|`

The join `joinSets T P n` of the finite partition `P` over the first `n` iterates of `T` has
`P.n ^ n` atoms, and these atoms form a finite measurable partition of `X₃`
(`Work.EKLComp.Core.joinSets_isMPart`, itself built from `joinSets_measurable`,
`joinSets_disjoint`, `joinSets_iUnion`).  For a probability measure `μ` the Shannon entropy of a
finite partition is at most the logarithm of the number of its atoms (Gibbs' inequality,
`Work.EKLComp.Core.Hfam_le_log_card`), and

`log (#atoms) = log (P.n ^ n) = n * log (P.n)`.

Combining the two gives the stated bound.  Note that no invariance of `μ` under `T` is needed:
the bound only uses that `joinSets T P n` is a partition of the whole space.
-/

namespace Work.Misiurewicz

/-- The `Hfam`-entropy of the join of `P` along the first `n` iterates of `T` is at most
`n * log P.n`, the logarithm of the number of atoms of that join. -/
theorem Hfam_joinSets_le_mul_log (μ : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsProbabilityMeasure μ]
    (T : Work.EKLContract.X3 → Work.EKLContract.X3) (hT : Measurable T)
    (P : Work.EKLContract.FinPart Work.EKLContract.X3) (n : ℕ) :
    Work.EKLContract.Hfam μ (Work.EKLContract.joinSets T P n) ≤
      (n : ℝ) * Real.log (P.n : ℝ) := by
  have hle := Work.EKLComp.Core.Hfam_le_log_card μ (Work.EKLComp.Core.joinSets_isMPart hT P n)
  have hcard : Fintype.card (Fin n → Fin P.n) = P.n ^ n := by
    rw [Fintype.card_fun]
    simp
  rw [hcard, Nat.cast_pow, Real.log_pow] at hle
  exact hle

end Work.Misiurewicz
