import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLComp.Misiurewicz.Defs
import Submission.Work.EKLComp.Core
import Submission.Work.EKLComp.Entropy
import Submission.Work.Misiurewicz.Hfam_iInter_range_le
import Submission.Work.Misiurewicz.Hfam_winJoin_grid_reindex

/-!
# Grid subadditivity for window joins

The window join `winJoin T P k N w = ⋂_{j < N} T^{-(j+k)} (P.parts (w j))` observes the
orbit of a point over the time window `[k, k+N)`.  The window `[k, k + m*n)` is tiled by the
`m` disjoint blocks `[k + i*n, k + (i+1)*n)`, `i < m`, so `winJoin T P k (m*n)` is the join
(the common refinement) of the `m` partitions `winJoin T P (k + i*n) n`; Shannon entropy is
subadditive over joins, which gives

`Hfam μ (winJoin T P k (m*n)) ≤ ∑_{i<m} Hfam μ (winJoin T P (k + i*n) n)`.

The two ingredients are proved separately:

* `Hfam_winJoin_grid_reindex` : the reindexing identity expressing `winJoin T P k (m*n)` as the
  `m`-fold join of the block partitions (via `finProdFinEquiv`);
* `Hfam_iInter_range_le` : subadditivity of `Hfam` over an `m`-fold join of partitions.

This file records the `IsMPart` structure of the window joins (needed by the second ingredient)
and assembles the two.
-/

namespace Work.Misiurewicz

open Work.EKLContract Work.EKLComp

/-- Each atom of a window join is measurable, being a finite intersection of preimages of the
measurable parts of `P` under iterates of `T`. -/
theorem winJoin_measurable {T : X3 → X3} (hT : Measurable T) (P : FinPart X3) (k N : ℕ)
    (w : Fin N → Fin P.n) : MeasurableSet (winJoin T P k N w) := by
  rw [winJoin_eq_preimage T P k N w]
  exact (Work.EKLComp.Core.joinSets_measurable hT P N w).preimage (hT.iterate k)

/-- The window join `winJoin T P k N` is a finite measurable partition of `X₃`. -/
theorem winJoin_isMPart {T : X3 → X3} (hT : Measurable T) (P : FinPart X3) (k N : ℕ) :
    Work.EKLComp.Core.IsMPart (winJoin T P k N) :=
  ⟨winJoin_measurable hT P k N, (winJoin_isPartition T P k N).2,
    (winJoin_isPartition T P k N).1⟩

theorem Hfam_winJoin_grid (μ : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsProbabilityMeasure μ]
    (T : Work.EKLContract.X3 → Work.EKLContract.X3) (hT : Measurable T)
    (P : Work.EKLContract.FinPart Work.EKLContract.X3) (k m n : ℕ) :
    Work.EKLContract.Hfam μ (Work.EKLComp.winJoin T P k (m * n)) ≤
      ∑ i ∈ Finset.range m, Work.EKLContract.Hfam μ (Work.EKLComp.winJoin T P (k + i * n) n) := by
  rw [Hfam_winJoin_grid_reindex μ T P k m n]
  exact Hfam_iInter_range_le μ m (fun i => winJoin T P (k + i * n) n)
    (fun i _ => winJoin_isMPart hT P (k + i * n) n)

end Work.Misiurewicz
