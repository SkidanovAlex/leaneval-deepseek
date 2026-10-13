/-
  `Work.WilE7.coreLT_succ.LowLocus`: the `π_n`-rank slices of an absolute `Good` stratum, as
  `SemiPf` sets with the null-dimension bound that the `Σ`-family of `CoreLT_succ` needs.

  The two halves are already proved elsewhere:

  * `Work.CoreStep.rankSlice_projRank` — the slice `{z ∈ T.X.set : projRank T z = r}` is
    `SemiPf`, of format `≤ F` and degree `≤ B.eval T.deg` whenever `T.X.fmt ≤ F`;
  * `Work.WilE7.DimAPI.rankLocus_nullDimLE` — for a `Good` absolute stratum `T` the locus
    `{projRank T z ≤ r}` maps to a `NullDimLE · r` set, hence to a `NullDimLT · (r+1)` set.

  Combining them gives the form consumed by `Work.WilE7.CoreStep.sigmaLow` (the "low-dimensional"
  part of `Σ`): a `SemiPf` set whose `π_n`-projection is `NullDimLT · (r+1)`, with bounds
  depending only on `F` (for the format) and on `T.deg` (for the degree).
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.coreLT_succ.SubStratum
import Submission.Work.CoreStep.rankSlice_projRank
import Submission.Work.WilE7.DimAPI.rankLocus_nullDimLE
import Submission.Work.WilE7.DimAPI.nullDimLT_basics

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology

namespace Work.WilE7.coreLT_succ

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign

/-- **The `π_n`-rank slice of an absolute `Good` stratum is a `SemiPf` set whose `π_n`-projection
has dimension `< r+1`.**  The format bound `A` and the degree polynomial `B` depend only on the
format bound `F`. -/
theorem rankSlice_nullDim (F : ℕ) :
    ∃ (A : ℕ) (B : Polynomial ℕ),
      ∀ (n m r : ℕ) (T : Stratum 0 (n + (m + 1))),
        T.Good → T.X.fmt ≤ F →
        ∃ Y : SemiPf (0 + (n + (m + 1))),
          Y.set = {z | z ∈ T.X.set ∧ projRank T z = r} ∧
          Y.fmt ≤ A ∧ Y.deg ≤ B.eval T.deg ∧
          NullDimLT (projFirst n (m + 1) '' (absPt '' Y.set)) (r + 1) := by
  obtain ⟨A, B, h⟩ := Work.CoreStep.rankSlice_projRank F
  refine ⟨A, B, fun n m r T hT hF => ?_⟩
  obtain ⟨Y, hset, hfmt, hdeg⟩ := h n (m + 1) r T hF
  refine ⟨Y, hset, hfmt, hdeg, ?_⟩
  have hsub : Y.set ⊆ {z | z ∈ T.X.set ∧ projRank T z ≤ r} := by
    intro z hz
    rw [hset] at hz
    exact ⟨hz.1, le_of_eq hz.2⟩
  refine NullDimLT.mono (Work.WilE7.DimAPI.rankLocus_nullDimLE T hT r) ?_
  exact Set.image_mono (Set.image_mono hsub)

end Work.WilE7.coreLT_succ
