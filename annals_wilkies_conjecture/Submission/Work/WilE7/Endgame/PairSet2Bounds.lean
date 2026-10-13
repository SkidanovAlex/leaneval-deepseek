/-
  Area E7 / `Work.WilE7.Endgame`: **bounds for the two-piece pair sets** `absPairSet2`.

  `Work.CoreStep.SigmaFamDefs` provides the format/degree bounds of the *same-piece* pair sets
  `absPairSet T = fiberProdZ (absReindex T) (absReindex T)` and of the level-agreement sets
  `absLevelPairSet T T'`.  The endgame (G2, E1, E2) also needs the pair set of two *different*
  pieces, `Work.WilE7.CoreLTSuccPlan.absPairSet2 R T = fiberProdZ (absReindex R) (absReindex T)`
  reindexed to `SemiPf (0 + pPair n m)`, and there the analogous bounds were missing (flagged by
  the reviewer of E1).

  The proofs are the same one-liners as `absPairSet_deg_le`: the reindexing preserves `r` and
  `deg`, `fiberProdZ_deg` needs only the format bound of the *first* factor, and `fiberProdZ_fmt`
  needs both.
-/
import Mathlib
import Submission.Work.WilE7.CoreStep.CoreLTSuccNodes
import Submission.Work.CoreStep.SigmaFamDefs
import Submission.Work.WilE7.fiberProduct_semiPf

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.Endgame

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreLTSuccPlan
open Work.WilE7.CoreStep (pPair absReindex absLevelPairSet absPairSet)

theorem absPairSet2_set {n m : ℕ} (R T : Stratum 0 (n + (m + 1))) :
    (absPairSet2 R T).set = {z : Fin (0 + pPair n m) → ℝ |
      (fun i : Fin (pPair n m) => z (Fin.cast (Nat.zero_add (pPair n m)).symm i)) ∈
        (Work.WilE7.fiberProdZ (absReindex R) (absReindex T)).set} := by
  rw [absPairSet2, Work.WilE7.sp_reindex_set]
  rfl

/-- The format of the two-piece pair set is at most twice the format bound of the pieces. -/
theorem absPairSet2_fmt_le {n m F : ℕ} (R T : Stratum 0 (n + (m + 1)))
    (hR : (n + (m + 1)) + R.X.r ≤ F) (hT : (n + (m + 1)) + T.X.r ≤ F) :
    (absPairSet2 R T).fmt ≤ 2 * F := by
  have h := Work.WilE7.fiberProdZ_fmt (absReindex R) (absReindex T) hR hT
  have h1 : (absPairSet2 R T).fmt =
      (Work.WilE7.fiberProdZ (absReindex R) (absReindex T)).fmt := by
    show (0 + pPair n m) + (R.X.r + T.X.r) = pPair n m + (R.X.r + T.X.r)
    rw [Nat.zero_add]
  rw [h1]
  exact h

/-- The degree of the two-piece pair set. -/
theorem absPairSet2_deg_le {n m F : ℕ} (R T : Stratum 0 (n + (m + 1)))
    (hR : (n + (m + 1)) + R.X.r ≤ F) :
    (absPairSet2 R T).deg ≤ 2 * (1 + F) * (1 + (R.X.deg + T.X.deg)) ^ 2 := by
  have hfmt : (absReindex R).fmt ≤ F := hR
  have hdeg : (absReindex R).deg = R.X.deg := Work.WilE7.sp_reindex_deg _ _
  have hdeg' : (absReindex T).deg = T.X.deg := Work.WilE7.sp_reindex_deg _ _
  have hmain := Work.WilE7.fiberProdZ_deg (absReindex R) (absReindex T) hfmt
  rw [hdeg, hdeg'] at hmain
  have h1 : (absPairSet2 R T).deg =
      (Work.WilE7.fiberProdZ (absReindex R) (absReindex T)).deg :=
    Work.WilE7.sp_reindex_deg _ _
  rw [h1]
  exact hmain

end Work.WilE7.Endgame
