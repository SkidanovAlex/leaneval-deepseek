/-
  Area E7 / `CoreLT_succ`: the **rank classification** of a piece.

  A piece `T : Stratum 0 (n + (m+1))` in the `(n, m+1)` frame with `Good` and
  `π_{n+1}`-rank `= dim T` (`piPiecesIdx` + `stratReindex_projTop`) has, at every `z ∈ T.X.set`,
  `projRank T z ∈ {d-1, d}` where `d := n + (m+1) - T.j = dim T`:

  * `projRank T z ≤ d` is `RankBounds.projRank_le_dim`;
  * `d - 1 ≤ projRank T z` is `RankBounds.le_projRank_of_projTop_rank` (the `π_{n+1}`-rank being
    `d` means `projTopLin` is injective on the tangent space, so dropping its last coordinate
    loses at most one dimension).

  Consequently the "low" locus `{projRank T z ≤ K-1}` is the union of the rank slices
  `Y_r = {z ∈ T.X.set : projRank T z = r}`, `r < K`, all of which are `SemiPf` with
  `NullDimLT (π_n ·) K` (`LowLocus.rankSlice_nullDim` at `r`).  These are the `Σlow` members of
  the `CoreLT_succ` assembly.

  `absSlice` turns a `SemiPf (0 + N)` (the shape in which `rankSlice_nullDim` returns its set,
  via `MainDesign.absPt`) into a `SemiPf N`.
-/
import Mathlib
import Submission.Work.WilE7.coreLT_succ.Pieces
import Submission.Work.WilE7.coreLT_succ.LowLocus
import Submission.Work.WilE7.CoreStep.SigmaAux
import Submission.Work.WilE7.coreLT_succ.RankBounds
import Submission.Work.WilE7.DimAPI.nullDimLT_basics

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.coreLT_succ

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreStep (projTop projTopLin absPtLin)

/-! ## The `absPt`-reindexing of a `SemiPf` set -/

/-- A `SemiPf (0 + N)` set, transported to `SemiPf N` along `absPt`.  This is the shape in which
`rankSlice_nullDim` presents its set. -/
def absSlice {N : ℕ} (Y : WilkiesDesign.E.SemiPf (0 + N)) : WilkiesDesign.E.SemiPf N :=
  Work.CoreStep.absSub ⟨Y, 0, Fin.elim0⟩

theorem absSlice_set {N : ℕ} (Y : WilkiesDesign.E.SemiPf (0 + N)) :
    (absSlice Y).set = MainDesign.absPt '' Y.set :=
  Work.CoreStep.absSub_set ⟨Y, 0, Fin.elim0⟩

@[simp] theorem absSlice_r {N : ℕ} (Y : WilkiesDesign.E.SemiPf (0 + N)) :
    (absSlice Y).r = Y.r := rfl

theorem absSlice_deg {N : ℕ} (Y : WilkiesDesign.E.SemiPf (0 + N)) :
    (absSlice Y).deg = Y.deg :=
  Work.CoreStep.absSub_deg ⟨Y, 0, Fin.elim0⟩

theorem absSlice_fmt {N : ℕ} (Y : WilkiesDesign.E.SemiPf (0 + N)) :
    (absSlice Y).fmt = N + Y.r := rfl

/-! ## The two-sided rank bound -/

/-- **The `π_n`-rank of a piece lies in `{d-1, d}`.**  For a `Good` stratum of the `(n, m+1)`
frame whose `π_{n+1}`-rank equals its dimension `d = n + (m+1) - T.j`, the `π_n`-rank at every
point of the stratum is `d` or `d - 1`. -/
theorem projRank_mem_two {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1))) (hT : T.Good)
    (hrankTop : ∀ z ∈ T.X.set,
      Module.finrank ℝ
          ↥(Submodule.map (projTopLin n m ∘ₗ absPtLin (n + (m + 1))) (MainDesign.jac T z).ker) =
        n + (m + 1) - T.j)
    {z : Fin (0 + (n + (m + 1))) → ℝ} (hz : z ∈ T.X.set) :
    n + (m + 1) - T.j - 1 ≤ MainDesign.projRank T z ∧
      MainDesign.projRank T z ≤ n + (m + 1) - T.j :=
  ⟨le_projRank_of_projTop_rank T (hrankTop z hz), projRank_le_dim T hT hz⟩

/-! ## The `Σlow` members -/

/-- **The rank slice `Y_r` of a piece is a `Σlow` member.**  For `r + 1 ≤ K`, the rank-`r` locus
of a piece is a `SemiPf` set whose `π_n`-projection is `NullDimLT · K`. -/
theorem rankSlice_sigmaLow_data (F : ℕ) :
    ∃ (A : ℕ) (B : Polynomial ℕ),
      ∀ (n m r K : ℕ) (T : WilkiesDesign.E.Stratum 0 (n + (m + 1))), T.Good → T.X.fmt ≤ F →
        r + 1 ≤ K →
        ∃ Y : WilkiesDesign.E.SemiPf (n + (m + 1)),
          Y.set = MainDesign.absPt '' {z : Fin (0 + (n + (m + 1))) → ℝ |
              z ∈ T.X.set ∧ MainDesign.projRank T z = r} ∧
          Y.fmt ≤ A ∧ Y.deg ≤ B.eval T.deg ∧
          NullDimLT (WilkiesDesign.E.projFirst n (m + 1) '' Y.set) K := by
  classical
  obtain ⟨A, B, h⟩ := rankSlice_nullDim F
  refine ⟨A, B, ?_⟩
  intro n m r K T hT hF hK
  obtain ⟨Y₀, hset, hfmt, hdeg, hnull⟩ := h n m r T hT hF
  refine ⟨absSlice Y₀, ?_, ?_, ?_, ?_⟩
  · rw [absSlice_set, hset]
  · rw [absSlice_fmt]
    have h : Y₀.fmt = n + (m + 1) + Y₀.r := by
      simp only [WilkiesDesign.E.SemiPf.fmt]
      omega
    rw [← h]
    exact hfmt
  · rw [absSlice_deg]
    exact hdeg
  · rw [absSlice_set]
    cases K with
    | zero => omega
    | succ K' =>
        have hle : r ≤ K' := by omega
        exact Work.WilE7.DimAPI.nullDimLE_mono_dim hnull hle

end Work.WilE7.coreLT_succ
