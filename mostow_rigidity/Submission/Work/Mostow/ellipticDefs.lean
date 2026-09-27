import Mathlib
import Submission.Mostow.SubHypDefs
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.HaarBoost
import Submission.Work.Mostow.bieberbachDefs
import Submission.Work.Mostow.fix_subset_hyperplane

/-!
# Shared definitions for the elliptic normal form chapter

`linBlk k m R` is the "linear block map" in the split space `E (k+m)`: it keeps the first `k`
coordinates and applies `R` to the last `m` coordinates.  `vblk k hk R` is the same map
written in the coordinates of `E n` (with `k ≤ n`, `m = n - k`), i.e. the "value split".
The lemma `blkMap_linBlk` identifies `blkMap k m 1 R` with `linBlk k m R`; it is the honest
meaning of `blk`, used only through the single lemma `blk_linear_act`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-- The linear block map in `E (k+m)`: keep the first `k` coordinates, apply `R` to the last
`m` coordinates. -/
def linBlk (k m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (u : E (k + m)) : E (k + m) :=
  WithLp.toLp 2 (Fin.append (fun i => u (Fin.castAdd m i))
    (fun j => R (WithLp.toLp 2 (fun j' => u (Fin.natAdd k j'))) j))

/-- The value-split block map on `E n`: keep the coordinates with value `< k`, apply `R` to the
coordinates with value `≥ k`. -/
def vblk (k : ℕ) {n : ℕ} (hk : k ≤ n) (R : E (n - k) ≃ₗᵢ[ℝ] E (n - k)) (u : E n) : E n :=
  WithLp.toLp 2 (fun i : Fin n =>
    if h : (i : ℕ) < k then u i
    else (R (WithLp.toLp 2 (fun j : Fin (n - k) =>
      u ⟨k + j.val, by have := j.isLt; omega⟩)))
      ⟨i.val - k, by have := i.isLt; omega⟩)

end

end Work.Mostow
