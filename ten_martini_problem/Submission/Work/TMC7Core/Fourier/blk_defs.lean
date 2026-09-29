/-
Definitions shared by `blk_weighted` and its two supporting estimates.

For a block index `m` and `r ∈ [1,q]`, `blkY α q m r` is the `q`-scaled distance of
`(m*q+r)*α` to the nearest integer:
`blkY = q * fracDist ((m*q+r) * α)`.

`blkE α q s m` is the contribution of the *second smallest* of the block's scaled distances:
the minimum over pairs of distinct indices of `max (blkY r) (blkY r')`, fed into
`1/(1+(s·x)²)`.  The per-block estimate holds with `1 + 2/s + 4 * blkE`, and `blkE` itself
has a small harmonically weighted sum.
-/
import Mathlib
import Submission.Work.TMC7Core.Defs

namespace Work.TMC7Core.Fourier

open Finset
open Classical

noncomputable section

/-- `q`-scaled distance of `(m*q+r)*α` to `ℤ`. -/
def blkY (α : ℝ) (q : ℕ) (m r : ℕ) : ℝ :=
  (q : ℝ) * fracDist ((((m * q + r : ℕ) : ℝ)) * α)

/-- The pairs of distinct indices in `[1,q]`. -/
def blkPairs (q : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 q).product (Finset.Icc 1 q)).filter (fun p => p.1 ≠ p.2)

/-- The second smallest of the block's scaled distances: the minimum over pairs of distinct
indices of the maximum of the two scaled distances (junk value `0` when `q ≤ 1`). -/
def blkY2 (α : ℝ) (q m : ℕ) : ℝ :=
  if h : (blkPairs q).Nonempty then
    (blkPairs q).inf' h (fun p => max (blkY α q m p.1) (blkY α q m p.2))
  else 0

/-- Contribution of the second-smallest scaled distance. -/
def blkE (α : ℝ) (q s m : ℕ) : ℝ :=
  if h : (blkPairs q).Nonempty then
    (1 + ((s : ℝ) * ((blkPairs q).inf'
      h (fun p => max (blkY α q m p.1) (blkY α q m p.2)))) ^ 2)⁻¹
  else 0

/-- Indicator of the "exceptional" blocks, where two of the block points have scaled
distances summing to less than `4/s` (kept for compatibility with the first formulation). -/
def blkBad (α : ℝ) (q s m : ℕ) : ℝ :=
  if ∃ r ∈ Finset.Icc 1 q, ∃ r' ∈ Finset.Icc 1 q, r ≠ r' ∧
      blkY α q m r + blkY α q m r' < 4 / (s : ℝ) then 1 else 0

lemma blkBad_nonneg (α : ℝ) (q s m : ℕ) : 0 ≤ blkBad α q s m := by
  unfold blkBad; split <;> norm_num

lemma blkBad_le_one (α : ℝ) (q s m : ℕ) : blkBad α q s m ≤ 1 := by
  unfold blkBad; split <;> norm_num

lemma blkE_nonneg (α : ℝ) (q s m : ℕ) : 0 ≤ blkE α q s m := by
  unfold blkE; split
  · positivity
  · norm_num

lemma blkE_le_one (α : ℝ) (q s m : ℕ) : blkE α q s m ≤ 1 := by
  unfold blkE; split
  · rename_i h
    apply inv_le_one_of_one_le₀
    nlinarith [sq_nonneg ((s : ℝ) * ((blkPairs q).inf'
      h (fun p => max (blkY α q m p.1) (blkY α q m p.2))))]
  · norm_num

end

end Work.TMC7Core.Fourier
