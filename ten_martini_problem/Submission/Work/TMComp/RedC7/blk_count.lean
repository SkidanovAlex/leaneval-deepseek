import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Fourier.blk_defs
import Submission.Work.TMC7Core.Fourier.win_count

/-!
# `RedC7.blk_count`: the per-block witness count

For `α` within `1/q²` of a reduced fraction `a/q` and every block index `m`, the number of
`r ∈ [1,q]` whose block value `blkY α q m r = q·‖(m q + r)α‖` falls below `τ` is at most
`2τ + 2`.

This is `win_count` applied to the arithmetic progression
`blkY α q m r = qDist q (r · (q α) + m q² α)`: the block is the `q`-term AP with step
`ν = qα` (within `1/q` of the integer `a`) on the circle `ℝ/qℤ`, and `qDist q` is the
distance to `qℤ`.
-/

namespace Work.TMComp.RedC7

open Finset
open Work.TMC7Core Work.TMC7Core.Fourier

noncomputable section

/-- **The block values are the distance of an arithmetic progression to the lattice `qℤ`.** -/
theorem blkY_eq_qDist (α : ℝ) (q m r : ℕ) (hq : 1 ≤ q) :
    blkY α q m r = qDist q ((r : ℝ) * ((q : ℝ) * α) + (m : ℝ) * (q : ℝ) ^ 2 * α) := by
  have hq0 : ((q : ℝ)) ≠ 0 := by positivity
  have harg : ((m * q + r : ℕ) : ℝ) * α
      = ((r : ℝ) * ((q : ℝ) * α) + (m : ℝ) * (q : ℝ) ^ 2 * α) / (q : ℝ) := by
    field_simp
    push_cast
    ring
  simp only [blkY, qDist]
  rw [harg]

/-- **Per-block witness count.**  The number of `r ∈ [1,q]` with `blkY α q m r < τ` is at most
`2τ + 2`. -/
theorem blkY_count (α : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q)
    (hcop : Nat.Coprime (Int.natAbs a) q)
    (hα : |α - (a : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) ^ 2)) (m : ℕ) (τ : ℝ) (hτ : 0 ≤ τ) :
    (((Finset.Icc 1 q).filter (fun r : ℕ => blkY α q m r < τ)).card : ℝ) ≤ 2 * τ + 2 := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hdist : dist ((q : ℝ) * α) (a : ℝ) < 1 / (q : ℝ) := by
    rw [Real.dist_eq]
    have hkey : (q : ℝ) * α - (a : ℝ) = (q : ℝ) * (α - (a : ℝ) / (q : ℝ)) := by
      rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt hqpos)]
    rw [hkey, abs_mul, abs_of_pos hqpos]
    calc (q : ℝ) * |α - (a : ℝ) / (q : ℝ)| < (q : ℝ) * (1 / ((q : ℝ) ^ 2)) :=
          mul_lt_mul_of_pos_left hα hqpos
      _ = 1 / (q : ℝ) := by field_simp
  have h := win_count q hq a hcop ((q : ℝ) * α) ((m : ℝ) * (q : ℝ) ^ 2 * α) hdist τ hτ
  have hset : (Finset.Icc 1 q).filter
        (fun r : ℕ => qDist q ((r : ℝ) * ((q : ℝ) * α) + (m : ℝ) * (q : ℝ) ^ 2 * α) < τ)
      = (Finset.Icc 1 q).filter (fun r : ℕ => blkY α q m r < τ) := by
    apply Finset.filter_congr
    intro r _
    rw [blkY_eq_qDist α q m r hq]
  rwa [hset] at h

end

end Work.TMComp.RedC7
