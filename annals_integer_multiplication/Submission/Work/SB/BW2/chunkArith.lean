import Mathlib
import Submission.Work.SB.BW2.Defs

namespace Work.SB.BW2

open HvdH
open Work.Layout

/-!
## The arithmetic of the `branchWord2` (chunks) stage

With `BIG N L = (N+1)*(L+N.size+1)*(N.size+1)`, the hypothesis `A*m*B ≤ N` forces

* `(A*m*B+1)*(L+1) ≤ BIG N L` — the flat array fits in one `BIG` budget, and
* `A*B*(m*L+m+1) + A*B + 1 ≤ 4 * BIG N L` — the cost of writing the `A*B` chunk words of
  total length `A*B*m*(L+1)` (the `+ A*B` counting the chunk separators, each costing at most
  one `BIG`) is at most four `BIG` budgets.

`0 < m` is used only to deduce `A*B ≤ N` from `A*m*B ≤ N`; the estimates themselves already
hold when `m = 0`.
-/

/-- Both estimates needed for the chunks stage: the array size and the chunk-writing cost are
controlled by the `BIG N L` budget once `A*m*B ≤ N` and `0 < m`. -/
theorem chunkArith (A m B N L : ℕ) (hm : 0 < m) (hAmB : A * m * B ≤ N) :
    (A * m * B + 1) * (L + 1) ≤ Work.SB.BW2.BIG N L ∧
    A * B * (m * L + m + 1) + A * B + 1 ≤ 4 * Work.SB.BW2.BIG N L := by
  have hAB : A * B ≤ N := by
    have h : A * B * m ≤ N := by nlinarith [hAmB]
    exact le_trans (Nat.le_mul_of_pos_right (A * B) hm) h
  have hBIG : 4 * ((N + 1) * (L + 1)) ≤ 4 * BIG N L := by
    refine Nat.mul_le_mul_left 4 ?_
    simp only [BIG]
    calc (N + 1) * (L + 1) ≤ (N + 1) * (L + N.size + 1) :=
          Nat.mul_le_mul_left _ (by omega)
      _ ≤ (N + 1) * (L + N.size + 1) * (N.size + 1) :=
          Nat.le_mul_of_pos_right _ (by omega)
  constructor
  · simp only [BIG]
    calc (A * m * B + 1) * (L + 1) ≤ (N + 1) * (L + 1) :=
          Nat.mul_le_mul_right _ (by omega)
      _ ≤ (N + 1) * (L + N.size + 1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ (N + 1) * (L + N.size + 1) * (N.size + 1) :=
          Nat.le_mul_of_pos_right _ (by omega)
  · have h1 : A * B * (m * L + m + 1) + A * B + 1 ≤ N * (L + 1) + N + N + 1 := by
      nlinarith [hAmB, hAB, hm]
    have h2 : N * (L + 1) + N + N + 1 ≤ 4 * ((N + 1) * (L + 1)) := by nlinarith
    linarith [hBIG]

end Work.SB.BW2
