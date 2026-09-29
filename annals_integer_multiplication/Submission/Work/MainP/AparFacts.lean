import Mathlib
import Submission.Work.MainP.basic
import Submission.Work.MainP.sqrt_twelve_mul
import Submission.Work.MainP.apar_sq_le
import Submission.Work.MainP.apar_lin_bounds

/-!
# Facts about `apar` (paper §5.1)

`HvdH.apar n = isqrt (isqrt (12·D²·bpar n − 1)) + 1` with `D = 1729` and `bpar n = clog 2 n`.
Everything about it depends on `b = bpar n` only, so the arithmetic is proved once for a generic
`b ≥ 2^61` (`apar_arith_aux`) and then instantiated at `b = bpar n`.

Writing `X = 12·D²·b`, `m = isqrt (X − 1)`, `α = isqrt m + 1`:

* **(lower)** `X − 1 < (m+1)²` and `m + 1 ≤ α²`, hence `X ≤ α⁴`; and `24·D·b ≤ X = 12·D²·b`
  because `D ≥ 2`; also `m ≥ 1` and hence `α ≥ 2`;
* **(upper)** `α² ≤ 3m + 1 ≤ 3·5990·(isqrt b + 1) + 1 ≤ 17970·(b/2^30 + 1) + 1`
  (`Work.MainP.apar_sq_le`), and this is `< 6b`, and `2Dα² + 13 < b`
  (`Work.MainP.apar_lin_bounds`).
-/

namespace Work.MainP

/-- The `AparFacts` statement for a generic `b ≥ 2^61` (all occurrences of `HvdH.bpar n` replaced by
`b`, `HvdH.D` by `1729`, and `HvdH.ppar n` by `6 * b`). -/
theorem apar_arith_aux (b : ℕ) (hb : 2 ^ 61 ≤ b) :
    12 * 1729 ^ 2 * b ≤ (Nat.sqrt (Nat.sqrt (12 * 1729 ^ 2 * b - 1)) + 1) ^ 4 ∧
    4 * 1729 * (6 * b) ≤ (Nat.sqrt (Nat.sqrt (12 * 1729 ^ 2 * b - 1)) + 1) ^ 4 ∧
    (Nat.sqrt (Nat.sqrt (12 * 1729 ^ 2 * b - 1)) + 1) ^ 2 < 6 * b ∧
    2 * 1729 * (Nat.sqrt (Nat.sqrt (12 * 1729 ^ 2 * b - 1)) + 1) ^ 2 + 13 < b ∧
    2 ≤ Nat.sqrt (Nat.sqrt (12 * 1729 ^ 2 * b - 1)) + 1 := by
  obtain ⟨hlin1, hlin2⟩ := apar_lin_bounds b hb
  have hsq : (Nat.sqrt (Nat.sqrt (12 * 1729 ^ 2 * b - 1)) + 1) ^ 2 ≤
      17970 * (b / 2 ^ 30 + 1) + 1 :=
    by simpa only [HvdH.D] using apar_sq_le b hb
  have hX1 : 1 ≤ 12 * 1729 ^ 2 * b := by omega
  -- `m + 1 ≤ α²` (with `m = sqrt (X-1)`, `α = sqrt m + 1`)
  have hB' : Nat.sqrt (12 * 1729 ^ 2 * b - 1) + 1 ≤
      (Nat.succ (Nat.sqrt (Nat.sqrt (12 * 1729 ^ 2 * b - 1)))) ^ 2 := by
    have h := Nat.lt_succ_sqrt' (Nat.sqrt (12 * 1729 ^ 2 * b - 1))
    omega
  have hB : Nat.sqrt (12 * 1729 ^ 2 * b - 1) + 1 ≤
      (Nat.sqrt (Nat.sqrt (12 * 1729 ^ 2 * b - 1)) + 1) ^ 2 := hB'
  -- `(m+1)² ≤ α⁴`
  have hC : (Nat.sqrt (12 * 1729 ^ 2 * b - 1) + 1) ^ 2 ≤
      (Nat.sqrt (Nat.sqrt (12 * 1729 ^ 2 * b - 1)) + 1) ^ 4 := by
    calc (Nat.sqrt (12 * 1729 ^ 2 * b - 1) + 1) ^ 2
        ≤ ((Nat.sqrt (Nat.sqrt (12 * 1729 ^ 2 * b - 1)) + 1) ^ 2) ^ 2 :=
          Nat.pow_le_pow_left hB 2
      _ = (Nat.sqrt (Nat.sqrt (12 * 1729 ^ 2 * b - 1)) + 1) ^ 4 := by ring
  -- `X ≤ α⁴`
  have hquad : 12 * 1729 ^ 2 * b ≤
      (Nat.sqrt (Nat.sqrt (12 * 1729 ^ 2 * b - 1)) + 1) ^ 4 := by
    have h := Nat.lt_succ_sqrt' (12 * 1729 ^ 2 * b - 1)
    have h' : 12 * 1729 ^ 2 * b - 1 <
        (Nat.sqrt (Nat.sqrt (12 * 1729 ^ 2 * b - 1)) + 1) ^ 4 := h.trans_le hC
    omega
  refine ⟨hquad, ?_, hsq.trans_lt hlin1, ?_, ?_⟩
  · have h24 : 4 * 1729 * (6 * b) ≤ 12 * 1729 ^ 2 * b := by omega
    exact h24.trans hquad
  · have h3458 : 3458 * (Nat.sqrt (Nat.sqrt (12 * 1729 ^ 2 * b - 1)) + 1) ^ 2
        ≤ 3458 * (17970 * (b / 2 ^ 30 + 1) + 1) := Nat.mul_le_mul_left _ hsq
    omega
  · have h2 : 1 ≤ Nat.sqrt (Nat.sqrt (12 * 1729 ^ 2 * b - 1)) :=
      Nat.le_sqrt.mpr (Nat.le_sqrt.mpr (by omega : 1 * 1 ≤ 12 * 1729 ^ 2 * b - 1) :
        1 * 1 ≤ Nat.sqrt (12 * 1729 ^ 2 * b - 1))
    omega

/-- Facts about `apar n = isqrt (isqrt (12*D^2*bpar n - 1)) + 1`, for large `bpar n`.
With `m = isqrt (12D²b-1)`, `α = isqrt m + 1`: `α² > m` and `(m+1)² ≥ 12D²b` give `α⁴ ≥ 12D²b`;
`isqrt b ≤ b/2^30` (from `2^61 ≤ b`, see `Work.MainP.sqrt_le_div`) and
`isqrt(12D²b) ≤ 5990(isqrt b + 1)` give `α² ≤ 3m+1 ≤ 17970(b/2^30 + 1) + 1`,
which is `< 6b` and `2Dα²+13 < b` for `b ≥ 2^61`. -/
theorem AparFacts (n : ℕ) (hb : 2 ^ 61 ≤ HvdH.bpar n) :
    12 * HvdH.D ^ 2 * HvdH.bpar n ≤ HvdH.apar n ^ 4 ∧
    4 * HvdH.D * HvdH.ppar n ≤ HvdH.apar n ^ 4 ∧
    HvdH.apar n ^ 2 < HvdH.ppar n ∧
    2 * HvdH.D * HvdH.apar n ^ 2 + 13 < HvdH.bpar n ∧ 2 ≤ HvdH.apar n := by
  have h := apar_arith_aux (HvdH.bpar n) hb
  simpa [HvdH.apar, HvdH.ppar, HvdH.D] using h

end Work.MainP
