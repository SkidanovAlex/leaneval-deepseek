import Mathlib
import Submission.Work.IntLib.drainCost

/-!
# The pre-phase cost bound

Pure `ℕ` arithmetic bookkeeping used by the `Main` assembly: the codes returned by the
pre-phase (`n1`, `n2`, `n5`, `n6`) are bounded by a single linear expression in the
parameters of the computation.
-/

namespace Work.IntLib

/-- `HvdH.isz` of a natural cast to `ℤ` is `n.size + 2`. -/
theorem isz_natCast' (n : ℕ) : HvdH.isz (n : ℤ) = n.size + 2 := by
  simp [HvdH.isz, Int.natAbs_natCast]

theorem preMainCostBound (KR b N iszx iszN C n1 n2 n5 n6 : ℕ) (hb : 1 ≤ b) (hN : 1 ≤ N)
    (hn1 : n1 ≤ 5 * (HvdH.isz (b : ℤ) + 1) + 2) (hn2 : n2 ≤ KR * (b.size + b + 1))
    (hn5 : n5 ≤ 17) (hn6 : n6 ≤ C) :
    n1 + (n2 + (1 + (1 + (n5 + n6)))) ≤
      (2 * KR + 100) * (iszx + HvdH.isz (b : ℤ) + iszN + N * (b + 1) + 1) + C := by
  have hiz : HvdH.isz (b : ℤ) = b.size + 2 := isz_natCast' b
  -- `b.size + b + 1` is dominated by `2 * S` where `S` is the big bracket.
  have hbnd : b.size + b + 1 ≤ 2 * (iszx + HvdH.isz (b : ℤ) + iszN + N * (b + 1) + 1) := by
    rw [hiz]
    nlinarith [hN, Nat.zero_le b, Nat.zero_le iszx, Nat.zero_le iszN, Nat.zero_le b.size]
  have hn1' : n1 ≤ 5 * (iszx + HvdH.isz (b : ℤ) + iszN + N * (b + 1) + 1) + 2 := by
    nlinarith [hn1, Nat.zero_le iszx, Nat.zero_le iszN, Nat.zero_le (N * (b + 1))]
  have hn2' : n2 ≤ 2 * KR * (iszx + HvdH.isz (b : ℤ) + iszN + N * (b + 1) + 1) := by
    have h := Nat.mul_le_mul_left KR hbnd
    nlinarith [hn2, h]
  nlinarith [hn1', hn2', hn5, hn6, hbnd, hN, Nat.zero_le KR]

end Work.IntLib
