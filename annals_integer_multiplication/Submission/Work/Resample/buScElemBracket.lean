import Mathlib
import Submission.Work.Resample.buQWscalDefs

namespace Work.Resample
open HvdH

/-- Size bound for an integer: if `|z| ≤ 2^q` then `isz z ≤ q + 3`
(its `natAbs` has at most `q + 1` bits, and the encoding adds two glyphs). -/
private theorem isz_le_of_natAbs_le {z : ℤ} {q : ℕ} (h : z.natAbs ≤ 2 ^ q) :
    isz z ≤ q + 3 := by
  have h1 : z.natAbs.size ≤ q + 1 := by
    rw [Nat.size_le]
    exact lt_of_le_of_lt h (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self q))
  simp only [isz]
  omega

/-- The size bracket of the element word of the scaling `zipWith`: for a weight with
`8|W| ≤ 3·2^p`, coordinates `|a|,|b| ≤ 2^(p+1)` and the divisor `D = 2^p`, the sizes add up to
at most `18(p+1)`.  `isz W ≤ p+2`, `isz a, isz b ≤ p+4`, `isz (2^p) = p+3`. -/
theorem buScElemBracket (p : ℕ) (W a b : ℤ) (hW : 8 * W.natAbs ≤ 3 * 2 ^ p)
    (ha : a.natAbs ≤ 2 ^ (p + 1)) (hb : b.natAbs ≤ 2 ^ (p + 1)) :
    isz W + isz a + isz b + isz ((2 : ℤ) ^ p) + 1 ≤ 18 * (p + 1) := by
  -- `8|W| ≤ 3·2^p` forces `|W| ≤ 2^p`.
  have hWabs : W.natAbs ≤ 2 ^ p := by omega
  have hWsz : isz W ≤ p + 3 := isz_le_of_natAbs_le hWabs
  have hasz : isz a ≤ p + 1 + 3 := isz_le_of_natAbs_le ha
  have hbsz : isz b ≤ p + 1 + 3 := isz_le_of_natAbs_le hb
  have hDabs : ((2 : ℤ) ^ p).natAbs ≤ 2 ^ (p + 1) := by
    have h2 : ((2 : ℤ) ^ p).natAbs = 2 ^ p := by rw [Int.natAbs_pow]; norm_num
    rw [h2]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hDsz : isz ((2 : ℤ) ^ p) ≤ p + 1 + 3 := isz_le_of_natAbs_le hDabs
  omega

end Work.Resample
