import Mathlib

namespace Work.SB.BW2

/-- Elementary cost arithmetic: with `va ≤ 4 Bg`, `vA ≤ Ss`, `vB ≤ Ss` and `Bg ≥ 1`,
the "drop two" cost expression is bounded by `(20 KR + 2 KD) (Bg + Ss)`. -/
theorem dropTwoCostArith (KR KD va vA vB Bg Ss : ℕ)
    (hBg : 1 ≤ Bg) (hva : va ≤ 4 * Bg) (hA : vA ≤ Ss) (hB : vB ≤ Ss) :
    ((2 * KR * (va + vB + 1) + KD * (vB + 1)) + 2 * KR * (va + vA + 1)) + KD * (vA + 1)
      ≤ (20 * KR + 2 * KD) * (Bg + Ss) := by
  nlinarith [hBg, hva, hA, hB]

end Work.SB.BW2
