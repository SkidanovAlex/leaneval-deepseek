import Mathlib
import Submission.Work.ANum.Ivl

/-! # A fixed-point logarithm for the certificate

`log x` for `x ∈ [1/2, 2]` is `2·atanh((x-1)/(x+1))` with `|(x-1)/(x+1)| ≤ 1/3`, so the Taylor
polynomial `Σ_{i<K} 2v^{2i+1}/(2i+1)` plus the geometric tail
`2·(1/3)^{2K+1}/((2K+1)·(1-1/9))` (a *constant*, since `|v| ≤ 1/3`) encloses `log x`.

All operations are integer mantissas at scale `SC = 2^30` (`Work.ANum.Ivl`); the soundness lemma
`log_mem` is proved in the sibling module `Submission.Work.ANum.log_mem`. -/

namespace Work.ANum

noncomputable section

namespace Iv

/-- Interval division by a positive natural number (outward rounding). -/
def divN (I : Iv) (n : ℕ) : Iv := ⟨Int.ediv I.lo (n : ℤ), -Int.ediv (-I.hi) (n : ℤ)⟩

/-- Accumulator for `Σ_{i<K} 2·v^{2i+1}/(2i+1)`: `fuel` steps, `i` the current index, `p` the
current odd power `v^{2i+1}`, `acc` the partial sum. -/
def logSumAux (v2 : Iv) : ℕ → ℕ → Iv → Iv → Iv
  | 0, _, _, acc => acc
  | fuel + 1, i, p, acc => logSumAux v2 fuel (i + 1) (p.mul v2) (acc.add (divN (p.add p) (2 * i + 1)))

/-- The `K`-term Taylor polynomial of `2·atanh` at an interval `V` containing `v`. -/
def logSum (V : Iv) (K : ℕ) : Iv := logSumAux (V.mul V) K 0 V (pt 0)

/-- Mantissa bound for the tail `2·(1/3)^{2K+1}/((2K+1)·(1-1/9))` at scale `SC`. -/
def logTailN (K : ℕ) : ℤ :=
  Int.ediv (9 * SC) (4 * ((2 * K + 1) * 3 ^ (2 * K + 1))) + 1

/-- The tail interval `[-logTailN K, logTailN K]/SC`. -/
def logTail (K : ℕ) : Iv := ⟨-(logTailN K), logTailN K⟩

end Iv

end

end Work.ANum
