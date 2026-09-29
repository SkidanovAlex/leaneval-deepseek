import Mathlib
import Submission.Work.CNum.Fx

/-!
# `Work.CNum.PtC2YBound` — the one decidable side condition of `PtC2Spec`

`ptC2` forms the boundary point `psiC (e^{iθ_k})`, `θ_k = 2πk/1024`, as an interval; the square
root of the radicand is taken with `IvS` (the binary-search integer square root `isqrt`, specified
by `IsqrtSpec` only for inputs below `2^70`).  Hence the mantissa bound
`Y.hi * SC < 2^70` — where `Y` is the interval enclosing `2A(γ - cos θ_k)` — has to be checked.

This is a pure integer computation on the `2^30`-mantissa tables `expI k`; the kernel decides all
`535` instances of the range `245 ≤ k ≤ 779` at once.
-/

namespace Work.CNum

open Work.ANum

/-- The interval of `ptC2` enclosing `2·A·(γ - cos θ)`. -/
def ptC2Y (k : ℕ) : Iv :=
  IvM (ratIv 791282 10000)
    (Iv.sub (ratIv 27559 395641) (Iv.sub (Iv.sq (expI k).re) (Iv.sq (expI k).im)))

lemma ptC2Y_eq (k : ℕ) :
    ptC2Y k = IvM (ratIv 791282 10000)
      (Iv.sub (ratIv 27559 395641) (Iv.sub (Iv.sq (expI k).re) (Iv.sq (expI k).im))) := rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem PtC2YBound {k : ℕ} (h1 : 245 ≤ k) (h2 : k ≤ 779) :
    (ptC2Y k).hi.toNat * SC.toNat < 2 ^ 70 := by
  interval_cases k <;> decide +kernel

end Work.CNum
