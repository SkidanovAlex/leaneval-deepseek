import Submission.Work.DFT.rootSum

/-!
# Root-of-unity sum with integer frequency (integer-index bookkeeping)

`Work.DFT.rootSumZ` is the `c : ℤ` form of the geometric root-of-unity sum
`Work.DFT.rootSum`: the sum over `q : Fin t` of `exp(2πi·c·q/t)` equals `t`
when `t ∣ c` and `0` otherwise.

The only difference from `Work.DFT.rootSum` is the order of the hypotheses
(`ht` before `c`), so the proof is a direct application.
-/

namespace Work.DFT

theorem rootSumZ (t : ℕ) (ht : 0 < t) (c : ℤ) :
    (∑ q : Fin t, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((c : ℝ) * (q : ℝ)) / (t : ℝ) : ℝ))) =
      if (t : ℤ) ∣ c then (t : ℂ) else 0 :=
  rootSum t c ht

end Work.DFT
