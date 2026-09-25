import Mathlib
import Submission.Work.RHContract.Corpus

/-!
# Region III: the two scale parameters `ξ = caXi ε` and `n = ⌊√(2.5ξ)⌋₊ + 1`

`ξ(ε) ≥ 10^8` is the region III of the margin lemma.  Write `ξᴿ = (caXi ε : ℝ)` for the
largest prime factor of the colossally abundant number `N_ε` as a *real* number, `L = log ξᴿ`,
and `caN ε = ⌊√(2.5 ξᴿ)⌋₊ + 1` for the lower summation limit used to estimate the `k = 1`
excess `Margin.caC1 ε` from below.

The point of the constant `2.5`: `ξ₂(ε) ≤ √(2.5 ξ) + 1` (`A.caXi2_le_sqrt`), so every prime
`p > caN ε` (and `p ≤ ξ`) contributes to `caC1 ε` with a nonnegative excess.
-/

namespace Work.RHContract.A.RegionIII

noncomputable section

/-- `ξ(ε) = caXi ε` as a real number. -/
def caXiR (ε : ℝ) : ℝ := (Work.RHPlan.caXi ε : ℝ)

/-- `L(ε) = log ξ(ε)`. -/
def caL (ε : ℝ) : ℝ := Real.log (caXiR ε)

/-- `n(ε) = ⌊√(2.5 ξ(ε))⌋₊ + 1`. -/
def caN (ε : ℝ) : ℕ := Nat.floor (Real.sqrt (2.5 * caXiR ε)) + 1

lemma caXiR_eq (ε : ℝ) : caXiR ε = (Work.RHPlan.caXi ε : ℝ) := rfl

lemma caL_eq (ε : ℝ) : caL ε = Real.log (Work.RHPlan.caXi ε : ℝ) := rfl

lemma caN_eq (ε : ℝ) :
    caN ε = Nat.floor (Real.sqrt (2.5 * (Work.RHPlan.caXi ε : ℝ))) + 1 := rfl

end

end Work.RHContract.A.RegionIII
