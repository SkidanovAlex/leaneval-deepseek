import Mathlib
import Submission.Work.RHContract.A.RegionI.Defs
import Submission.Work.RHContract.A.RegionI.cF_basic
import Submission.Work.RHContract.A.RegionI.Core

namespace Work.RHContract.A.RegionI

/-- If `cF (y k + 1) (k+1) < ε`, `1 ≤ y k` and `y k < p` (`k : Fin K`), then
`⌊caMu p ε⌋₊ ≤ k`.  (The hypothesis `1 ≤ y k` is needed: `cF 1 j = 0` is a junk value, so
without it the statement is false.)

`cF` is decreasing in the prime argument and `y k + 1 ≥ 2`, so
`cF p (k+1) ≤ cF (y k + 1) (k+1) < ε`; hence `¬ (ε ≤ cF p (k+1))`, i.e.
`¬ ((k+1 : ℝ) ≤ caMu p ε)` by `Commons.NumberTheory.Robin.caMu_ge_iff_caF`.)

Useful: `Work.RHContract.A.RegionI.cFBasic.cF_anti_p` from
`Submission.Work.RHContract.A.RegionI.cF_basic`. -/
theorem caExp_le_of_gt_y
    (ε : ℝ) (hε : 0 < ε) (K : ℕ) (y : Fin K → ℕ)
    (hy1k : ∀ k : Fin K, 1 ≤ y k)
    (hyc : ∀ k : Fin K, Work.RHContract.RegionI.cF (y k + 1) (k.val + 1) < ε)
    (k : Fin K) (p : ℕ) (hp : 2 ≤ p) (hpy : y k < p) :
    ⌊Work.RHPlan.caMu p ε⌋₊ ≤ k.val := by
  have hlt : ⌊Work.RHPlan.caMu p ε⌋₊ < k.val + 1 :=
    Work.RHContract.RegionI.level_lt (ε := ε) hε (p := p) (y := y k) (k := k.val + 1)
      hp (hy1k k) (by omega) hpy (hyc k)
  omega

end Work.RHContract.A.RegionI
