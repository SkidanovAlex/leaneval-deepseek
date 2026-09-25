import Mathlib
import Submission.Work.RHContract.A.RegionI.Defs
import Submission.Work.RHContract.A.RegionI.cF_basic

namespace Work.RHContract.A.RegionI

/-- If `ε ≤ cF (x k) (k+1)` and `p ≤ x k` (`k : Fin K`), then `k+1 ≤ ⌊caMu p ε⌋₊`.
(`cF q j = log(1 + 1/S_j(q))/log q` is decreasing in the prime argument `q`, so
`ε ≤ cF (x k) (k+1) ≤ cF p (k+1)`; and `k+1 ≤ ⌊caMu p ε⌋₊ ↔ ε ≤ cF p (k+1)` is
`Commons.NumberTheory.Robin.caMu_ge_iff_caF`.)

Useful: `Work.RHContract.A.RegionI.cFBasic.cF_anti_p` (`cF q k < cF p k` for `p < q`,
`2 ≤ p`, `2 ≤ q`, `1 ≤ k`) from `Submission.Work.RHContract.A.RegionI.cF_basic`. -/
theorem caExp_ge_of_le_x
    (ε : ℝ) (hε : 0 < ε) (K : ℕ) (x : Fin K → ℕ)
    (hxc : ∀ k : Fin K, ε ≤ Work.RHContract.RegionI.cF (x k) (k.val + 1))
    (hxlo : ∀ k : Fin K, 2 ≤ x k)
    (k : Fin K) (p : ℕ) (hp : 2 ≤ p) (hpx : p ≤ x k) :
    k.val + 1 ≤ ⌊Work.RHPlan.caMu p ε⌋₊ := by
  -- `cF (·) (k+1)` is antitone in the prime argument, so `cF (x k) (k+1) ≤ cF p (k+1)`.
  have h2 : Work.RHContract.RegionI.cF (x k) (k.val + 1) ≤ Work.RHContract.RegionI.cF p (k.val + 1) := by
    rcases lt_or_eq_of_le hpx with hlt | heq
    · exact le_of_lt (Work.RHContract.A.RegionI.cFBasic.cF_anti_p hp (hxlo k) (by omega) hlt)
    · rw [heq]
  have h3 : ε ≤ Work.RHContract.RegionI.cF p (k.val + 1) := le_trans (hxc k) h2
  -- `(k+1 : ℝ) ≤ caMu p ε ↔ ε ≤ cF p (k+1)`, then take floors.
  have hm : ((k.val + 1 : ℕ) : ℝ) ≤ Work.RHPlan.caMu p ε := by
    have hiff := Commons.NumberTheory.Robin.caMu_ge_iff_caF p ε (k.val + 1) hp hε (by omega)
    exact hiff.mpr h3
  exact Nat.le_floor hm

end Work.RHContract.A.RegionI
