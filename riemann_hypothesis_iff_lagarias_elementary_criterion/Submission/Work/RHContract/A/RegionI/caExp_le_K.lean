import Mathlib
import Submission.Work.RHContract.A.RegionI.Defs
import Submission.Work.RHContract.A.RegionI.cF_basic

namespace Work.RHContract.A.RegionI

/-- If `cF 2 (K+1) < ε` and `2 ≤ p`, then `⌊caMu p ε⌋₊ ≤ K`.
(`cF p (K+1) ≤ cF 2 (K+1) < ε`, so `¬ (ε ≤ cF p (K+1))` and by
`Commons.NumberTheory.Robin.caMu_ge_iff_caF` we get `¬ ((K+1 : ℝ) ≤ caMu p ε)`, whence the
floor is `≤ K`.)

Useful: `Work.RHContract.A.RegionI.cFBasic.cF_anti_p` from
`Submission.Work.RHContract.A.RegionI.cF_basic`. -/
theorem caExp_le_K
    (ε : ℝ) (hε : 0 < ε) (K : ℕ) (hK : 1 ≤ K)
    (hKtop : Work.RHContract.RegionI.cF 2 (K + 1) < ε)
    (p : ℕ) (hp : 2 ≤ p) :
    ⌊Work.RHPlan.caMu p ε⌋₊ ≤ K := by
  -- `cF (·) (K+1)` is antitone in the prime argument, so `cF p (K+1) ≤ cF 2 (K+1)`.
  have hcf : Work.RHContract.RegionI.cF p (K + 1) ≤ Work.RHContract.RegionI.cF 2 (K + 1) := by
    rcases eq_or_lt_of_le hp with h | h
    · rw [← h]
    · exact le_of_lt
        (cFBasic.cF_anti_p (p := 2) (q := p) (k := K + 1) le_rfl hp (by omega) h)
  -- hence `cF p (K+1) < ε`.
  have hcfε : Work.RHContract.RegionI.cF p (K + 1) < ε := lt_of_le_of_lt hcf hKtop
  -- unfold `caMu_ge_iff_caF` to get `(K+1 : ℝ) ≤ caMu p ε → ε ≤ cF p (K+1)`.
  have hiff := Commons.NumberTheory.Robin.caMu_ge_iff_caF p ε (K + 1) hp hε (by omega)
  have hval : Work.RHPlan.caMu p ε < (K + 1 : ℝ) := by
    by_contra hcon
    have hcon' : (K + 1 : ℝ) ≤ Work.RHPlan.caMu p ε := le_of_not_gt hcon
    have hle : ε ≤ Work.RHContract.RegionI.cF p (K + 1) := by
      have h := hiff.mp (by simpa [Work.RHPlan.caMu] using hcon')
      simpa [Work.RHContract.RegionI.cF] using h
    linarith
  have hge : (0 : ℝ) ≤ Work.RHPlan.caMu p ε := by
    have hpos := Commons.NumberTheory.Robin.caMu_pos (p := p) (ε := ε) hp hε
    simpa [Work.RHPlan.caMu] using le_of_lt hpos
  have hlt : ⌊Work.RHPlan.caMu p ε⌋₊ < K + 1 := by
    rw [Nat.floor_lt hge]
    exact_mod_cast hval
  omega

end Work.RHContract.A.RegionI
