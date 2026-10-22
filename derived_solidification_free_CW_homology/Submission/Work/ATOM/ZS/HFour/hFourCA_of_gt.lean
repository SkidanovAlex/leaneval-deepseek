import Mathlib
import Submission.Work.ATOM.ZS.HFour.Helpers

namespace Work.ATOM.ZS.HFour

/-- **The `k > n(j)` case of the closed cover of `(ℕ∪∞) × T'`** (for `Work.ATOM.ZS.hFour_cover`).

Let `w = (k,t)` be a point of `Work.ATOM.ZS.hFourW S = (ℕ∪∞) ⊗ T' S` with `k = m : ℕ` and `t` over
the finite index `j`, i.e. `tProj S t = j` (so `t = (j, a_j)` and `pr₂ t = a_j`).  If
`n(j) = Work.ATOM.lvl S j < m`, then `w` lies in the first closed piece `Work.ATOM.ZS.hFourCA S`:
both `ψ`-terms are `∞` (`Work.ATOM.ZS.psiFun_pr2T_eq_infty`,
`Work.ATOM.ZS.psiFun_betaT_eq_infty`), and the two `φ`-terms are `∞` because `n(j) < m` and
`n(j) < m+1` (`Work.ATOM.phiPFun_some_some_of_lt`). -/
lemma hFourCA_of_gt (S : LightProfinite.{0}) [Infinite S] {m j : ℕ} (w : ↥(Work.ATOM.ZS.hFourW S))
    (hm : w.1 = ((m : ℕ) : LightProfinite.NatUnionInfty))
    (hj : Work.ATOM.tProj S w.2 = ((j : ℕ) : LightProfinite.NatUnionInfty))
    (h : Work.ATOM.lvl S j < m) : w ∈ Work.ATOM.ZS.hFourCA S := by
  rw [Work.ATOM.ZS.hFourCA]
  refine ⟨?_, ?_⟩
  · rw [Work.ATOM.ZS.hFourPsi1_apply, Work.ATOM.ZS.hFourPsi2_apply, hm,
      Work.ATOM.ZS.psiFun_pr2T_eq_infty w.2 hj h,
      Work.ATOM.ZS.psiFun_betaT_eq_infty w.2 hj (le_of_lt h)]
  · rw [Work.ATOM.ZS.hFourQ1_apply, Work.ATOM.ZS.hFourQ2_apply, hm, hj,
      Work.ATOM.ZS.shift_some, Work.ATOM.phiPFun_some_some_of_lt h,
      Work.ATOM.phiPFun_some_some_of_lt (show Work.ATOM.lvl S j < m + 1 by omega)]

end Work.ATOM.ZS.HFour
