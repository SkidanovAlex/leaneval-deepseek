import Mathlib
import Submission.Work.ATOM.ZS.HFour.Helpers

namespace Work.ATOM.ZS.HFour

/-- **The `k = n(j)` case of the closed cover of `(ℕ∪∞) × T'`** (for `Work.ATOM.ZS.hFour_cover`).

Let `w = (k,t)` be a point of `Work.ATOM.ZS.hFourW S = (ℕ∪∞) ⊗ T' S` with `k = m : ℕ` and `t` over
the finite index `j`, i.e. `tProj S t = j` (so `t = (j, a_j)` and `pr₂ t = a_j`).  If
`m = n(j) = Work.ATOM.lvl S j`, then `w` lies in the second closed piece `Work.ATOM.ZS.hFourCB S`:
`ψ(k, pr₂ t) = ψ(n(j), a_j) = j = φ_P(n(j), j)` (`Work.ATOM.ZS.psiFun_lvl_a`,
`Work.ATOM.phiPFun_some_some_of_le`), while `ψ(k, β t) = ∞` (`Work.ATOM.ZS.psiFun_betaT_eq_infty`)
and `φ_P(k+1, j) = ∞` because `n(j) < n(j)+1` (`Work.ATOM.phiPFun_some_some_of_lt`). -/
lemma hFourCB_of_eq (S : LightProfinite.{0}) [Infinite S] {m j : ℕ} (w : ↥(Work.ATOM.ZS.hFourW S))
    (hm : w.1 = ((m : ℕ) : LightProfinite.NatUnionInfty))
    (hj : Work.ATOM.tProj S w.2 = ((j : ℕ) : LightProfinite.NatUnionInfty))
    (h : m = Work.ATOM.lvl S j) : w ∈ Work.ATOM.ZS.hFourCB S := by
  constructor
  · -- `ψ(m, pr₂ t) = ψ(n(j), a_j) = j = φ_P(n(j), j)`
    rw [Work.ATOM.ZS.hFourPsi1_apply, Work.ATOM.ZS.hFourQ1_apply, hm, h,
      Work.ATOM.ZS.pr₂T_of_finite w.2 hj, Work.ATOM.ZS.psiFun_lvl_a, hj,
      Work.ATOM.phiPFun_some_some_of_le (k := Work.ATOM.lvl S j) le_rfl]
  · -- `ψ(m, β t) = ∞ = φ_P(n(j)+1, j)`
    rw [Work.ATOM.ZS.hFourPsi2_apply, Work.ATOM.ZS.hFourQ2_apply, hm, h,
      Work.ATOM.ZS.psiFun_betaT_eq_infty w.2 hj le_rfl, hj, Work.ATOM.ZS.shift_some,
      Work.ATOM.phiPFun_some_some_of_lt (k := Work.ATOM.lvl S j + 1) (by omega)]

end Work.ATOM.ZS.HFour
