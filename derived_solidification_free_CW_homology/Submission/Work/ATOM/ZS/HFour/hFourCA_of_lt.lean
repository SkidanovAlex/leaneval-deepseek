import Mathlib
import Submission.Work.ATOM.ZS.HFour.Helpers

namespace Work.ATOM.ZS.HFour

/-- **The `k < n(j)` case of the closed cover of `(ℕ∪∞) × T'`** (for `Work.ATOM.ZS.hFour_cover`).

Let `w = (k,t)` be a point of `Work.ATOM.ZS.hFourW S = (ℕ∪∞) ⊗ T' S` with `k = m : ℕ` and `t` over
the finite index `j`, i.e. `tProj S t = j` (so `t = (j, a_j)` and `pr₂ t = a_j`).  If
`m < n(j) = Work.ATOM.lvl S j`, then `w` lies in the first closed piece `Work.ATOM.ZS.hFourCA S`:
the two `ψ`-terms agree because `e_m (e_{n(j)-1} a_j) = e_m a_j` (via
`Work.ATOM.ZS.e_comp_apply` and `Work.ATOM.ZS.psiFun_dep`), and the two `φ`-terms both equal `j`
because `m ≤ n(j)` and `m+1 ≤ n(j)` (`Work.ATOM.phiPFun_some_some_of_le`). -/
lemma hFourCA_of_lt (S : LightProfinite.{0}) [Infinite S] {m j : ℕ} (w : ↥(Work.ATOM.ZS.hFourW S))
    (hm : w.1 = ((m : ℕ) : LightProfinite.NatUnionInfty))
    (hj : Work.ATOM.tProj S w.2 = ((j : ℕ) : LightProfinite.NatUnionInfty))
    (h : m < Work.ATOM.lvl S j) : w ∈ Work.ATOM.ZS.hFourCA S := by
  constructor
  · -- the two `ψ`-terms agree: `ψ(m, a_j) = ψ(m, e_{n(j)-1} a_j)`
    rw [Work.ATOM.ZS.hFourPsi1_apply, Work.ATOM.ZS.hFourPsi2_apply, hm,
      Work.ATOM.ZS.pr₂T_of_finite w.2 hj, Work.ATOM.ZS.betaT_of_finite w.2 hj,
      ite_eq_right (by omega : ¬ (Work.ATOM.lvl S j = 0))]
    refine Work.ATOM.ZS.psiFun_dep (S := S) ?_
    rw [Work.ATOM.ZS.e_comp_apply,
      Nat.min_eq_right (by omega : m ≤ Work.ATOM.lvl S j - 1)]
  · -- the two `φ`-terms are both `j`
    rw [Work.ATOM.ZS.hFourQ1_apply, Work.ATOM.ZS.hFourQ2_apply, hm, hj,
      Work.ATOM.ZS.shift_some m]
    rw [Work.ATOM.phiPFun_some_some_of_le (S := S) (le_of_lt h),
      Work.ATOM.phiPFun_some_some_of_le (S := S) (by omega : m + 1 ≤ Work.ATOM.lvl S j)]

end Work.ATOM.ZS.HFour
