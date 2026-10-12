import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Submission.Work.BoseSym.BoxTest
import Submission.Work.BoseSym.Bridge.l2Sq_graphPoint_box
import Submission.Work.BoseSym.Perm.continuous_symAvgAmb
import Submission.Work.BoseSym.Perm.symAvgAmb_eq_of_isSym
import Submission.Work.BoseSym.Perm.symAvgAmb_graphPoint
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSym.Main

/-!
# Eventually the symmetrised trial functions do not vanish

If `graphPoint N L (F n)` converges to a permutation-invariant `p ∈ Hsub N L` of
`L²`-norm `1`, then eventually the symmetrisation `symTest N L (F n)` is not the
zero function.

Proof.  The key is the commuting identity `symAvgAmb N (graphPoint N L F)
= graphPoint N L (symTest N L F)` (`Perm.symAvgAmb_graphPoint`), combined with
continuity of the group average (`Perm.continuous_symAvgAmb`).  The limit
`symAvgAmb N p` equals `p` (`Perm.symAvgAmb_eq_of_isSym`), hence is nonzero
because `l2Sq p = 1`.  So `symAvgAmb N (graphPoint N L (F n)) ≠ 0` eventually;
if `symTest N L (F n)` were the zero function, its graph point — and therefore
the symmetrisation average of `graphPoint N L (F n)` — would vanish.
-/

theorem eventually_symTest_ne_zero {N : ℕ} {L : ℝ} {p : Hsub N L}
    (hp : l2Sq (p : Amb N) = 1) (hpsym : IsSym N (p : Amb N))
    {F : ℕ → testSub N L}
    (hF : Filter.Tendsto (fun n => graphPoint N L (F n)) Filter.atTop (nhds (p : Amb N))) :
    ∀ᶠ n in Filter.atTop, (symTest N L (F n) : Conf N → ℝ) ≠ 0 := by
  -- the symmetrisation average of the limit is the limit itself, hence nonzero
  have hpne : symAvgAmb N (p : Amb N) ≠ 0 := by
    intro h0
    have hp0 : (p : Amb N) = 0 := by
      rw [← Perm.symAvgAmb_eq_of_isSym hpsym]
      exact h0
    have h1 : l2Sq (0 : Amb N) = 1 := by rw [← hp0]; exact hp
    simp [l2Sq] at h1
  -- by continuity the symmetrisation average stays nonzero eventually
  have hlim : Filter.Tendsto (fun n => symAvgAmb N (graphPoint N L (F n))) Filter.atTop
      (nhds (symAvgAmb N (p : Amb N))) :=
    ((Perm.continuous_symAvgAmb N).tendsto (p : Amb N)).comp hF
  have hγ : ∀ᶠ z in nhds (symAvgAmb N (p : Amb N)), z ≠ (0 : Amb N) :=
    eventually_ne_nhds hpne
  have hev : ∀ᶠ n in Filter.atTop, symAvgAmb N (graphPoint N L (F n)) ≠ 0 :=
    Filter.Tendsto.eventually (p := fun z => z ≠ (0 : Amb N)) hlim hγ
  filter_upwards [hev] with n hn
  intro hzero
  exact hn (by
    rw [Perm.symAvgAmb_graphPoint, show symTest N L (F n) = 0 from Subtype.ext hzero]
    exact map_zero (Perm.graphPointLin N L))

end Work.BoseSym.Main
