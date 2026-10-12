import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Submission.Work.BoseSym.BoxTest
import Submission.Work.BoseSym.Bridge.tendsto_dirForm
import Submission.Work.BoseSym.Perm.continuous_symAvgAmb
import Submission.Work.BoseSym.Perm.symAvgAmb_eq_of_isSym
import Submission.Work.BoseSym.Perm.symAvgAmb_graphPoint
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSym.Main

open MeasureTheory Filter
open scoped Topology

/-- `l2Sq` is continuous on the ambient space. -/
private lemma continuous_l2Sq_amb {N : ℕ} : Continuous (fun p : Amb N => l2Sq p) := by
  simp only [l2Sq]
  exact (continuous_fst.norm).pow 2

theorem tendsto_symTest_quot {N : ℕ} {L : ℝ} {W : Conf N → ℝ} {C : ℝ} (hW : BddBy N W C)
    (hWm : AEMeas N W) {p : Hsub N L} (hp : l2Sq (p : Amb N) = 1) (hpsym : IsSym N (p : Amb N))
    {F : ℕ → testSub N L}
    (hF : Filter.Tendsto (fun n => graphPoint N L (F n)) Filter.atTop (nhds (p : Amb N))) :
    Filter.Tendsto (fun n => dirForm W (graphPoint N L (symTest N L (F n)))
        / l2Sq (graphPoint N L (symTest N L (F n)))) Filter.atTop
      (nhds (dirForm W (p : Amb N))) := by
  -- the symmetrised graph points converge, because `symAvgAmb` is continuous
  -- and fixes the symmetric limit `p`
  have hsymlim : Filter.Tendsto (fun n => symAvgAmb N (graphPoint N L (F n)))
      Filter.atTop (nhds (p : Amb N)) := by
    have h1 : Filter.Tendsto (fun n => symAvgAmb N (graphPoint N L (F n)))
        Filter.atTop (nhds (symAvgAmb N (p : Amb N))) :=
      ((Perm.continuous_symAvgAmb N).tendsto (p : Amb N)).comp hF
    rwa [Perm.symAvgAmb_eq_of_isSym hpsym] at h1
  -- transport along `symAvgAmb N ∘ graphPoint = graphPoint ∘ symTest`
  have hgp : Filter.Tendsto (fun n => graphPoint N L (symTest N L (F n)))
      Filter.atTop (nhds (p : Amb N)) := by
    have hcongr : (fun n => symAvgAmb N (graphPoint N L (F n)))
        = fun n => graphPoint N L (symTest N L (F n)) :=
      funext fun n => Perm.symAvgAmb_graphPoint (F n)
    rwa [hcongr] at hsymlim
  have hdir := Bridge.tendsto_dirForm hW hWm hgp
  have hl2 : Filter.Tendsto (fun n => l2Sq (graphPoint N L (symTest N L (F n))))
      Filter.atTop (nhds (l2Sq (p : Amb N))) :=
    ((continuous_l2Sq_amb (N := N)).tendsto (p : Amb N)).comp hgp
  have hne : l2Sq (p : Amb N) ≠ 0 := by rw [hp]; norm_num
  have hquot := hdir.div hl2 hne
  rw [hp, div_one] at hquot
  exact hquot

end Work.BoseSym.Main
