import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Submission.Work.BoseSym.Form.tendsto_potSq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Sequential continuity of the Dirichlet form

`dirForm W p = gSq p + potSq W p` where `gSq p = ∑_j ‖p.2 j‖²` is the squared
gradient norm and `potSq W p = ∫ W · (p.1)²` is the potential energy.

The gradient term is continuous on the ambient space `Amb N` (it is a finite
sum of squared norms of evaluations), and the potential term is sequentially
continuous on the `L²` part by `tendsto_potSq` (boundedness `BddBy` and a.e.
measurability `AEMeas` of the weight `W`).  Adding the two gives

`u n → v  ⟹  dirForm W (u n) → dirForm W v`.
-/

namespace Work.BoseSym.Bridge

open MeasureTheory Filter
open scoped Topology

/-- The squared gradient norm `gSq` is continuous on the ambient space. -/
lemma continuous_gSq {N : ℕ} : Continuous (gSq (N := N)) := by
  unfold gSq
  refine continuous_finsetSum _ (fun j _ => ?_)
  exact (((continuous_apply j).comp continuous_snd).norm).pow 2

theorem tendsto_dirForm {N : ℕ} {W : Work.BoseSym.Conf N → ℝ} {C : ℝ}
    (hW : Work.BoseSym.BddBy N W C) (hWm : Work.BoseSym.AEMeas N W)
    {u : ℕ → Work.BoseSym.Amb N} {v : Work.BoseSym.Amb N}
    (h : Filter.Tendsto u Filter.atTop (nhds v)) :
    Filter.Tendsto (fun n => Work.BoseSym.dirForm W (u n)) Filter.atTop
      (nhds (Work.BoseSym.dirForm W v)) := by
  -- the gradient part converges by continuity of `gSq`
  have hg : Filter.Tendsto (fun n => gSq (u n)) Filter.atTop (nhds (gSq v)) :=
    (continuous_gSq (N := N)).continuousAt.tendsto.comp h
  -- the potential part converges by the weighted quadratic form estimate
  have hfst : Filter.Tendsto (fun n => (u n).1) Filter.atTop (nhds v.1) :=
    continuous_fst.continuousAt.tendsto.comp h
  have hpot : Filter.Tendsto (fun n => potSq W (u n)) Filter.atTop (nhds (potSq W v)) :=
    Form.tendsto_potSq hW hWm hfst
  simpa [dirForm] using hg.add hpot

end Work.BoseSym.Bridge
