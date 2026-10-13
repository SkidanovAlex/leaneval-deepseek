import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.Radial.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC.HonestCut

theorem radGreen_hasDerivAt_slots {α : ℝ} (m : ℕ) {c : ℝ → ℝ}
    (hsmooth : ∀ n : ℕ, ContDiffOn ℝ n (fun z => Work.FTS.PhiStar.Radial.radGreen α m c z) (Set.Ioi 0)) :
    (∀ z : ℝ, 0 < z → HasDerivAt (fun z => Work.FTS.PhiStar.Radial.radGreen α m c z)
        (deriv (fun z => Work.FTS.PhiStar.Radial.radGreen α m c z) z) z)
    ∧ (∀ z : ℝ, 0 < z →
        HasDerivAt (deriv (fun z => Work.FTS.PhiStar.Radial.radGreen α m c z))
          (deriv (deriv (fun z => Work.FTS.PhiStar.Radial.radGreen α m c z)) z) z) := by
  constructor
  · intro z hz
    have h1 : ContDiffOn ℝ 1 (fun z => Work.FTS.PhiStar.Radial.radGreen α m c z) (Set.Ioi 0) :=
      hsmooth 1
    have hc : ContDiffAt ℝ 1 (fun z => Work.FTS.PhiStar.Radial.radGreen α m c z) z :=
      h1.contDiffAt (isOpen_Ioi.mem_nhds hz)
    exact (hc.differentiableAt (by norm_num)).hasDerivAt
  · intro z hz
    have h2 : ContDiffOn ℝ 2 (fun z => Work.FTS.PhiStar.Radial.radGreen α m c z) (Set.Ioi 0) :=
      hsmooth 2
    have hd : ContDiffOn ℝ 1 (deriv (fun z => Work.FTS.PhiStar.Radial.radGreen α m c z))
        (Set.Ioi 0) :=
      ContDiffOn.deriv_of_isOpen h2 isOpen_Ioi (by norm_num)
    have hc : ContDiffAt ℝ 1 (deriv (fun z => Work.FTS.PhiStar.Radial.radGreen α m c z)) z :=
      hd.contDiffAt (isOpen_Ioi.mem_nhds hz)
    exact (hc.differentiableAt (by norm_num)).hasDerivAt

end Work.FTS.ClassC.HonestCut
