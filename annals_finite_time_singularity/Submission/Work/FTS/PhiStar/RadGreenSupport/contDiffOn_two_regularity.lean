import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.RadGreenSupport

open Set

theorem contDiffOn_two_regularity {c : ℝ → ℝ} (hc : ContDiffOn ℝ 2 c (Set.Ioi 0)) :
    ContinuousOn c (Set.Ioi 0) ∧ ContinuousOn (deriv c) (Set.Ioi 0) ∧
      ContinuousOn (iteratedDeriv 2 c) (Set.Ioi 0) ∧
      (∀ t : ℝ, 0 < t → HasDerivAt c (deriv c t) t) ∧
      (∀ t : ℝ, 0 < t → HasDerivAt (deriv c) (iteratedDeriv 2 c t) t) := by
  -- `deriv c` is `C^1` and `deriv (deriv c) = iteratedDeriv 2 c` is continuous on the open set
  have h1 : ContDiffOn ℝ 1 (deriv c) (Set.Ioi 0) :=
    hc.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)
  have h2 : ContDiffOn ℝ 0 (deriv (deriv c)) (Set.Ioi 0) :=
    h1.deriv_of_isOpen isOpen_Ioi (m := 0) (by norm_num)
  have hiter : iteratedDeriv 2 c = deriv (deriv c) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  refine ⟨hc.continuousOn, h1.continuousOn, ?_, ?_, ?_⟩
  · rw [hiter]
    exact h2.continuousOn
  · intro t ht
    exact ((hc.contDiffAt (isOpen_Ioi.mem_nhds ht)).hasStrictDerivAt (by norm_num)).hasDerivAt
  · intro t ht
    rw [hiter]
    exact ((h1.contDiffAt (isOpen_Ioi.mem_nhds ht)).hasStrictDerivAt (by norm_num)).hasDerivAt

end Work.FTS.PhiStar.RadGreenSupport
