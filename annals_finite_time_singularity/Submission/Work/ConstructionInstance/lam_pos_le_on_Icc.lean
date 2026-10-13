import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.ConstructionInstance.Reduced

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- **A uniform positive lower bound for `λ̄` on the initial strip `[0,S]`.**

The hypotheses are exactly the `λ̄`-fields of the construction: `λ̄` is positive on
`preWindow T = (-2,T)` and differentiable (hence continuous) there, and `0 ≤ S < T`.  Then
`Set.Icc 0 S` is a compact interval contained in the open half-window `preWindow T`, so the
continuous function `λ̄` attains its minimum there, and that minimum is positive because
`λ̄ > 0` on `preWindow T`. -/
theorem lam_pos_le_on_Icc {lam : ℝ → ℝ} {T S : ℝ} (hS : 0 ≤ S) (hST : S < T)
    (hlam : ∀ t ∈ preWindow T, 0 < lam t)
    (hlamdif : ∀ t ∈ preWindow T, HasDerivAt lam (deriv lam t) t) :
    ∃ m : ℝ, 0 < m ∧ ∀ t ∈ Set.Icc 0 S, m ≤ lam t := by
  have hsub : Set.Icc (0 : ℝ) S ⊆ preWindow T := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2, hST]⟩
  have hcontpre : ContinuousOn lam (preWindow T) :=
    fun t ht => (hlamdif t ht).continuousAt.continuousWithinAt
  have hcont : ContinuousOn lam (Set.Icc (0 : ℝ) S) := hcontpre.mono hsub
  have hne : (Set.Icc (0 : ℝ) S).Nonempty := ⟨0, by simp [hS]⟩
  obtain ⟨a, ha, hmin⟩ := isCompact_Icc.exists_isMinOn hne hcont
  exact ⟨lam a, hlam a (hsub ha), fun t ht => hmin ht⟩

end Work.ConstructionInstance
