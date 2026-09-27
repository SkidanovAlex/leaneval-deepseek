import Mathlib
import Submission.Work.SimplyConnected.ABS.GreenSetupReg

namespace Work.SimplyConnected.ABS

theorem globalizedBarrier {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω : Set X} (hΩo : IsOpen Ω) {p : X} (hp : p ∈ frontier Ω)
    (hb : ∃ (u : X → ℝ) (V : Set X), IsOpen V ∧ p ∈ V ∧
      Submission.SuperharmonicOnX u (Ω ∩ V) ∧ (∀ x ∈ Ω ∩ V, 0 < u x) ∧
      ContinuousOn u V ∧ u p = 0) :
    ∃ β : X → ℝ, Submission.SuperharmonicOnX β Ω ∧ (∀ x ∈ Ω, 0 ≤ β x) ∧ β p = 0 ∧
      ContinuousOn β Ω ∧ (∀ x ∈ Ω, x ≠ p → 0 < β x) ∧
      (∀ ε : ℝ, 0 < ε → ∃ V : Set X, V ∈ nhds p ∧ ∀ x ∈ Ω ∩ V, β x < ε) := by sorry

end Work.SimplyConnected.ABS
