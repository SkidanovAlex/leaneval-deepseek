import Mathlib
import Submission.Work.SimplyConnected.ABS.Defs

namespace Work.SimplyConnected.ABS

theorem exists_isGreenOn {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) {Ω : Set X} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    (hΩs : IsSimplyConnected Ω) (hΩne : Ω ≠ Set.univ) (hcomp : IsCompact (closure Ω))
    {x₀ : X} (hx₀ : x₀ ∈ Ω) :
    ∃ E : X → ℝ, Work.SimplyConnected.ABS.IsGreenOn Ω x₀ E := by sorry

end Work.SimplyConnected.ABS
