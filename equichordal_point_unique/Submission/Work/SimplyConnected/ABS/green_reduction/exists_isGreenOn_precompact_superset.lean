import Mathlib
import Submission.Work.SimplyConnected.ABS.Defs
import Submission.Work.SimplyConnected.ABS.green_reduction.exists_barrier_regular_precompact_region
import Submission.Work.SimplyConnected.Perron.greenOn

/-!
# A Green function on a precompact region containing a prescribed compact set

Combining the barrier-regular precompact region
`Work.SimplyConnected.ABS.green_reduction.exists_barrier_regular_precompact_region` with the sweep
construction `Work.SimplyConnected.Perron.exists_isGreenOn_of_barriers_final` gives, for every compact
`K` and point `x₀` of a connected second-countable non-compact `ℂ`-charted surface, a precompact
connected open `Ω ⊇ K ∪ {x₀}` carrying a Green function `E` with pole `x₀`
(`Work.SimplyConnected.ABS.IsGreenOn`, the satisfiable "relatively compact superlevel sets"
formulation — see `Defs.lean`).

This is the analytic prerequisite of the ABS argument (arXiv:2008.12189, §6): the Green function of
a relatively compact region is what produces the level circles `γ` and the bands `{|E - ε| < ρ}`
whose crossing by the bridge circle refutes simple connectivity
(`Work.SimplyConnected.ABS.not_simplyConnected_of_band_datum`).
-/

open scoped Topology Manifold ContDiff
open Set Filter

noncomputable section

namespace Work.SimplyConnected.ABS.green_reduction

/-- **A Green function on a precompact region containing `K ∪ {x₀}`.** -/
theorem exists_isGreenOn_precompact_superset {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) {K : Set X} (hK : IsCompact K) (x₀ : X) :
    ∃ Ω : Set X, IsOpen Ω ∧ IsConnected Ω ∧ IsCompact (closure Ω) ∧ K ⊆ Ω ∧ x₀ ∈ Ω ∧
      ∃ E : X → ℝ, Work.SimplyConnected.ABS.IsGreenOn Ω x₀ E := by
  obtain ⟨Ω, hΩo, hΩc, hΩcomp, hKx, hΩne, hbar⟩ :=
    Work.SimplyConnected.ABS.green_reduction.exists_barrier_regular_precompact_region
      (X := X) hX (K := K) hK x₀
  have hx₀Ω : x₀ ∈ Ω := hKx (Set.mem_union_right K (Set.mem_singleton x₀))
  obtain ⟨E, hE⟩ :=
    Work.SimplyConnected.Perron.exists_isGreenOn_of_barriers_final (X := X)
      hΩo hΩc hΩne hΩcomp hx₀Ω hbar
  exact ⟨Ω, hΩo, hΩc, hΩcomp, fun x hx => hKx (Set.mem_union_left _ hx), hx₀Ω, E, hE⟩

end Work.SimplyConnected.ABS.green_reduction
