import Mathlib
import Submission.Work.SimplyConnected.ABS.RegularPieceDefs
import Submission.Work.SimplyConnected.ABS.ray_boundary_barrier
import Submission.Work.SimplyConnected.ABS.Defs
import Submission.Work.SimplyConnected.Perron.greenOn

namespace Work.SimplyConnected.ABS

/-- The sector-or-ray condition at every frontier point of an open set `Ω` is the Dirichlet
regularity (barrier) hypothesis consumed by
`Work.SimplyConnected.Perron.exists_isGreenOn_of_barriers_final`: a frontier point of an open set
does not lie in it, and the sector and ray conditions each yield a local superharmonic barrier
(`barrier_of_sector`, `barrier_of_ray`). -/
theorem barriers_of_sector_or_ray_of_open {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω : Set X} (hΩo : IsOpen Ω)
    (h : ∀ p ∈ frontier Ω,
      Work.SimplyConnected.ABS.HasSectorBoundary Ω p ∨
      Work.SimplyConnected.ABS.HasRayBoundary Ω p) :
    ∀ p ∈ frontier Ω, ∃ (u : X → ℝ) (V : Set X), IsOpen V ∧ p ∈ V ∧
      Submission.SuperharmonicOnX u (Ω ∩ V) ∧ (∀ x ∈ Ω ∩ V, 0 < u x) ∧
      ContinuousOn u V ∧ u p = 0 := by
  intro p hp
  have hpU : p ∉ Ω := by
    have hf : frontier Ω = closure Ω \ Ω := hΩo.frontier_eq
    rw [hf] at hp
    exact hp.2
  rcases h p hp with hs | hr
  · exact Work.SimplyConnected.ABS.barrier_of_sector hΩo hpU hs
  · exact Work.SimplyConnected.ABS.barrier_of_ray hΩo hpU hr

theorem exists_greenOn_of_sectorBoundary {X : Type*} [TopologicalSpace X]
    [T2Space X] [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) {Ω : Set X} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    (hΩne : Ω ≠ Set.univ) (hcomp : IsCompact (closure Ω)) {x₀ : X} (hx₀ : x₀ ∈ Ω)
    (hsect : ∀ p ∈ frontier Ω,
      Work.SimplyConnected.ABS.HasSectorBoundary Ω p ∨ Work.SimplyConnected.ABS.HasRayBoundary Ω p) :
    ∃ E : X → ℝ, Work.SimplyConnected.ABS.IsGreenOn Ω x₀ E :=
  Work.SimplyConnected.Perron.exists_isGreenOn_of_barriers_final hΩo hΩc hΩne hcomp hx₀
    (barriers_of_sector_or_ray_of_open hΩo hsect)

end Work.SimplyConnected.ABS
