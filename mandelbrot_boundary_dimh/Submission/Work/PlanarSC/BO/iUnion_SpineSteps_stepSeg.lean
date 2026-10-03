import Mathlib
import Submission.Work.PlanarSC.BO.Defs

/-!
# The spine is the union of the closed segments of its lattice steps

`Work.PlanarSC.spine S = ⋃ e ∈ Commons.Topology.Plane.gEdges 0 S, segment ℝ e.1 e.2` is written in
the dyadic-scale vocabulary of the library (`gEdges`, `gcorner`), while the combinatorial theory of
`Submission/Work/PlanarSC/BO/Defs.lean` works with integer lattice steps (`SpineSteps`, `stepSeg`,
`lpt`).  At scale `0` the two dictionaries coincide: `gcorner 0 a b = lpt (a,b)` and the map
`e ↦ (lpt e.1, lpt e.2)` matches `SpineSteps S` with `gEdges 0 S`.  This module records that
dictionary and deduces the identification of the two descriptions of the spine.
-/

open Set

namespace Work.PlanarSC.BO

/-- At scale `0` the library's grid corner `gcorner` is the lattice point map `lpt`. -/
theorem gcorner_zero_eq_lpt (a b : ℤ) :
    Commons.Topology.Plane.gcorner 0 a b = Work.HornSC.CellBoundaryJordan.lpt (a, b) := by
  apply Complex.ext <;> simp [Commons.Topology.Plane.gcorner, Work.HornSC.CellBoundaryJordan.lpt]

/-- The endpoints `(lpt e.1, lpt e.2)` of a spine step form an edge of the library's edge family
`gEdges 0 S`. -/
theorem lpt_pair_mem_gEdges {S : Finset (ℤ × ℤ)} {e : (ℤ × ℤ) × (ℤ × ℤ)}
    (he : e ∈ Work.HornSC.CellBoundaryJordan.BO.SpineSteps S) :
    (Work.HornSC.CellBoundaryJordan.lpt e.1, Work.HornSC.CellBoundaryJordan.lpt e.2) ∈
      Commons.Topology.Plane.gEdges 0 S := by
  rcases Work.HornSC.CellBoundaryJordan.BO.mem_SpineSteps.mp he with
    ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, hp', rfl⟩
  · exact Finset.mem_union_left _
      (Commons.Topology.Plane.mem_gVEdges.mpr (Or.inl ⟨p, hp, by simp [gcorner_zero_eq_lpt]⟩))
  · exact Finset.mem_union_left _
      (Commons.Topology.Plane.mem_gVEdges.mpr (Or.inr ⟨p, hp, by simp [gcorner_zero_eq_lpt]⟩))
  · exact Finset.mem_union_right _
      (Commons.Topology.Plane.mem_gHEdges.mpr ⟨p, hp, hp', by simp [gcorner_zero_eq_lpt]⟩)

/-- Conversely, every edge of `gEdges 0 S` is the endpoint pair of a spine step. -/
theorem exists_mem_SpineSteps_of_mem_gEdges {S : Finset (ℤ × ℤ)} {e' : ℂ × ℂ}
    (he' : e' ∈ Commons.Topology.Plane.gEdges 0 S) :
    ∃ e ∈ Work.HornSC.CellBoundaryJordan.BO.SpineSteps S,
      (Work.HornSC.CellBoundaryJordan.lpt e.1, Work.HornSC.CellBoundaryJordan.lpt e.2) = e' := by
  rcases Finset.mem_union.mp he' with hv | hh
  · rcases Commons.Topology.Plane.mem_gVEdges.mp hv with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · exact ⟨((p.1, p.2), (p.1, p.2 + 1)),
        Work.HornSC.CellBoundaryJordan.BO.mem_SpineSteps.mpr (Or.inl ⟨p, hp, rfl⟩),
        by simp [gcorner_zero_eq_lpt]⟩
    · exact ⟨((p.1 + 1, p.2), (p.1 + 1, p.2 + 1)),
        Work.HornSC.CellBoundaryJordan.BO.mem_SpineSteps.mpr (Or.inr (Or.inl ⟨p, hp, rfl⟩)),
        by simp [gcorner_zero_eq_lpt]⟩
  · rcases Commons.Topology.Plane.mem_gHEdges.mp hh with ⟨p, hp, hp', rfl⟩
    exact ⟨((p.1, p.2), (p.1 + 1, p.2)),
      Work.HornSC.CellBoundaryJordan.BO.mem_SpineSteps.mpr (Or.inr (Or.inr ⟨p, hp, hp', rfl⟩)),
      by simp [gcorner_zero_eq_lpt]⟩

/-- The union of the closed segments of the lattice steps `SpineSteps S` is exactly the spine
`Work.PlanarSC.spine S = ⋃ e ∈ Commons.Topology.Plane.gEdges 0 S, segment ℝ e.1 e.2`. -/
theorem iUnion_SpineSteps_stepSeg (S : Finset (ℤ × ℤ)) :
    (⋃ e ∈ Work.HornSC.CellBoundaryJordan.BO.SpineSteps S,
        Work.HornSC.CellBoundaryJordan.stepSeg e) = Work.PlanarSC.spine S := by
  ext z
  simp only [Work.PlanarSC.spine, Set.mem_iUnion]
  constructor
  · rintro ⟨e, he, hz⟩
    refine ⟨(Work.HornSC.CellBoundaryJordan.lpt e.1, Work.HornSC.CellBoundaryJordan.lpt e.2),
      lpt_pair_mem_gEdges he, ?_⟩
    rw [Work.HornSC.CellBoundaryJordan.BO.stepSeg_eq_segment
      (Work.HornSC.CellBoundaryJordan.BO.isUnitStep_of_mem_SpineSteps he)] at hz
    simpa using hz
  · rintro ⟨e', he', hz⟩
    obtain ⟨e, he, hee⟩ := exists_mem_SpineSteps_of_mem_gEdges he'
    refine ⟨e, he, ?_⟩
    rw [Work.HornSC.CellBoundaryJordan.BO.stepSeg_eq_segment
      (Work.HornSC.CellBoundaryJordan.BO.isUnitStep_of_mem_SpineSteps he)]
    have hz' : z ∈ segment ℝ (Work.HornSC.CellBoundaryJordan.lpt e.1)
        (Work.HornSC.CellBoundaryJordan.lpt e.2) := by
      rw [show e' = (Work.HornSC.CellBoundaryJordan.lpt e.1,
        Work.HornSC.CellBoundaryJordan.lpt e.2) from hee.symm] at hz
      simpa using hz
    exact hz'

end Work.PlanarSC.BO
