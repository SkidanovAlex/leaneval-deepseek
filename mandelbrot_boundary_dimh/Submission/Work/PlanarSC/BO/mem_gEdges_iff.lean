import Mathlib
import Submission.Work.PlanarSC.BO.Defs

namespace Work.PlanarSC.BO

/-- `lpt` is `gcorner` at scale `0`: both send `(a,b)` to `⟨(a:ℝ),(b:ℝ)⟩`. -/
lemma lpt_eq_gcorner_zero (v : ℤ × ℤ) :
    Work.HornSC.CellBoundaryJordan.lpt v = Commons.Topology.Plane.gcorner 0 v.1 v.2 := by
  apply Complex.ext <;>
    simp [Work.HornSC.CellBoundaryJordan.lpt, Commons.Topology.Plane.gcorner]

/-- Put this in `Submission/Work/PlanarSC/BO/mem_gEdges_iff.lean`, with imports `Mathlib` and
`Submission.Work.PlanarSC.BO.Defs`, inside `namespace Work.HornSC.CellBoundaryJordan.BO`.

The lattice steps of `SpineSteps S` map onto the library edge family
`Commons.Topology.Plane.gEdges 0 S` under `e ↦ (lpt e.1, lpt e.2)`.
`lpt (a,b) = ⟨(a:ℝ),(b:ℝ)⟩` and `Commons.Topology.Plane.gcorner 0 a b = ⟨(a:ℝ)/2^0,(b:ℝ)/2^0⟩`
coincide (`2^0 = 1`), so this is an unfolding: `mem_gVEdges`, `mem_gHEdges` (in
`Submission/Lib/Unif2/Commons/Topology/Plane/exists_homotopyEquiv_subgraph_oneDimCW_of_dyadic_subcomplex.lean`)
and `mem_SpineSteps` describe the two sides, and `lpt_injective` handles endpoint equalities. -/
theorem mem_gEdges_iff (S : Finset (ℤ × ℤ)) (e : ℂ × ℂ) :
    e ∈ Commons.Topology.Plane.gEdges 0 S ↔
      ∃ e' ∈ Work.HornSC.CellBoundaryJordan.BO.SpineSteps S,
        (Work.HornSC.CellBoundaryJordan.lpt e'.1, Work.HornSC.CellBoundaryJordan.lpt e'.2) = e := by
  constructor
  · intro he
    rw [Commons.Topology.Plane.gEdges, Finset.mem_union] at he
    rcases he with hv | hh
    · rcases Commons.Topology.Plane.mem_gVEdges.mp hv with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
      · exact ⟨((p.1, p.2), (p.1, p.2 + 1)),
          Work.HornSC.CellBoundaryJordan.BO.mem_SpineSteps.mpr (Or.inl ⟨p, hp, rfl⟩),
          by simp [lpt_eq_gcorner_zero]⟩
      · exact ⟨((p.1 + 1, p.2), (p.1 + 1, p.2 + 1)),
          Work.HornSC.CellBoundaryJordan.BO.mem_SpineSteps.mpr (Or.inr (Or.inl ⟨p, hp, rfl⟩)),
          by simp [lpt_eq_gcorner_zero]⟩
    · rcases Commons.Topology.Plane.mem_gHEdges.mp hh with ⟨p, hp, hp', rfl⟩
      exact ⟨((p.1, p.2), (p.1 + 1, p.2)),
        Work.HornSC.CellBoundaryJordan.BO.mem_SpineSteps.mpr (Or.inr (Or.inr ⟨p, hp, hp', rfl⟩)),
        by simp [lpt_eq_gcorner_zero]⟩
  · rintro ⟨e', he', rfl⟩
    rcases Work.HornSC.CellBoundaryJordan.BO.mem_SpineSteps.mp he' with
      ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, hp', rfl⟩
    · rw [Commons.Topology.Plane.gEdges]
      exact Finset.mem_union_left _
        (Commons.Topology.Plane.mem_gVEdges.mpr (Or.inl ⟨p, hp, by simp [lpt_eq_gcorner_zero]⟩))
    · rw [Commons.Topology.Plane.gEdges]
      exact Finset.mem_union_left _
        (Commons.Topology.Plane.mem_gVEdges.mpr (Or.inr ⟨p, hp, by simp [lpt_eq_gcorner_zero]⟩))
    · rw [Commons.Topology.Plane.gEdges]
      exact Finset.mem_union_right _
        (Commons.Topology.Plane.mem_gHEdges.mpr ⟨p, hp, hp', by simp [lpt_eq_gcorner_zero]⟩)

end Work.PlanarSC.BO
