import Mathlib
import Submission.Work.PlanarSC.BO.Defs
import Submission.Work.PlanarSC.BO.UnitOrder
import Submission.Work.PlanarSC.BO.mem_gEdges_iff
import Submission.Work.PlanarSC.BO.iUnion_SpineSteps_stepSeg

/-!
# From a lattice-step building order to `Work.PlanarSC.HasBuildingOrder`

`Work.PlanarSC.building_order_of_no_jordan`: a nonempty polyomino whose spine is preconnected and
contains no Jordan curve has a building order (`Work.PlanarSC.HasBuildingOrder S`).

The lattice level is `HasStepOrder (SpineSteps S)`, obtained from the preconnectedness and the
absence of Jordan curves by `hasStepOrder_of_no_jordan`
(`Submission/Work/PlanarSC/BO/UnitOrder.lean`); the lattice steps of `SpineSteps S` correspond to
the library edges `Commons.Topology.Plane.gEdges 0 S` under `e ↦ (lpt e.1, lpt e.2)`
(`mem_gEdges_iff`), and the union of their segments is the spine (`iUnion_SpineSteps_stepSeg`).
-/

open Set

namespace Work.HornSC.CellBoundaryJordan.BO

noncomputable section

/-- A building order at the lattice level yields a building order in the vocabulary of
`Work.PlanarSC` (the edges `Commons.Topology.Plane.gEdges 0 S`). -/
theorem hasBuildingOrder_of_hasStepOrder (S : Finset (ℤ × ℤ))
    (h : HasStepOrder (SpineSteps S)) : Work.PlanarSC.HasBuildingOrder S := by
  obtain ⟨N, f, hN, honto, hint⟩ := h
  have hunit : ∀ e ∈ SpineSteps S, IsUnitStep e := fun e he => isUnitStep_of_mem_SpineSteps he
  set F : ℕ → ℂ × ℂ := fun k => (lpt (f k).1, lpt (f k).2) with hF
  refine ⟨N, F, hN, ?_, ?_⟩
  · intro e
    rw [Work.PlanarSC.BO.mem_gEdges_iff S e]
    constructor
    · rintro ⟨e', he', hfe'⟩
      obtain ⟨k, hk, hfk⟩ := (honto e').mp he'
      exact ⟨k, hk, by simp only [hF, hfk, hfe']⟩
    · rintro ⟨k, hk, hfk⟩
      exact ⟨f k, (honto (f k)).mpr ⟨k, hk, rfl⟩, by simpa only [hF] using hfk⟩
  · intro k hk hkN
    have hfk : f k ∈ SpineSteps S := (honto (f k)).mpr ⟨k, hkN, rfl⟩
    have hunitj : ∀ j, j < k → IsUnitStep (f j) := fun j hj =>
      hunit (f j) ((honto (f j)).mpr ⟨j, lt_of_lt_of_le hj hkN.le, rfl⟩)
    obtain ⟨p, hp⟩ := hint k hk hkN
    refine ⟨lpt p, ?_⟩
    simp only [hF]
    have hunion : (⋃ j, ⋃ (_ : j < k), segment ℝ (lpt (f j).1) (lpt (f j).2)) =
        ⋃ j, ⋃ (_ : j < k), stepSeg (f j) := by
      refine Set.iUnion_congr fun j => Set.iUnion_congr fun hj => ?_
      rw [← stepSeg_eq_segment (hunitj j hj)]
    rw [← stepSeg_eq_segment (hunit (f k) hfk), hunion, hp]

/-- **The main theorem of this area.**  A nonempty finite set of lattice cells whose spine is
preconnected and contains no Jordan curve has a building order. -/
theorem building_order_of_no_jordan (S : Finset (ℤ × ℤ)) (hne : S.Nonempty)
    (hconn : IsPreconnected (Work.PlanarSC.spine S))
    (hno : ¬ ∃ γ : C(Circle, ℂ), Function.Injective γ ∧ Set.range γ ⊆ Work.PlanarSC.spine S) :
    Work.PlanarSC.HasBuildingOrder S := by
  have hspine : (⋃ e ∈ SpineSteps S, stepSeg e) = Work.PlanarSC.spine S :=
    Work.PlanarSC.BO.iUnion_SpineSteps_stepSeg S
  have hunit : ∀ e ∈ SpineSteps S, IsUnitStep e := fun e he => isUnitStep_of_mem_SpineSteps he
  have hne' : (SpineSteps S).Nonempty := SpineSteps_nonempty hne
  have hconn' : IsPreconnected (⋃ e ∈ SpineSteps S, stepSeg e) := by
    rw [hspine]; exact hconn
  have hno' : ¬ ∃ γ : C(Circle, ℂ), Function.Injective γ ∧
      Set.range γ ⊆ ⋃ e ∈ SpineSteps S, stepSeg e := by
    rintro ⟨γ, hinj, hrange⟩
    exact hno ⟨γ, hinj, by rw [← hspine]; exact hrange⟩
  exact hasBuildingOrder_of_hasStepOrder S
    (hasStepOrder_of_no_jordan (SpineSteps S) hunit hne' hconn' hno')

end

end Work.HornSC.CellBoundaryJordan.BO
