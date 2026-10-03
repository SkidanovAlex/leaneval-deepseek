import Mathlib
import Submission.Work.PlanarSC.PolyDefs
import Submission.Work.PlanarSC.SpineDefs
import Submission.Work.PlanarSC.spine_retract
import Submission.Work.PlanarSC.jordan_in_spine
import Submission.Work.PlanarSC.BO.Transfer
import Submission.Work.PlanarSC.simplyConnectedSpace_inside_jordan_of_polyK

/-!
# A hole-free dyadic polyomino is simply connected

Target: `Work.PlanarSC.polyomino_simplyConnected` — a nonempty finite union of closed dyadic cells
(`dyadicPolyomino n S`) which is preconnected and whose complement is preconnected is a simply
connected space.

The proof goes through the unit scale and the *spine* of the polyomino.

* `Work.PlanarSC.spine S` is the union of the lattice edges of `polyK S`; `polyK S` strongly
  deformation retracts onto it (`Work.PlanarSC.simplyConnectedSpace_polyK_of_spineSet`), so it is
  enough to prove the spine simply connected.
* A Jordan curve inside the spine would force `(polyK S)ᶜ` to be disconnected
  (`Work.PlanarSC.jordan_in_spine`), so the spine is Jordan-free; then it admits a *building order*
  (`Work.PlanarSC.HasBuildingOrder`), i.e. an edge-by-edge construction in which every new edge
  meets the union of its predecessors in a single point.  That is the content of
  `psc_buildingOrder_of_no_jordan` below, obtained by transporting the lattice-level statement
  `Work.HornSC.CellBoundaryJordan.BO.hasStepOrder_of_no_jordan` (the combinatorial peel: a
  connected acyclic finite graph has a leaf) along the identification of the lattice steps
  `SpineSteps S` with the edges `gEdges 0 S` (`psc_iUnion_SpineSteps_stepSeg`).
* A building order makes the spine a retract of `ℂ` (`Work.PlanarSC.spine_retract`), and a retract
  of the contractible space `ℂ` is simply connected
  (`Work.PlanarSC.simplyConnectedSpace_spine_of_retract`).
* Finally the level-`n` statement is obtained from the unit one by scaling the plane by `2⁻ⁿ`
  (`Work.PlanarSC.simplyConnectedSpace_dyadicPolyomino`).
-/

open Set

namespace Work.PlanarSC

noncomputable section

/-! ## The lattice steps of the spine exhaust the spine -/

/-- The union of the closed segments of the lattice steps `SpineSteps S` is the spine of `S`. -/
theorem psc_iUnion_SpineSteps_stepSeg (S : Finset (ℤ × ℤ)) :
    (⋃ e ∈ Work.HornSC.CellBoundaryJordan.BO.SpineSteps S,
        Work.HornSC.CellBoundaryJordan.stepSeg e) = Work.PlanarSC.spine S := by
  ext z
  constructor
  · rintro hz
    obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.mp hz
    have hone : Work.HornSC.CellBoundaryJordan.stepSeg e =
        segment ℝ (Work.HornSC.CellBoundaryJordan.lpt e.1)
          (Work.HornSC.CellBoundaryJordan.lpt e.2) :=
      Work.HornSC.CellBoundaryJordan.BO.stepSeg_eq_segment
        (Work.HornSC.CellBoundaryJordan.BO.isUnitStep_of_mem_SpineSteps he)
    rw [Work.PlanarSC.spine]
    exact Set.mem_iUnion₂.mpr
      ⟨(Work.HornSC.CellBoundaryJordan.lpt e.1, Work.HornSC.CellBoundaryJordan.lpt e.2),
        (Work.PlanarSC.BO.mem_gEdges_iff S _).mpr ⟨e, he, rfl⟩, by rw [← hone]; exact hze⟩
  · rintro hz
    rw [Work.PlanarSC.spine] at hz
    obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.mp hz
    obtain ⟨e', he', hfe'⟩ := (Work.PlanarSC.BO.mem_gEdges_iff S e).mp he
    rw [← hfe'] at hze
    refine Set.mem_iUnion₂.mpr ⟨e', he', ?_⟩
    rw [Work.HornSC.CellBoundaryJordan.BO.stepSeg_eq_segment
      (Work.HornSC.CellBoundaryJordan.BO.isUnitStep_of_mem_SpineSteps he')]
    simpa using hze

/-! ## A Jordan-free connected spine has a building order -/

/-- A nonempty finite set of lattice cells whose spine is preconnected and contains no Jordan
curve has a building order.  (This is `Work.HornSC.CellBoundaryJordan.BO.building_order_of_no_jordan`
with the two hypothesis conversions performed using `psc_iUnion_SpineSteps_stepSeg`.) -/
theorem psc_buildingOrder_of_no_jordan (S : Finset (ℤ × ℤ)) (hne : S.Nonempty)
    (hconn : IsPreconnected (Work.PlanarSC.spine S))
    (hno : ¬ ∃ γ : C(Circle, ℂ), Function.Injective γ ∧
      Set.range γ ⊆ Work.PlanarSC.spine S) :
    Work.PlanarSC.HasBuildingOrder S := by
  have hspine := psc_iUnion_SpineSteps_stepSeg S
  have hunit : ∀ e ∈ Work.HornSC.CellBoundaryJordan.BO.SpineSteps S,
      Work.HornSC.CellBoundaryJordan.IsUnitStep e :=
    fun e he => Work.HornSC.CellBoundaryJordan.BO.isUnitStep_of_mem_SpineSteps he
  have hne' : (Work.HornSC.CellBoundaryJordan.BO.SpineSteps S).Nonempty :=
    Work.HornSC.CellBoundaryJordan.BO.SpineSteps_nonempty hne
  have hconn' : IsPreconnected (⋃ e ∈ Work.HornSC.CellBoundaryJordan.BO.SpineSteps S,
      Work.HornSC.CellBoundaryJordan.stepSeg e) := by
    rw [hspine]; exact hconn
  have hno' : ¬ ∃ γ : C(Circle, ℂ), Function.Injective γ ∧ Set.range γ ⊆
      (⋃ e ∈ Work.HornSC.CellBoundaryJordan.BO.SpineSteps S,
        Work.HornSC.CellBoundaryJordan.stepSeg e) := by
    rintro ⟨γ, hinj, hrange⟩
    exact hno ⟨γ, hinj, by rw [← hspine]; exact hrange⟩
  exact Work.HornSC.CellBoundaryJordan.BO.hasBuildingOrder_of_hasStepOrder S
    (Work.HornSC.CellBoundaryJordan.BO.hasStepOrder_of_no_jordan
      (Work.HornSC.CellBoundaryJordan.BO.SpineSteps S) hunit hne' hconn' hno')

/-! ## The unit-scale case -/

/-- A nonempty hole-free unit polyomino is simply connected. -/
theorem psc_polyK_holefree (S : Finset (ℤ × ℤ)) (hne : S.Nonempty)
    (h1 : IsPreconnected (Commons.Topology.Plane.polyK S))
    (h2 : IsPreconnected (Commons.Topology.Plane.polyK S)ᶜ) :
    SimplyConnectedSpace ↥(Commons.Topology.Plane.polyK S) := by
  -- a Jordan curve in the spine would disconnect the complement
  have hno : ¬ ∃ γ : C(Circle, ℂ), Function.Injective γ ∧
      Set.range γ ⊆ Work.PlanarSC.spine S :=
    fun ⟨γ, hγ, hr⟩ => jordan_in_spine S γ hγ hr h2
  -- hence the spine has a building order
  have hbo : Work.PlanarSC.HasBuildingOrder S :=
    psc_buildingOrder_of_no_jordan S hne (isPreconnected_spine S h1) hno
  -- so the spine is a retract of the plane, hence simply connected
  have hret : Commons.Topology.Plane.IsRetract (Commons.Topology.Plane.spineSet S S) := by
    rw [← Work.PlanarSC.spine_eq_spineSet]
    exact Work.PlanarSC.spine_retract S hbo
  -- and simple connectivity transfers to the polyomino along the deformation retraction
  exact Work.PlanarSC.simplyConnectedSpace_polyK_of_spineSet S
    (Work.PlanarSC.simplyConnectedSpace_spine_of_retract S hret)

/-! ## The target -/

theorem polyomino_simplyConnected {n : ℕ} (S : Finset (ℤ × ℤ))
    (hne : (Work.PlanarSC.dyadicPolyomino n S).Nonempty)
    (hconn : IsPreconnected (Work.PlanarSC.dyadicPolyomino n S))
    (hcompl : IsPreconnected (Work.PlanarSC.dyadicPolyomino n S)ᶜ) :
    SimplyConnectedSpace ↥(Work.PlanarSC.dyadicPolyomino n S) := by
  -- the index set is nonempty as soon as the union of the (nonempty) cells is
  have hSne : S.Nonempty := by
    obtain ⟨z, hz⟩ := hne
    rw [Work.PlanarSC.mem_dyadicPolyomino] at hz
    obtain ⟨p, hp, -⟩ := hz
    exact ⟨p, hp⟩
  exact Work.PlanarSC.simplyConnectedSpace_dyadicPolyomino (n := n) (S := S) hSne hconn hcompl
    (fun T hT h1 h2 => psc_polyK_holefree T hT h1 h2)

end

end Work.PlanarSC
