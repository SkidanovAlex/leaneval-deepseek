/-
# `T5`: the region of a ray polygon is simply connected

A ray polygon's region `Work.EL.polyRegion ps R` is the bounded side of the Jordan curve
`Work.EL.polyCurve ps R` (`Work.ELTop.polyRegion_eq_bounded_side`).  It is therefore bounded,
open and connected, and its complement is the closure of the *unbounded* side, hence
preconnected.  The uniformization input `Work.EL.PlaneSimplyConnectedInput` — the exact content
of the copied `simplyConnectedSpace_of_isBounded_isConnected_compl` of the uniformization area
— then gives `SimplyConnectedSpace`.
-/
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.polyRegion_eq_bounded_side
import Submission.Work.ELTop.seed_mem_polyRegion

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELTop

/-- **T5 of the ELTop contract.**  The region of a ray polygon is simply connected, given the
uniformization input `PlaneSimplyConnectedInput` (a bounded open connected plane set with
connected complement is simply connected). -/
theorem simplyConnectedSpace_polyRegion {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hSC : Work.EL.PlaneSimplyConnectedInput) (hJ : Work.Top.JordanForm)
    (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps)
    {R : ℝ} (hR : 1 < R) (hC : Work.Top.IsJordanCurve (Work.EL.polyCurve ps R)) :
    SimplyConnectedSpace ↥(Work.EL.polyRegion ps R) := by
  classical
  obtain ⟨S, hS⟩ := polyRegion_eq_bounded_side hN hJ ps hA hR hC
  have hbdd : Bornology.IsBounded (Work.EL.polyRegion ps R) := by
    rw [hS]; exact S.bounded_I
  have hopen : IsOpen (Work.EL.polyRegion ps R) := by
    rw [hS]; exact S.isOpen_I
  have hconn : IsConnected (Work.EL.polyRegion ps R) := by
    refine ⟨⟨_, seed_mem_polyRegion hN ps hA hR⟩, ?_⟩
    rw [hS]; exact S.preconnected_I
  have hcompl : IsPreconnected (Work.EL.polyRegion ps R)ᶜ := by
    have h_eq : (Work.EL.polyRegion ps R)ᶜ = closure S.O := by
      rw [hS]
      ext z
      constructor
      · intro hz
        by_cases hzO : z ∈ S.O
        · exact subset_closure hzO
        · have hzC : z ∈ Work.EL.polyCurve ps R := by
            by_contra hzC
            have hzc : z ∈ (Work.EL.polyCurve ps R)ᶜ := hzC
            rw [← S.union_eq] at hzc
            exact hzc.elim hz hzO
          have hfr : z ∈ frontier S.O := by rw [S.frontier_O]; exact hzC
          exact frontier_subset_closure hfr
      · intro hz
        have hsub : S.O ⊆ (S.I)ᶜ := fun w hw hwI => S.notMem_O_of_mem_I hwI hw
        have hcl : closure S.O ⊆ closure (S.I)ᶜ := closure_mono hsub
        rw [S.isOpen_I.isClosed_compl.closure_eq] at hcl
        exact hcl hz
    rw [h_eq]
    exact S.preconnected_O.closure
  exact hSC _ hbdd hopen hconn hcompl

end Work.ELTop
