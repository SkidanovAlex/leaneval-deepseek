import Mathlib
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.MChartAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology

namespace Work.Cusp

/-- The interior of the `v`-th filling piece is open in `SquarePt × T_v`. -/
theorem isOpen_fillInterior (a : Work.Space.Assembly) (v : Work.Space.Cusp) :
    IsOpen (fillInterior a v) := by
  have h : Continuous (fun p : Work.Space.SquarePt × a.Torus v => Work.Space.sqNorm p.1) :=
    Work.Space.continuous_sqNorm.comp continuous_fst
  simpa [fillInterior] using isOpen_lt h continuous_const

theorem isOpenEmbedding_incW_interior (a : Work.Space.Assembly) (v : Work.Space.Cusp) :
    Topology.IsOpenEmbedding (fun p : (fillInterior a v) => a.incW v p.1) := by
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
  · exact (a.continuous_incW v).comp continuous_subtype_val
  · intro p q h
    exact Subtype.ext (a.incW_injective v h)
  · intro U hU
    have hU' : IsOpen ((Subtype.val : (fillInterior a v) → Work.Space.SquarePt × a.Torus v) '' U) :=
      ((isOpen_fillInterior a v).isOpenEmbedding_subtypeVal).isOpen_iff_image_isOpen.mp hU
    -- The image of `U` in the disjoint union `a.Y`
    have hUY : IsOpen ((fun p : (fillInterior a v) => (⟨v, p.1⟩ : a.Y)) '' U) := by
      rw [isOpen_sigma_iff]
      intro w
      by_cases hwv : w = v
      · rw [hwv]
        have hEq : Sigma.mk v ⁻¹' ((fun p : (fillInterior a v) => (⟨v, p.1⟩ : a.Y)) '' U)
            = Subtype.val '' U := by
          ext z
          simp only [mem_preimage, mem_image]
          constructor
          · rintro ⟨p, hpU, hpz⟩
            exact ⟨p, hpU, eq_of_heq (Sigma.mk.inj_iff.mp hpz).2⟩
          · rintro ⟨p, hpU, hpz⟩
            exact ⟨p, hpU, by rw [hpz]⟩
        rw [hEq]
        exact hU'
      · have hEmp : Sigma.mk w ⁻¹' ((fun p : (fillInterior a v) => (⟨v, p.1⟩ : a.Y)) '' U)
            = ∅ := by
          ext z
          simp only [mem_preimage, mem_image, mem_empty_iff_false, iff_false]
          rintro ⟨p, hpU, hpz⟩
          exact hwv (Sigma.mk.inj_iff.mp hpz).1.symm
        rw [hEmp]
        exact isOpen_empty
    rw [a.isOpen_iff_sum]
    refine ⟨?_, ?_⟩
    · -- the trace on `M̄` is empty
      have hleft : {x : a.Mbar |
          a.incMbar x ∈ (fun p : (fillInterior a v) => a.incW v p.1) '' U} = ∅ := by
        ext x
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, mem_image]
        rintro ⟨p, hpU, hpx⟩
        have hne : a.incMbar x ≠ a.incY (⟨v, p.1⟩ : a.Y) := by
          apply a.incMbar_ne_incY
          rintro ⟨hx, hgl⟩
          have hb : Work.Space.sqNorm
              ((a.glue ⟨x, hx⟩ : {q // q ∈ a.boundarySet}) : a.Y).2.1 = 1 :=
            (a.glue ⟨x, hx⟩).2
          rw [hgl] at hb
          have hp : Work.Space.sqNorm p.1.1 < 1 := p.2
          linarith
        exact hne hpx.symm
      rw [hleft]
      exact isOpen_empty
    · -- the trace on the disjoint union is the image of `U`
      have hright : {y : a.Y | a.incY y ∈ (fun p : (fillInterior a v) => a.incW v p.1) '' U}
          = (fun p : (fillInterior a v) => (⟨v, p.1⟩ : a.Y)) '' U := by
        ext y
        simp only [mem_setOf_eq, mem_image]
        constructor
        · rintro ⟨p, hpU, hpy⟩
          exact ⟨p, hpU, a.incY_injective hpy⟩
        · rintro ⟨p, hpU, hpy⟩
          exact ⟨p, hpU, by rw [← hpy]⟩
      rw [hright]
      exact hUY

end Work.Cusp
