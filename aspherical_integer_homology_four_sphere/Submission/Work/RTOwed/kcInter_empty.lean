import Mathlib
import Submission.Work.RTOwed.FillAtlas
import Submission.Work.RTOwed.atlas_empty
import Submission.Work.RTOwed.jTransCollAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The core chart and the collar chart of one cusp have disjoint sources

For each cusp `v` of the assembly `a`, the filling atlas of `a.Mhat` carries two charts
specialised to the `v`-th filling piece:

* the **core** chart `Work.RTOwed.kChartOf a tor v W hW hsec` (flat core coordinates, layer
  parameter `< 1/12`), and
* the **collar** chart `Work.RTOwed.cChart a D v c δ hδ hne` (UHS collar coordinates of the box
  `cBoxR v c δ`, cut at the junction height, layer parameter in `(1/4, 1]`).

Their sources are complementary regions of the layer, hence disjoint.

The argument: a common point `z` of the two sources has two descriptions
`Work.Cusp.cuspCoordMTop a v (D v) c δ q = Work.Cusp.coreCoordM a v (tor v) W q'`.

* If `q` lies *below* the ceiling, `cuspCoordMTop` is the point `a.incMbar ((D v).mbarLow q.1)` of
  the un-glued chimney, while the core point lies in `range (a.incW v)`; the two ranges are
  disjoint (`Work.RTOwed.disjoint_range_incW_incMbar`).
* Otherwise `q` lies at or above the ceiling and both points are `a.incW v`-valued; injectivity of
  `a.incW v` identifies the two points, so their first factors — the layer parameters, which
  satisfy `1/4 < nrm` on the collar side and `nrm < 1/12` on the core side — are equal, which is
  impossible.
-/

namespace Work.RTOwed

theorem kcInter_empty (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (tor : ∀ v : Work.Space.Cusp, a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ)))
    (v : Work.Space.Cusp) (W : Set Work.Cusp.E2) (hW : IsOpen W)
    (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y')
    (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) :
    (Work.RTOwed.kChartOf a tor v W hW hsec).source ∩
      (Work.RTOwed.cChart a D v c δ hδ hne).source = ∅ := by
  rw [Set.inter_comm, cChart_source, kChartOf_source]
  rw [Set.eq_empty_iff_forall_notMem]
  rintro z ⟨hzC, hzK⟩
  rw [Set.mem_image] at hzC hzK
  obtain ⟨q, hqR, hqeq⟩ := hzC
  obtain ⟨q', -, hq'eq⟩ := hzK
  have hval : Work.Cusp.cuspCoordMTop a v (D v) c δ q
      = Work.Cusp.coreCoordM a v (tor v) W q' := by
    rw [hqeq, hq'eq]
  by_cases hlt : q.1 3 < Work.Cusp.beta (Work.Cusp.xOf q.1)
  · -- below the ceiling: the collar point is a point of the un-glued chimney `a.incMbar '' Tsetᶜ`
    have hf : Work.Cusp.cuspCoordMTop a v (D v) c δ q = a.incMbar ((D v).mbarLow q.1) := by
      rw [Work.Cusp.cuspCoordMTop, dite_eq_left hlt]
    rw [hf] at hval
    have h1 : a.incMbar ((D v).mbarLow q.1) ∈ a.incMbar '' a.Tsetᶜ :=
      ⟨_, (D v).mbarLow_not_TsetTop c δ q.2 hlt, rfl⟩
    have h2 : Work.Cusp.coreCoordM a v (tor v) W q' ∈ Set.range (a.incW v) := ⟨_, rfl⟩
    rw [hval] at h1
    exact Set.disjoint_left.mp (disjoint_range_incW_incMbar a v) h2 h1
  · -- at or above the ceiling: both points are `a.incW v`-valued, and `a.incW v` is injective
    have hge : Work.Cusp.beta (Work.Cusp.xOf q.1) ≤ q.1 3 := not_lt.mp hlt
    have hsrc : q.1 ∈ Work.Cusp.cuspSourceTop v c δ := ⟨q.2, hge⟩
    have hC : ∃ p : Work.Space.SquarePt × a.Torus v,
        Work.Cusp.cuspCoordMTop a v (D v) c δ q = a.incW v p ∧
        (p.1 : Work.Cusp.E2) = (Work.Cusp.cuspInvOuter v q.1).1 := by
      refine ⟨(⟨(Work.Cusp.cuspInvOuter v q.1).1,
          Work.Cusp.cuspInvOuter_mem_SqTop v c δ q.1 hsrc⟩,
        (D v).tor.symm (fun i =>
          (((Work.Cusp.cuspInvOuter v q.1).2 i : ℝ) : AddCircle (1 : ℝ)))), ?_, rfl⟩
      rw [Work.Cusp.cuspCoordMTop, dite_eq_right hlt]
    obtain ⟨p, hpeq, hp1⟩ := hC
    have hK : ∃ p' : Work.Space.SquarePt × a.Torus v,
        Work.Cusp.coreCoordM a v (tor v) W q' = a.incW v p' ∧
        (p'.1 : Work.Cusp.E2) = (Work.Cusp.cuspInvCore v q'.1).1 := ⟨_, rfl, rfl⟩
    obtain ⟨p', hp'eq, hp'1⟩ := hK
    have hpp' : p = p' := a.incW_injective v (by rw [← hpeq, hval, hp'eq])
    have hsq : (Work.Cusp.cuspInvOuter v q.1).1 = (Work.Cusp.cuspInvCore v q'.1).1 := by
      rw [← hp1, ← hp'1, hpp']
    -- layer parameters: `(1/4, 1]` on the collar side, `< 1/12` on the core side
    have hgt := (Work.Cusp.cuspInvOuter_nrm_Top v c δ q.1 hsrc).1
    have hcb : q'.1 ∈ Work.Cusp.coreBox := q'.2.1
    have hlt' := Work.Cusp.cuspInvCore_mem_coreStratum v q'.1 hcb
    simp only [Work.Cusp.coreStratum, Set.mem_ofPred_eq] at hlt'
    rw [hsq] at hgt
    rw [Work.Cusp.layerLo] at hgt
    linarith

end Work.RTOwed
