/-
# The collar coordinate `cuspCoordM` of `M̂` is an open embedding

`cuspCoordM a v D c δ` (`Work.Cusp.Assembly`) sends a point of the *open* chart box
`B = cuspChartBox v c δ` to the assembled space `M̂`: below the ceiling `s = β x` to the point of the
chimney of the hyperbolic piece with cusp coordinates `q` (the branch `incMbar ∘ mbarLow`), at or
above it to the point of the `v`-th filling piece recovered by the outer chart (the branch
`incW ∘ cuspInvOuter`).

This file proves that it is an **open embedding**.  Continuity and injectivity are
`cuspCoordM_continuous` and `cuspCoordM_injective` (the latter uses `δ ≤ 1/2`), so by
`Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap` it remains to see that `cuspCoordM` is
an open map, i.e. (for every open `U ⊆ B`) that `cuspCoordM '' U` is open in `M̂`.  By the
openness criterion of the adjunction, `Assembly.isOpen_iff_sum`, this is a statement about the two
traces of `cuspCoordM '' U` on the pieces `M̄` and `Y = ⊔_v [-1,1]² × T_v`.

* **Trace on `M̄`.**  The points of `M̄` whose `incMbar`-image lies in `cuspCoordM '' U` come from
  the lower branch: if `q` is *strictly* above the ceiling then its image `incW v p` meets
  `range incMbar` only along the glued boundary `‖p‖∞ = 1`, which would force the recovered layer
  parameter to be `1`, hence (by `cuspInvOuter_nrm_eq_one_ceiling`) `q` to lie *on* the ceiling
  after all.  So the trace is `mbarLow '' (U ∩ {q 3 ≤ β (xOf q)})`, open in `M̄` because `mbarLow`
  is an open embedding on the below-ceiling region (`CuspGlueData.mbarLow_isEmbedding`).

* **Trace on `Y`.**  It is concentrated on the `v`-th filling piece, where it is the image under
  the upper branch `cuspCoordUp` of `U ∩ cuspCollarSource v c δ`; the upper branch is the composite
  `(layerPtSq × (tor ∘ π)) ∘ cuspCollarF` of three open maps: the open embedding `cuspCollarF`
  (the `(u,t,y)`-coordinates of the collar source, `isOpenEmbedding_cuspCollarF`), the
  layer-direction chart `layerPtSq` of the square (`isOpenEmbedding_layerPtSq`) and the projection
  of the cover of the filling piece (`fillProj_torus_isOpenMap`).
-/
import Mathlib
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.CuspChartAux
import Submission.Work.Cusp.cuspCoordM_continuous
import Submission.Work.Cusp.cuspCoordM_injective
import Submission.Work.Cusp.isOpenMap_fillProj
import Submission.Work.Cusp.isOpenEmbedding_layerPtSq
import Submission.Work.Cusp.isOpenEmbedding_cuspCollarF
import Submission.Work.Space.Assembly

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function

namespace Work.Cusp

/-! ### The upper branch of the collar coordinate -/

/-- **The collar coordinate on the collar source is the upper branch of the chart.**  For a point of
the collar source (on or above the ceiling, with perimeter coordinate in `(0,1)`) the value of
`cuspCoordM` is the point of the `v`-th filling piece described by `cuspCoordUp`. -/
theorem cuspCoordM_eq_up (a : Work.Space.Assembly) (v : Work.Space.Cusp) (D : CuspGlueData a v)
    (c : E3) (δ : ℝ) (q : {q : E4 // q ∈ cuspCollarSource v c δ}) :
    cuspCoordM a v D c δ ⟨q.1, cuspCollarSource_subset_chartBox v c δ q.2⟩
      = a.incW v (cuspCoordUp a v D c δ q) := by
  have hβ : beta (xOf q.1) ≤ q.1 3 := q.2.1.2
  rw [cuspCoordM_eq_ge a v D c δ ⟨q.1, cuspCollarSource_subset_chartBox v c δ q.2⟩ hβ,
    cuspCoordUp_eq]
  simp only [cuspCoordMUp]

/-- **The upper branch `cuspCoordUp` is an open map.**  It is the composite of the `(u,t,y)`-chart
`cuspCollarF`, the layer-direction chart `layerPtSq` of the square and the projection
`y ↦ tor.symm (y mod ℤ²)` of the cover of the filling piece, all three of which are open. -/
theorem isOpenMap_cuspCoordUp (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) :
    IsOpenMap (cuspCoordUp a v D c δ) := by
  rw [cuspCoordUp_eq_comp]
  exact ((isOpenEmbedding_layerPtSq.isOpenMap.prodMap
    (fillProj_torus_isOpenMap a v D.tor)).comp (isOpenEmbedding_cuspCollarF v c δ).isOpenMap)

/-! ### The collar coordinate is an open map -/

/-- **The collar coordinate is an open map.**  For an open `U` of the chart box, the two traces of
`cuspCoordM '' U` on the pieces of `M̂` are open: the trace on `M̄` is
`mbarLow '' (U ∩ {q 3 ≤ β x})`, open because `mbarLow` is an open embedding on the below-ceiling
region, and the trace on `Y` is the image of `U ∩ cuspCollarSource v c δ` under the open map
`cuspCoordUp`, sitting in the `v`-th filling piece. -/
theorem isOpenMap_cuspCoordM_of (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2) :
    IsOpenMap (cuspCoordM a v D c δ) := by
  intro U hU
  obtain ⟨U', hU'open, hU'eq⟩ := isOpen_induced_iff.mp hU
  -- a point of the chart box lies in `U` exactly when its underlying point of `E4` lies in `U'`
  have memU : ∀ q : {q : E4 // q ∈ cuspChartBox v c δ}, q ∈ U ↔ (q.1 : E4) ∈ U' := by
    intro q
    rw [← hU'eq]
    rfl
  rw [a.isOpen_iff_sum]
  refine ⟨?_, ?_⟩
  · -- the trace on `M̄`
    have hUA : IsOpen (subOfSet
        (p := fun q : E4 => q ∈ cuspChartBox v c δ ∧ q 3 ≤ beta (xOf q)) U') := by
      exact hU'open.preimage continuous_subtype_val
    have hset : {x : a.Mbar | a.incMbar x ∈ cuspCoordM a v D c δ '' U}
        = (fun z : {q : E4 // q ∈ cuspChartBox v c δ ∧ q 3 ≤ beta (xOf q)} => D.mbarLow z) ''
            subOfSet (p := fun q : E4 => q ∈ cuspChartBox v c δ ∧ q 3 ≤ beta (xOf q)) U' := by
      ext x
      constructor
      · rintro ⟨q, hqU, hqx⟩
        have hqU' : (q.1 : E4) ∈ U' := (memU q).mp hqU
        by_cases hle : q.1 3 ≤ beta (xOf q.1)
        · -- the lower branch: `incMbar` is injective
          have hinc : a.incMbar (D.mbarLow q.1) = a.incMbar x := by
            rw [← cuspCoordM_eq_le a v D c δ q hle]
            exact hqx
          exact ⟨⟨q.1, ⟨q.2, hle⟩⟩, hqU', by simpa using a.incMbar_injective hinc⟩
        · -- the upper branch can only meet `range incMbar` along the glued boundary
          exfalso
          have hgt : beta (xOf q.1) < q.1 3 := not_le.mp hle
          set qC : {q : E4 // q ∈ cuspCollarSource v c δ} :=
            ⟨q.1, ⟨⟨cuspChartBox_subset_cuspBox v c δ q.2, le_of_lt hgt⟩, q.2.2.2.2.1⟩⟩ with hqC
          have hB : (⟨qC.1, cuspCollarSource_subset_chartBox v c δ qC.2⟩ :
              {q : E4 // q ∈ cuspChartBox v c δ}) = q := Subtype.ext rfl
          have hmix : a.incMbar x = a.incW v (cuspCoordUp a v D c δ qC) := by
            rw [← hqx, ← hB, cuspCoordM_eq_up a v D c δ qC]
          obtain ⟨hxT, hglue⟩ := incMbar_eq_incW_imp a v hmix
          have hbdry := (a.glue ⟨x, hxT⟩).2
          rw [hglue] at hbdry
          have hnrm1 : nrm (cuspInvOuter v qC.1).1 = 1 := by
            have hb : Work.Space.sqNorm ((cuspCoordUp a v D c δ qC).1 : Work.Space.SquarePt) = 1 :=
              hbdry
            rw [cuspCoordUp_eq] at hb
            simpa only [Work.Space.sqNorm, Work.Space.nrm, nrm] using hb
          exact (ne_of_lt hgt)
            (cuspInvOuter_nrm_eq_one_ceiling v c δ qC.1
              (cuspChartBox_subset_cuspBox v c δ q.2) hnrm1).symm
      · -- conversely, a point of the below-ceiling region is the image of its cusp coordinate
        rintro ⟨z, hzU', hzx⟩
        have hzle : z.1 3 ≤ beta (xOf z.1) := z.2.2
        refine ⟨⟨z.1, z.2.1⟩, (memU _).mpr hzU', ?_⟩
        rw [cuspCoordM_eq_le a v D c δ ⟨z.1, z.2.1⟩ hzle]
        simpa using congrArg a.incMbar hzx
    rw [hset]
    exact (D.mbarLow_isEmbedding c δ hδ).isOpenMap
      (subOfSet (p := fun q : E4 => q ∈ cuspChartBox v c δ ∧ q 3 ≤ beta (xOf q)) U') hUA
  · -- the trace on the filling pieces
    have hUC : IsOpen (subOfSet (p := fun q : E4 => q ∈ cuspCollarSource v c δ) U') := by
      exact hU'open.preimage continuous_subtype_val
    have hImg : IsOpen (cuspCoordUp a v D c δ ''
        subOfSet (p := fun q : E4 => q ∈ cuspCollarSource v c δ) U') :=
      isOpenMap_cuspCoordUp a v D c δ _ hUC
    have hset2 : {y : a.Y | a.incY y ∈ cuspCoordM a v D c δ '' U}
        = (fun p : Work.Space.SquarePt × a.Torus v => (⟨v, p⟩ : a.Y)) ''
            (cuspCoordUp a v D c δ ''
              subOfSet (p := fun q : E4 => q ∈ cuspCollarSource v c δ) U') := by
      ext y
      constructor
      · rintro ⟨q, hqU, hqy⟩
        have hqU' : (q.1 : E4) ∈ U' := (memU q).mp hqU
        by_cases hlt : q.1 3 < beta (xOf q.1)
        · -- the lower branch meets `range incY` only along the glued boundary
          exfalso
          have hval : cuspCoordM a v D c δ q = a.incMbar (D.mbarLow q.1) :=
            cuspCoordM_eq_le a v D c δ q (le_of_lt hlt)
          have hT : D.mbarLow q.1 ∉ a.Tset := D.mbarLow_not_Tset c δ q.2 hlt
          exact a.incMbar_ne_incY (fun h => hT h.1) (by rw [← hval]; exact hqy)
        · -- the upper branch: `incY` is injective
          have hge : beta (xOf q.1) ≤ q.1 3 := not_lt.mp hlt
          set qC : {q : E4 // q ∈ cuspCollarSource v c δ} :=
            ⟨q.1, ⟨⟨cuspChartBox_subset_cuspBox v c δ q.2, hge⟩, q.2.2.2.2.1⟩⟩ with hqC
          have hB : (⟨qC.1, cuspCollarSource_subset_chartBox v c δ qC.2⟩ :
              {q : E4 // q ∈ cuspChartBox v c δ}) = q := Subtype.ext rfl
          have hval : cuspCoordM a v D c δ q = a.incW v (cuspCoordUp a v D c δ qC) := by
            rw [← hB, cuspCoordM_eq_up a v D c δ qC]
          refine ⟨cuspCoordUp a v D c δ qC, ⟨qC, hqU', rfl⟩, ?_⟩
          refine a.incY_injective ?_
          rw [← hqy, hval]
      · rintro ⟨p, ⟨qC, hqU', hqp⟩, hyp⟩
        refine ⟨⟨qC.1, cuspCollarSource_subset_chartBox v c δ qC.2⟩, (memU _).mpr hqU', ?_⟩
        rw [cuspCoordM_eq_up a v D c δ qC, hqp]
        simpa using congrArg a.incY hyp
    rw [hset2]
    exact isOpenMap_sigmaMk (i := v) _ hImg

/-- **The collar coordinate is an open embedding of the chart box into `M̂`.** -/
theorem isOpenEmbedding_cuspCoordM (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2) :
    Topology.IsOpenEmbedding (cuspCoordM a v D c δ) :=
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (cuspCoordM_continuous a v D c δ) (cuspCoordM_injective a v D c δ hδ)
    (isOpenMap_cuspCoordM_of a v D c δ hδ)

end Work.Cusp
