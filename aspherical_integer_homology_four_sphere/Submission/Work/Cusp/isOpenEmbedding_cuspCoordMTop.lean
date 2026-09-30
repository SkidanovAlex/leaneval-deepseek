/-
# The *unslabbed* collar coordinate `cuspCoordMTop` of `M̂` is an open embedding

`cuspCoordMTop a v D c δ` sends a point of the *unslabbed* collar box `cuspBoxTop v c δ` (side `2δ`
in the cusp coordinate `x`, heights in `(s₁, sTop)`, and **no** slab condition on the meridian
coordinate `outerU v x`) to the assembled space `M̂`: below the ceiling `s = β x` to the point of the
chimney of the hyperbolic piece with cusp coordinates `q` (the branch `incMbar ∘ mbarLow`), at or
above it to the point of the `v`-th filling piece recovered by the outer chart (the branch
`incW ∘ cuspInvOuter`).

This file proves that it is an **open embedding**.  Continuity and injectivity are
`cuspCoordMTop_continuous` and `cuspCoordMTop_injective` (the latter uses `δ ≤ 1/2`), so by
`Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap` it remains to see that `cuspCoordMTop`
is an *open map*, i.e. (for every open `U ⊆ cuspBoxTop v c δ`) that `cuspCoordMTop '' U` is open in
`M̂`.  By the openness criterion of the adjunction, `Assembly.isOpen_iff_sum`, this is a statement
about the two traces of `cuspCoordMTop '' U` on the pieces `M̄` and `Y = ⊔_v [-1,1]² × T_v`; the
argument is the same as for the slabbed family (`isOpenEmbedding_cuspCoordM`).

* **Trace on `M̄`.**  The points of `M̄` whose `incMbar`-image lies in `cuspCoordMTop '' U` come from
  the lower branch: if `q` is *strictly* above the ceiling then its image `incW v p` meets
  `range incMbar` only along the glued boundary `‖p‖∞ = 1`, which would force the recovered layer
  parameter to be `1`, hence (by `cuspInvOuter_nrm_eq_one_ceilingTop`) `q` to lie *on* the ceiling
  after all.  So the trace is `mbarLow '' (U ∩ {q 3 ≤ β (xOf q)})`, open in `M̄` because `mbarLow` is
  an open embedding on the below-ceiling region of the unslabbed box
  (`CuspGlueData.mbarLow_isEmbeddingTop`).

* **Trace on `Y`.**  It is concentrated on the `v`-th filling piece, where it is the image under the
  upper branch `cuspTopUp` of `U ∩ cuspSourceTop v c δ`; the upper branch is the composite
  `(layerPtI (cuspAnchor v c) × (tor ∘ mod)) ∘ cuspTopF` of three open maps
  (`isOpenMap_cuspTopUp`).

The point of the unslabbed family is that it reaches the *corner* directions of the filling square,
which the slabbed box `cuspChartBox` cannot (`LayerTop` / `TopBox`).
-/
import Mathlib
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.TopBox
import Submission.Work.Cusp.isOpenEmbedding_cuspTopF
import Submission.Work.Cusp.isOpenMap_cuspTopUp
import Submission.Work.Cusp.cuspCoordMTop_continuous
import Submission.Work.Cusp.cuspCoordMTop_injective
import Submission.Work.Cusp.CuspChartAux
import Submission.Work.Cusp.cuspCoordM_continuous
import Submission.Work.Cusp.cuspCoordM_injective
import Submission.Work.Cusp.isOpenMap_fillProj
import Submission.Work.Cusp.isOpenEmbedding_layerPtSq
import Submission.Work.Cusp.CuspCollarAux
import Submission.Work.Cusp.continuous_cuspCollarInv
import Submission.Work.Cusp.collarHeight_half
import Submission.Work.Space.Assembly
import Submission.Work.Cusp.cuspTopUp_eq
import Submission.Work.Cusp.cuspInvOuter_nrm_eq_one_ceilingTop

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function

namespace Work.Cusp

/-- **The upper branch of the unslabbed collar coordinate is `incW` applied to `cuspTopUp`.**  For a
point of the collar source (on or above the ceiling, heights in `(s₁, sTop)`) the value of
`cuspCoordMTop` is the point of the `v`-th filling piece described by `cuspTopUp` — the layer point
`layerPtI (cuspAnchor v c)` of its own `(u,t)`-coordinates and the `mod ℤ²`-reduction of its phase
`outerY v (xOf q)`. -/
theorem cuspCoordMTop_eq_up (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (q : {q : E4 // q ∈ cuspSourceTop v c δ}) :
    cuspCoordMTop a v D c δ ⟨q.1, q.2.1⟩ = a.incW v (cuspTopUp a v D c δ hδ q) := by
  rw [cuspCoordMTop_eq_ge a v D c δ ⟨q.1, q.2.1⟩ q.2.2, cuspTopUp_eq a v D c δ hδ q]
  rfl

/-- **The unslabbed collar coordinate is an open map.**  For an open `U` of the collar box, the two
traces of `cuspCoordMTop '' U` on the pieces of `M̂` are open: the trace on `M̄` is
`mbarLow '' (U ∩ {q 3 ≤ β x})`, open because `mbarLow` is an open embedding on the below-ceiling
region of the unslabbed box, and the trace on `Y` is the image of `U ∩ cuspSourceTop v c δ` under
the open map `cuspTopUp`, sitting in the `v`-th filling piece. -/
theorem isOpenMap_cuspCoordMTop_of (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2) :
    IsOpenMap (cuspCoordMTop a v D c δ) := by
  intro U hU
  obtain ⟨U', hU'open, hU'eq⟩ := isOpen_induced_iff.mp hU
  -- a point of the collar box lies in `U` exactly when its underlying point of `E4` lies in `U'`
  have memU : ∀ q : {q : E4 // q ∈ cuspBoxTop v c δ}, q ∈ U ↔ (q.1 : E4) ∈ U' := by
    intro q
    rw [← hU'eq]
    rfl
  rw [a.isOpen_iff_sum]
  refine ⟨?_, ?_⟩
  · -- the trace on `M̄`
    have hUA : IsOpen (subOfSet
        (p := fun q : E4 => q ∈ cuspBoxTop v c δ ∧ q 3 ≤ beta (xOf q)) U') :=
      hU'open.preimage continuous_subtype_val
    have hset : {x : a.Mbar | a.incMbar x ∈ cuspCoordMTop a v D c δ '' U}
        = (fun z : {q : E4 // q ∈ cuspBoxTop v c δ ∧ q 3 ≤ beta (xOf q)} => D.mbarLow z) ''
            subOfSet (p := fun q : E4 => q ∈ cuspBoxTop v c δ ∧ q 3 ≤ beta (xOf q)) U' := by
      ext x
      constructor
      · rintro ⟨q, hqU, hqx⟩
        have hqU' : (q.1 : E4) ∈ U' := (memU q).mp hqU
        by_cases hle : q.1 3 ≤ beta (xOf q.1)
        · -- the lower branch: `incMbar` is injective
          have hinc : a.incMbar (D.mbarLow q.1) = a.incMbar x := by
            rw [← cuspCoordMTop_eq_le a v D c δ q hle]
            exact hqx
          exact ⟨⟨q.1, ⟨q.2, hle⟩⟩, hqU', by simpa using a.incMbar_injective hinc⟩
        · -- the upper branch can only meet `range incMbar` along the glued boundary
          exfalso
          have hgt : beta (xOf q.1) < q.1 3 := not_le.mp hle
          have hsrc : q.1 ∈ cuspSourceTop v c δ := ⟨q.2, le_of_lt hgt⟩
          have hmix : a.incMbar x = a.incW v (cuspTopUp a v D c δ hδ ⟨q.1, hsrc⟩) :=
            hqx.symm.trans (cuspCoordMTop_eq_up a v D c δ hδ ⟨q.1, hsrc⟩)
          obtain ⟨hxT, hglue⟩ := incMbar_eq_incW_imp a v hmix
          have hbdry := (a.glue ⟨x, hxT⟩).2
          rw [hglue] at hbdry
          have hnrm1 : nrm (cuspInvOuter v q.1).1 = 1 := by
            have hb : Work.Space.sqNorm
                ((cuspTopUp a v D c δ hδ ⟨q.1, hsrc⟩).1 : Work.Space.SquarePt) = 1 := hbdry
            rw [cuspTopUp_eq a v D c δ hδ ⟨q.1, hsrc⟩] at hb
            simpa only [Work.Space.sqNorm, Work.Space.nrm, nrm] using hb
          exact (ne_of_lt hgt)
            (cuspInvOuter_nrm_eq_one_ceilingTop v c δ q.1 hsrc hnrm1).symm
      · -- conversely, a point of the below-ceiling region is the image of its cusp coordinate
        rintro ⟨z, hzU', hzx⟩
        have hzle : z.1 3 ≤ beta (xOf z.1) := z.2.2
        refine ⟨⟨z.1, z.2.1⟩, (memU _).mpr hzU', ?_⟩
        rw [cuspCoordMTop_eq_le a v D c δ ⟨z.1, z.2.1⟩ hzle]
        simpa using congrArg a.incMbar hzx
    rw [hset]
    exact (D.mbarLow_isEmbeddingTop c δ hδ).isOpenMap
      (subOfSet (p := fun q : E4 => q ∈ cuspBoxTop v c δ ∧ q 3 ≤ beta (xOf q)) U') hUA
  · -- the trace on the filling pieces
    have hUC : IsOpen (subOfSet (p := fun q : E4 => q ∈ cuspSourceTop v c δ) U') :=
      hU'open.preimage continuous_subtype_val
    have hImg : IsOpen (cuspTopUp a v D c δ hδ ''
        subOfSet (p := fun q : E4 => q ∈ cuspSourceTop v c δ) U') :=
      isOpenMap_cuspTopUp a v D c δ hδ _ hUC
    have hset2 : {y : a.Y | a.incY y ∈ cuspCoordMTop a v D c δ '' U}
        = (fun p : Work.Space.SquarePt × a.Torus v => (⟨v, p⟩ : a.Y)) ''
            (cuspTopUp a v D c δ hδ ''
              subOfSet (p := fun q : E4 => q ∈ cuspSourceTop v c δ) U') := by
      ext y
      constructor
      · rintro ⟨q, hqU, hqy⟩
        have hqU' : (q.1 : E4) ∈ U' := (memU q).mp hqU
        by_cases hlt : q.1 3 < beta (xOf q.1)
        · -- the lower branch meets `range incY` only along the glued boundary
          exfalso
          have hval : cuspCoordMTop a v D c δ q = a.incMbar (D.mbarLow q.1) :=
            cuspCoordMTop_eq_le a v D c δ q (le_of_lt hlt)
          have hT : D.mbarLow q.1 ∉ a.Tset := D.mbarLow_not_TsetTop c δ q.2 hlt
          exact a.incMbar_ne_incY (fun h => hT h.1) (by rw [← hval]; exact hqy)
        · -- the upper branch: `incY` is injective
          have hge : beta (xOf q.1) ≤ q.1 3 := not_lt.mp hlt
          have hsrc : q.1 ∈ cuspSourceTop v c δ := ⟨q.2, hge⟩
          refine ⟨cuspTopUp a v D c δ hδ ⟨q.1, hsrc⟩,
            ⟨⟨q.1, hsrc⟩, hqU', rfl⟩, ?_⟩
          refine a.incY_injective ?_
          rw [← hqy]
          exact (cuspCoordMTop_eq_up a v D c δ hδ ⟨q.1, hsrc⟩).symm
      · rintro ⟨p, ⟨qC, hqU', hqp⟩, hyp⟩
        refine ⟨⟨qC.1, qC.2.1⟩, (memU _).mpr hqU', ?_⟩
        rw [cuspCoordMTop_eq_up a v D c δ hδ qC, hqp]
        simpa using congrArg a.incY hyp
    rw [hset2]
    exact isOpenMap_sigmaMk (i := v) _ hImg

/-- **The unslabbed collar coordinate is an open embedding of the collar box into `M̂`.** -/
theorem isOpenEmbedding_cuspCoordMTop (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2) :
    Topology.IsOpenEmbedding (cuspCoordMTop a v D c δ) :=
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (cuspCoordMTop_continuous a v D c δ) (cuspCoordMTop_injective a v D c δ hδ)
    (isOpenMap_cuspCoordMTop_of a v D c δ hδ)

end Work.Cusp
