/-
# The collar chart of `M̂` (the unslabbed family)

This file assembles the **collar chart** of the filling side of `M̂` out of the open embedding
`isOpenEmbedding_cuspCoordMTop` of the coordinate inclusion and the openness of the collar box:

* `cuspChart a v D c δ hδ` — the collar chart, whose target is the **unslabbed** box
  `cuspBoxTop v c δ` of `E4` (side `2δ` around `c`, heights in `(s₁, sTop)`, *no* meridian slab).
  The box straddles the ceiling `s = β(x)`, so the chart covers both the chimney of the hyperbolic
  piece `M̄` (below the ceiling, the branches `incMbar ∘ mbarLow`) and the collar of the filling
  piece (at and above it, the branch `incW ∘ cuspInvOuter`).  Its source is the image of the
  coordinate inclusion `cuspCoordMTop a v D c δ` (`cuspChart_source`), and its inverse on the box is
  again that inclusion (`cuspChart_symm`).

This is the collar chart of the contract, and the *only* collar family that covers the collar layer
`‖p‖∞ ≥ 1/2` of every cusp: the slabbed chart `cuspChartSlab` (`Work.Cusp.ChartMhat`) misses the
four corner directions of the filling square (`u(p) ∈ ℤ`) because of its slab `0 < outerU v x < 1`,
and misses the junction `‖p‖∞ = 1/2` because of its strict height window `(s₁, s_J)`.  See
`Work.Cusp.collarLayer_subset_range_cuspCoordMTop` (every point of the collar layer lies in the
source of one of the charts `cuspChart`) and `Work.Cusp.cover_univ_charts` (the cover theorem).

The hypothesis `δ ≤ 1/2` is what makes the box meet at most one translate of the lattice `Λ_v` in
the meridian direction, and hence what makes `cuspCoordMTop` injective.
-/
import Mathlib
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.TopBox
import Submission.Work.Cusp.TopLayer
import Submission.Work.Cusp.isOpen_cuspBoxTop
import Submission.Work.Cusp.isOpenEmbedding_cuspCoordMTop
import Submission.Work.Cusp.exists_coreChartM
import Submission.Work.Cusp.MChartAux
import Submission.Work.Cusp.ThetaPolarS_cuspInvInner
import Submission.Work.Cusp.exists_polarChartS
import Submission.Work.Cusp.isOpen_polarBox
import Submission.Work.Cusp.isOpenEmbedding_incW_interior
import Submission.Work.Cusp.isOpenMap_fillProj
import Submission.Work.Cusp.isOpen_polarTargetS
import Submission.Work.Cusp.nrm_bndOfU
import Submission.Work.Cusp.nrm_smul
import Submission.Work.Cusp.isOpen_cuspChartBox
import Submission.Work.Cusp.CuspChartAux
import Submission.Work.Cusp.cuspCoordM_continuous
import Submission.Work.Cusp.cuspCoordM_injective
import Submission.Work.Cusp.isOpenEmbedding_layerPtSq
import Submission.Work.Cusp.CuspCollarAux
import Submission.Work.Cusp.continuous_cuspCollarInv
import Submission.Work.Cusp.collarHeight_half
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

/-! ### The collar chart of `M̂` -/

/-- **The collar chart of `M̂`** (unslabbed family): the chart of the upper half space model in the
collar of the `v`-th cusp, crossing the gluing along the truncation torus and covering the four
corner directions of the filling square.  Its target is the open box `cuspBoxTop v c δ` (which
straddles the ceiling `s = β(x)`) and its source is the image of the coordinate inclusion
`cuspCoordMTop a v D c δ`; its value on that image is the identity, i.e. the inverse chart is the
UHS coordinate map (`cuspChart_symm`). -/
noncomputable def cuspChart (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    [Nonempty {q : E4 // q ∈ cuspBoxTop v c δ}] :
    OpenPartialHomeomorph a.Mhat E4 :=
  (Topology.IsOpenEmbedding.toOpenPartialHomeomorph (cuspCoordMTop a v D c δ)
      (isOpenEmbedding_cuspCoordMTop a v D c δ hδ)).symm.trans
    (Topology.IsOpenEmbedding.toOpenPartialHomeomorph
      (fun q : {q : E4 // q ∈ cuspBoxTop v c δ} => (q : E4))
      (isOpen_cuspBoxTop v c δ).isOpenEmbedding_subtypeVal)

/-- The source of the collar chart is the image of the coordinate inclusion `cuspCoordMTop`, i.e.
the image of the open box `cuspBoxTop v c δ` in `M̂`. -/
theorem cuspChart_source (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    [Nonempty {q : E4 // q ∈ cuspBoxTop v c δ}] :
    (cuspChart a v D c δ hδ).source = Set.range (cuspCoordMTop a v D c δ) := by
  simp only [cuspChart, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, Set.preimage_univ, Set.inter_univ]

/-- The target of the collar chart is the unslabbed box `cuspBoxTop v c δ`. -/
theorem cuspChart_target (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    [Nonempty {q : E4 // q ∈ cuspBoxTop v c δ}] :
    (cuspChart a v D c δ hδ).target = cuspBoxTop v c δ := by
  simp only [cuspChart, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, Set.preimage_univ, Set.inter_univ,
    Subtype.range_val]

/-- **The collar chart inverts the coordinate inclusion**: on the image of the box it is the UHS
coordinate map. -/
theorem cuspChart_apply (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    [Nonempty {q : E4 // q ∈ cuspBoxTop v c δ}] (q : {q : E4 // q ∈ cuspBoxTop v c δ}) :
    cuspChart a v D c δ hδ (cuspCoordMTop a v D c δ q) = (q : E4) := by
  have hleft : (Topology.IsOpenEmbedding.toOpenPartialHomeomorph (cuspCoordMTop a v D c δ)
      (isOpenEmbedding_cuspCoordMTop a v D c δ hδ)).symm (cuspCoordMTop a v D c δ q) = q :=
    OpenPartialHomeomorph.left_inv _ (Set.mem_univ q)
  rw [cuspChart, OpenPartialHomeomorph.trans_apply, hleft]
  rfl

/-- **The explicit inverse of the collar chart**: the point of `M̂` with UHS coordinates `q` in the
box, i.e. the coordinate inclusion. -/
theorem cuspChart_symm (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    [Nonempty {q : E4 // q ∈ cuspBoxTop v c δ}] {q : E4} (hq : q ∈ cuspBoxTop v c δ) :
    (cuspChart a v D c δ hδ).symm q = cuspCoordMTop a v D c δ ⟨q, hq⟩ := by
  have h : (cuspChart a v D c δ hδ) (cuspCoordMTop a v D c δ ⟨q, hq⟩) = q :=
    cuspChart_apply a v D c δ hδ ⟨q, hq⟩
  have h2 : (cuspCoordMTop a v D c δ ⟨q, hq⟩) ∈ (cuspChart a v D c δ hδ).source := by
    rw [cuspChart_source]
    exact Set.mem_range_self _
  have h3 := OpenPartialHomeomorph.left_inv (cuspChart a v D c δ hδ) h2
  rw [h] at h3
  exact h3

end Work.Cusp
