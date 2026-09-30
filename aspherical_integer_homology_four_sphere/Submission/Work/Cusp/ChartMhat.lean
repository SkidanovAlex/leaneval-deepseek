/-
# The filling charts of `M̂`

This file assembles the `OpenPartialHomeomorph a.Mhat E4` charts of the filling side of `M̂` out of
the coordinate inclusions and open-embedding lemmas of `Work.Cusp.Assembly`:

* `cuspChartSlab a v D c δ hδ` — the **slabbed** collar chart (the UHS chart of the gluing on the
  *slab* box `cuspChartBox v c δ`, whose height window is `(s₁, s_J)` and which carries the meridian
  slab `0 < outerU v x < 1`): its target straddles the ceiling `s = β(x)`, so the chart covers both
  the chimney of the hyperbolic piece `M̄` and the collar of the filling piece.  Its source is the
  image of the coordinate inclusion `cuspCoordM a v D c δ`, and its inverse on the box is
  `cuspChartSlab_symm`.  *This* family is *not* the one used for the cover: because of its slab and
  of the strict window `(s₁, s_J)` it misses the four corner directions of the square (`u(p) ∈ ℤ`)
  and the junction `‖p‖∞ = 1/2`.  The chart which does cover the collar is `Work.Cusp.cuspChart`
  (the *unslabbed* family, `Submission/Work/Cusp/ChartTop.lean`); the slabbed one is kept because it
  is the one whose target is a genuine box of the *open* slab `0 < outerU v x < 1`;
* `polarChart a v tor c k W hW hsec` — the **polar chart** of the filling piece of the `v`-th cusp,
  in the coordinates `(r,θ,w₁,w₂)`, near the `(c,k)`-th wedge of the perimeter and over the local
  `w`-section `W`;
* `coreChart a v tor W hW hsec` — the **core chart**, in the Cartesian coordinates `(a,b,w₁,w₂)`.

The first is an open embedding by `Work.Cusp.isOpenEmbedding_cuspCoordM`, and the other two are the
charts delivered by `Work.Cusp.exists_polarChartM` / `Work.Cusp.exists_coreChartM`.  Each of them
comes with its explicit inverse: `cuspChartSlab_symm` is the coordinate inclusion `cuspCoordM`,
`polarChart_symm` is `polarCoordM` and `coreChart_symm` is `coreCoordM`, so a caller never has to
unfold the charts.

The hypotheses of the polar and core charts are the *section condition* `hsec` on the box `W`: two
real `y` whose `wOf`-images lie in `W` and whose classes in `(ℝ/ℤ)²` agree must be equal.  This is
what pins the lift of the torus coordinates, and hence what makes the coordinate inclusion
injective.  For the collar chart the corresponding pinning is the constraint `0 < outerU v x < 1`
of the box together with `δ ≤ 1/2`.
-/
import Mathlib
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.exists_coreChartM
import Submission.Work.Cusp.exists_polarChartM
import Submission.Work.Cusp.isOpen_cuspChartBox
import Submission.Work.Cusp.isOpenEmbedding_cuspCoordM

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function

namespace Work.Cusp

/-! ### The collar chart -/

/-- **The collar chart of `M̂`**: the chart of the upper half space model in the collar of the
`v`-th cusp, crossing the gluing along the truncation torus.  Its target is the open box
`cuspChartBox v c δ` (which straddles the ceiling `s = β(x)`) and its source is the image of the
coordinate inclusion `cuspCoordM a v D c δ`; its value on that image is the identity, i.e. the
inverse chart is the UHS coordinate map (`cuspChartSlab_symm`).

The hypothesis `δ ≤ 1/2` is what makes the box meet at most one translate of the lattice in the
`σ`-direction, and hence `cuspCoordM` injective. -/
noncomputable def cuspChartSlab (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    [Nonempty {q : E4 // q ∈ cuspChartBox v c δ}] :
    OpenPartialHomeomorph a.Mhat E4 :=
  (Topology.IsOpenEmbedding.toOpenPartialHomeomorph (cuspCoordM a v D c δ)
      (isOpenEmbedding_cuspCoordM a v D c δ hδ)).symm.trans
    (Topology.IsOpenEmbedding.toOpenPartialHomeomorph
      (fun q : {q : E4 // q ∈ cuspChartBox v c δ} => (q : E4))
      (isOpen_cuspChartBox v c δ).isOpenEmbedding_subtypeVal)

/-- The source of the collar chart is the image of the coordinate inclusion `cuspCoordM`, i.e. the
image of the open box `cuspChartBox v c δ` in `M̂`. -/
theorem cuspChartSlab_source (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    [Nonempty {q : E4 // q ∈ cuspChartBox v c δ}] :
    (cuspChartSlab a v D c δ hδ).source = Set.range (cuspCoordM a v D c δ) := by
  simp only [cuspChartSlab, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, Set.preimage_univ, Set.inter_univ]

/-- The target of the collar chart is the open box `cuspChartBox v c δ`. -/
theorem cuspChartSlab_target (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    [Nonempty {q : E4 // q ∈ cuspChartBox v c δ}] :
    (cuspChartSlab a v D c δ hδ).target = cuspChartBox v c δ := by
  simp only [cuspChartSlab, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, Set.preimage_univ, Set.inter_univ,
    Subtype.range_val]

/-- **The collar chart inverts the coordinate inclusion**: on the image of the box it is the UHS
coordinate map. -/
theorem cuspChartSlab_apply (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    [Nonempty {q : E4 // q ∈ cuspChartBox v c δ}] (q : {q : E4 // q ∈ cuspChartBox v c δ}) :
    cuspChartSlab a v D c δ hδ (cuspCoordM a v D c δ q) = (q : E4) := by
  have hleft : (Topology.IsOpenEmbedding.toOpenPartialHomeomorph (cuspCoordM a v D c δ)
      (isOpenEmbedding_cuspCoordM a v D c δ hδ)).symm (cuspCoordM a v D c δ q) = q :=
    OpenPartialHomeomorph.left_inv _ (Set.mem_univ q)
  rw [cuspChartSlab, OpenPartialHomeomorph.trans_apply, hleft]
  rfl

/-- **The explicit inverse of the collar chart**: the point of `M̂` with UHS coordinates `q` in the
box, i.e. the coordinate inclusion. -/
theorem cuspChartSlab_symm (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    [Nonempty {q : E4 // q ∈ cuspChartBox v c δ}] {q : E4}
    (hq : q ∈ cuspChartBox v c δ) :
    (cuspChartSlab a v D c δ hδ).symm q = cuspCoordM a v D c δ ⟨q, hq⟩ := by
  have h : (cuspChartSlab a v D c δ hδ) (cuspCoordM a v D c δ ⟨q, hq⟩) = q :=
    cuspChartSlab_apply a v D c δ hδ ⟨q, hq⟩
  have h2 : (cuspCoordM a v D c δ ⟨q, hq⟩) ∈ (cuspChartSlab a v D c δ hδ).source := by
    rw [cuspChartSlab_source]
    exact Set.mem_range_self _
  have h3 := OpenPartialHomeomorph.left_inv (cuspChartSlab a v D c δ hδ) h2
  rw [h] at h3
  exact h3

/-! ### The polar and core charts -/

/-- **The `(c,k)`-th polar chart of the filling piece of the `v`-th cusp as a chart of `M̂`**, over
the open `w`-box `W` of the torus coordinates (a local section of `ℝ² → (ℝ/ℤ)²` in the
`w`-coordinates, hypothesis `hsec`).  Its target is the box `polarBoxSect v c k W` and its source is
the image of the coordinate inclusion `polarCoordM a v tor c k W`; the inverse chart is that
inclusion (`polarChart_symm`). -/
noncomputable def polarChart (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) (c : ℝ) (k : Fin 4) (W : Set E2)
    (hW : IsOpen W)
    (hsec : ∀ y y' : E2, wOf v y ∈ W → wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    OpenPartialHomeomorph a.Mhat E4 :=
  Classical.choose (exists_polarChartM a v tor c k W hW hsec)

/-- The source of the polar chart is the image of the box `polarBoxSect v c k W`. -/
theorem polarChart_source (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) (c : ℝ) (k : Fin 4) (W : Set E2)
    (hW : IsOpen W)
    (hsec : ∀ y y' : E2, wOf v y ∈ W → wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    (polarChart a v tor c k W hW hsec).source = Set.range (polarCoordM a v tor c k W) := by
  unfold polarChart
  rw [(Classical.choose_spec (exists_polarChartM a v tor c k W hW hsec)).1, Set.image_univ]

/-- The target of the polar chart is the box `polarBoxSect v c k W`. -/
theorem polarChart_target (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) (c : ℝ) (k : Fin 4) (W : Set E2)
    (hW : IsOpen W)
    (hsec : ∀ y y' : E2, wOf v y ∈ W → wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    (polarChart a v tor c k W hW hsec).target = polarBoxSect v c k W := by
  unfold polarChart
  exact (Classical.choose_spec (exists_polarChartM a v tor c k W hW hsec)).2.1

/-- The polar chart inverts the coordinate inclusion `polarCoordM`. -/
theorem polarChart_apply (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) (c : ℝ) (k : Fin 4) (W : Set E2)
    (hW : IsOpen W)
    (hsec : ∀ y y' : E2, wOf v y ∈ W → wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y')
    {q : E4} (hq : q ∈ polarBoxSect v c k W) :
    polarChart a v tor c k W hW hsec (polarCoordM a v tor c k W ⟨q, hq⟩) = q := by
  unfold polarChart
  exact (Classical.choose_spec (exists_polarChartM a v tor c k W hW hsec)).2.2 q hq

/-- **The explicit inverse of the polar chart**: the coordinate inclusion `polarCoordM`. -/
theorem polarChart_symm (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) (c : ℝ) (k : Fin 4) (W : Set E2)
    (hW : IsOpen W)
    (hsec : ∀ y y' : E2, wOf v y ∈ W → wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y')
    {q : E4} (hq : q ∈ polarBoxSect v c k W) :
    (polarChart a v tor c k W hW hsec).symm q = polarCoordM a v tor c k W ⟨q, hq⟩ := by
  have h : polarChart a v tor c k W hW hsec (polarCoordM a v tor c k W ⟨q, hq⟩) = q :=
    polarChart_apply a v tor c k W hW hsec hq
  have h2 : (polarCoordM a v tor c k W ⟨q, hq⟩) ∈ (polarChart a v tor c k W hW hsec).source := by
    rw [polarChart_source]
    exact Set.mem_range_self _
  have h3 := OpenPartialHomeomorph.left_inv (polarChart a v tor c k W hW hsec) h2
  rw [h] at h3
  exact h3

/-- **The core chart of the filling piece of the `v`-th cusp as a chart of `M̂`**, over the open
`w`-box `W`.  Its target is the box `coreBoxSect W` and its source is the image of the coordinate
inclusion `coreCoordM a v tor W`; the inverse chart is that inclusion (`coreChart_symm`). -/
noncomputable def coreChart (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) (W : Set E2) (hW : IsOpen W)
    (hsec : ∀ y y' : E2, wOf v y ∈ W → wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    OpenPartialHomeomorph a.Mhat E4 :=
  Classical.choose (exists_coreChartM a v tor W hW hsec)

/-- The source of the core chart is the image of the box `coreBoxSect W`. -/
theorem coreChart_source (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) (W : Set E2) (hW : IsOpen W)
    (hsec : ∀ y y' : E2, wOf v y ∈ W → wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    (coreChart a v tor W hW hsec).source = Set.range (coreCoordM a v tor W) := by
  unfold coreChart
  rw [(Classical.choose_spec (exists_coreChartM a v tor W hW hsec)).1, Set.image_univ]

/-- The target of the core chart is the box `coreBoxSect W`. -/
theorem coreChart_target (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) (W : Set E2) (hW : IsOpen W)
    (hsec : ∀ y y' : E2, wOf v y ∈ W → wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    (coreChart a v tor W hW hsec).target = coreBoxSect W := by
  unfold coreChart
  exact (Classical.choose_spec (exists_coreChartM a v tor W hW hsec)).2.1

/-- The core chart inverts the coordinate inclusion `coreCoordM`. -/
theorem coreChart_apply (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) (W : Set E2) (hW : IsOpen W)
    (hsec : ∀ y y' : E2, wOf v y ∈ W → wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y')
    {q : E4} (hq : q ∈ coreBoxSect W) :
    coreChart a v tor W hW hsec (coreCoordM a v tor W ⟨q, hq⟩) = q := by
  unfold coreChart
  exact (Classical.choose_spec (exists_coreChartM a v tor W hW hsec)).2.2 q hq

/-- **The explicit inverse of the core chart**: the coordinate inclusion `coreCoordM`. -/
theorem coreChart_symm (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) (W : Set E2) (hW : IsOpen W)
    (hsec : ∀ y y' : E2, wOf v y ∈ W → wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y')
    {q : E4} (hq : q ∈ coreBoxSect W) :
    (coreChart a v tor W hW hsec).symm q = coreCoordM a v tor W ⟨q, hq⟩ := by
  have h : coreChart a v tor W hW hsec (coreCoordM a v tor W ⟨q, hq⟩) = q :=
    coreChart_apply a v tor W hW hsec hq
  have h2 : (coreCoordM a v tor W ⟨q, hq⟩) ∈ (coreChart a v tor W hW hsec).source := by
    rw [coreChart_source]
    exact Set.mem_range_self _
  have h3 := OpenPartialHomeomorph.left_inv (coreChart a v tor W hW hsec) h2
  rw [h] at h3
  exact h3

end Work.Cusp
