import Mathlib
import Submission.Work.ThomBordism.CofAtlas.Signs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The change of normal-form coordinates decomposes through the ambient ones

`Work.ThomBordism.CofAtlas.Tdom_comp_Delta`: for `x y` in the level set and `q` a point of the
overlap (lying over an interior point of `M`),

`Tdom x y q ∘ Delta x q = Delta y q ∘ Tex x y q`.

All four maps are derivatives of chart transitions `I.extendCoordChange e e'` of the ambient
manifold, and the identity is the chain rule for the decomposition

`(domChart x → domChart y) = (domChart x → ambChart x → ambChart y → domChart y)`,

i.e. the fact that the two composites `domChange x y ∘ ambDomChange x` and
`ambDomChange y ∘ ambChange x y` agree near the point (both equal
`extendCoordChange (ambChart x) (domChart y)`).  The auxiliary lemmas about
`ModelWithCorners.extendCoordChange` (`tcD_*` below) are proved here from the definition.

**Note for the requester.**  `Submission/Work/ThomBordism/CofAtlas/Pieces.lean` declares the *same*
theorem name (`Work.ThomBordism.CofAtlas.Tdom_comp_Delta`) with a `sorry`; the two modules must not
be imported together (duplicate declaration).  Replace the copy in `Pieces.lean` by this one
(e.g. delete it, or keep `Pieces.lean` and use `Tdom_comp_Delta` from here).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter ModelWithCorners
open Classical

namespace Work.ThomBordism.CofAtlas

noncomputable section

/-! ## Auxiliary lemmas about `ModelWithCorners.extendCoordChange` -/

section ExtendCoordChange

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [TopologicalSpace M]

/-- **The value of a chart transition at a chart point.**  For `x ∈ e.source ∩ e'.source`, the
transition `I.extendCoordChange e e'` sends `I (e x)` to `I (e' x)`. -/
theorem tcD_apply_extend (I : ModelWithCorners 𝕜 E H) (e e' : OpenPartialHomeomorph M H)
    {x : M} (hx : x ∈ e.source) :
    (I.extendCoordChange e e') ((e.extend I) x) = (e'.extend I) x := by
  simp only [ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply,
    OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    Function.comp_apply, ModelWithCorners.left_inv, OpenPartialHomeomorph.left_inv _ hx]

/-- **Transitivity of chart transitions, pointwise.**  The transition `e → e''` is the transition
`e → e'` followed by the transition `e' → e''`, on the source of the second. -/
theorem tcD_comp_apply (I : ModelWithCorners 𝕜 E H) (e e' e'' : OpenPartialHomeomorph M H)
    {z : E} (hw : (e.symm (I.symm z)) ∈ e'.source) :
    (I.extendCoordChange e' e'') ((I.extendCoordChange e e') z) = (I.extendCoordChange e e'') z := by
  simp only [ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply,
    OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    Function.comp_apply, ModelWithCorners.left_inv, OpenPartialHomeomorph.left_inv _ hw]

/-- **Transitivity of chart transitions, near a chart point.**  The composite of the transitions
`e → e'` and `e' → e''` agrees with the transition `e → e''` in a neighbourhood of `I (e x)`. -/
theorem tcD_comp_eventuallyEq (I : ModelWithCorners 𝕜 E H) (e e' e'' : OpenPartialHomeomorph M H)
    {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    ((I.extendCoordChange e' e'') ∘ (I.extendCoordChange e e'))
      =ᶠ[𝓝 ((e.extend I) x)] (I.extendCoordChange e e'') := by
  have hcont : ContinuousAt ((e.extend I).symm : E → M) ((e.extend I) x) :=
    OpenPartialHomeomorph.continuousAt_extend_symm e hx
  have hlt : (e.extend I).symm ((e.extend I) x) ∈ e'.source := by
    rwa [OpenPartialHomeomorph.extend_left_inv e hx]
  have hmem : (fun z : E => e.symm (I.symm z)) ⁻¹' e'.source ∈ 𝓝 ((e.extend I) x) := by
    refine mem_of_superset (hcont.preimage_mem_nhds (e'.open_source.mem_nhds hlt)) ?_
    intro z hz
    simpa only [Set.mem_preimage, OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply]
      using hz
  filter_upwards [hmem] with z hz
  exact tcD_comp_apply I e e' e'' (by simpa only [Set.mem_preimage] using hz)

variable {n : ℕ∞ω} [ChartedSpace H M]

/-- **A chart transition is differentiable at the image of an interior point of its source.** -/
theorem tcD_differentiableAt (I : ModelWithCorners 𝕜 E H) {e e' : OpenPartialHomeomorph M H}
    (hn : n ≠ 0) (he : e ∈ IsManifold.maximalAtlas I n M)
    (he' : e' ∈ IsManifold.maximalAtlas I n M)
    {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source)
    (hz : (e.extend I) x ∈ interior (range I)) :
    DifferentiableAt 𝕜 (I.extendCoordChange e e') ((e.extend I) x) := by
  have h1 : ContDiffWithinAt 𝕜 n (I.extendCoordChange e e') (range I) ((e.extend I) x) :=
    contDiffWithinAt_extendCoordChange' he he' hx hx'
  exact (h1.contDiffAt (mem_of_superset (isOpen_interior.mem_nhds hz)
    interior_subset)).differentiableAt hn

/-- **The image of an interior point in a maximal-atlas chart lies in the interior of the model
space.** -/
theorem tcD_mem_interior_range (I : ModelWithCorners 𝕜 E H) [IsManifold I n M]
    {e : OpenPartialHomeomorph M H} (hn : n ≠ 0) (he : e ∈ IsManifold.maximalAtlas I n M)
    {x : M} (hx : x ∈ e.source) (hint : I.IsInteriorPoint x) :
    (e.extend I) x ∈ interior (range I) :=
  OpenPartialHomeomorph.interior_extend_target_subset_interior_range e
    ((Work.ThomBordism.Transversality.Preimage.isInteriorPoint_iff_of_mem_maximalAtlas
      hn he hx).1 hint)

end ExtendCoordChange

/-! ## The target -/

/-- **The change of normal-form coordinates decomposes through the ambient ones.** -/
theorem Tdom_comp_Delta
    {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) ((⊤ : ENat) : WithTop ENat) M]
    (D : Work.ThomBordism.CofAtlas.Cof k n M) (x y : D.S.Pre) {q : D.S.Pre}
    (hx : q ∈ D.S.chartSource x) (hy : q ∈ D.S.chartSource y)
    (hax : q ∈ D.ambSrc x) (hay : q ∈ D.ambSrc y)
    (hint : (q : M) ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).interior M) :
    (D.Tdom x y (q : M)).comp (D.Delta x (q : M))
      = (D.Delta y (q : M)).comp (D.Tex x y (q : M)) := by
  set p : M := (q : M)
  have hn : (((⊤ : ENat) : WithTop ENat) : ℕ∞ω) ≠ 0 := by simp
  -- charts lie in the maximal atlas
  have hambx : D.ambChart x ∈ IsManifold.maximalAtlas (𝓡∂ (NN k)) ((⊤ : ENat) : WithTop ENat) M :=
    IsManifold.chart_mem_maximalAtlas (x : M)
  have hamby : D.ambChart y ∈ IsManifold.maximalAtlas (𝓡∂ (NN k)) ((⊤ : ENat) : WithTop ENat) M :=
    IsManifold.chart_mem_maximalAtlas (y : M)
  have hdomx : D.domChart x ∈ IsManifold.maximalAtlas (𝓡∂ (NN k)) ((⊤ : ENat) : WithTop ENat) M :=
    Work.PTGeometric.Lvl.Setup.domChartAt_mem_maximalAtlas D.S x
  have hdomy : D.domChart y ∈ IsManifold.maximalAtlas (𝓡∂ (NN k)) ((⊤ : ENat) : WithTop ENat) M :=
    Work.PTGeometric.Lvl.Setup.domChartAt_mem_maximalAtlas D.S y
  -- membership of `p` in the sources
  have hxsrc : p ∈ (D.domChart x).source := hx.1
  have hysrc : p ∈ (D.domChart y).source := hy.1
  have haxsrc : p ∈ (D.ambChart x).source := hax
  have haysrc : p ∈ (D.ambChart y).source := hay
  -- interior facts
  have hintX : (D.ambChart x).extend (𝓡∂ (NN k)) p ∈ interior (range (𝓡∂ (NN k))) :=
    tcD_mem_interior_range (𝓡∂ (NN k)) hn hambx haxsrc hint
  have hintY : (D.ambChart y).extend (𝓡∂ (NN k)) p ∈ interior (range (𝓡∂ (NN k))) :=
    tcD_mem_interior_range (𝓡∂ (NN k)) hn hamby haysrc hint
  have hintDomx : (D.domChart x).extend (𝓡∂ (NN k)) p ∈ interior (range (𝓡∂ (NN k))) :=
    tcD_mem_interior_range (𝓡∂ (NN k)) hn hdomx hxsrc hint
  -- differentiability of the four transitions
  have hdAmbDomx : DifferentiableAt ℝ (D.ambDomChange x) ((D.ambChart x).extend (𝓡∂ (NN k)) p) :=
    tcD_differentiableAt (𝓡∂ (NN k)) hn hambx hdomx haxsrc hxsrc hintX
  have hdAmbDomy : DifferentiableAt ℝ (D.ambDomChange y) ((D.ambChart y).extend (𝓡∂ (NN k)) p) :=
    tcD_differentiableAt (𝓡∂ (NN k)) hn hamby hdomy haysrc hysrc hintY
  have hdDom : DifferentiableAt ℝ (D.domChange x y) ((D.domChart x).extend (𝓡∂ (NN k)) p) :=
    tcD_differentiableAt (𝓡∂ (NN k)) hn hdomx hdomy hxsrc hysrc hintDomx
  have hdAmbCh : DifferentiableAt ℝ (D.ambChange x y) ((D.ambChart x).extend (𝓡∂ (NN k)) p) :=
    tcD_differentiableAt (𝓡∂ (NN k)) hn hambx hamby haxsrc haysrc hintX
  -- values at the base point
  have hv1 : (D.ambDomChange x) ((D.ambChart x).extend (𝓡∂ (NN k)) p)
      = (D.domChart x).extend (𝓡∂ (NN k)) p :=
    tcD_apply_extend (𝓡∂ (NN k)) (D.ambChart x) (D.domChart x) haxsrc
  have hv2 : (D.ambChange x y) ((D.ambChart x).extend (𝓡∂ (NN k)) p)
      = (D.ambChart y).extend (𝓡∂ (NN k)) p :=
    tcD_apply_extend (𝓡∂ (NN k)) (D.ambChart x) (D.ambChart y) haxsrc
  -- the two composites agree near the base point
  have hevL : ((D.domChange x y) ∘ (D.ambDomChange x))
      =ᶠ[𝓝 ((D.ambChart x).extend (𝓡∂ (NN k)) p)]
        ((𝓡∂ (NN k)).extendCoordChange (D.ambChart x) (D.domChart y)) :=
    tcD_comp_eventuallyEq (𝓡∂ (NN k)) (D.ambChart x) (D.domChart x) (D.domChart y) haxsrc hxsrc
  have hevR : ((D.ambDomChange y) ∘ (D.ambChange x y))
      =ᶠ[𝓝 ((D.ambChart x).extend (𝓡∂ (NN k)) p)]
        ((𝓡∂ (NN k)).extendCoordChange (D.ambChart x) (D.domChart y)) :=
    tcD_comp_eventuallyEq (𝓡∂ (NN k)) (D.ambChart x) (D.ambChart y) (D.domChart y) haxsrc haysrc
  have hev := hevL.trans hevR.symm
  have hfderiv : fderiv ℝ ((D.domChange x y) ∘ (D.ambDomChange x))
        ((D.ambChart x).extend (𝓡∂ (NN k)) p)
      = fderiv ℝ ((D.ambDomChange y) ∘ (D.ambChange x y))
        ((D.ambChart x).extend (𝓡∂ (NN k)) p) :=
    hev.fderiv_eq
  -- the chain rules
  have hdDom' : DifferentiableAt ℝ (D.domChange x y)
      ((D.ambDomChange x) ((D.ambChart x).extend (𝓡∂ (NN k)) p)) := by
    rw [hv1]; exact hdDom
  have hdAmbDomy' : DifferentiableAt ℝ (D.ambDomChange y)
      ((D.ambChange x y) ((D.ambChart x).extend (𝓡∂ (NN k)) p)) := by
    rw [hv2]; exact hdAmbDomy
  have hchainL : fderiv ℝ ((D.domChange x y) ∘ (D.ambDomChange x))
        ((D.ambChart x).extend (𝓡∂ (NN k)) p)
      = (D.Tdom x y p).comp (D.Delta x p) := by
    rw [fderiv_comp (x := (D.ambChart x).extend (𝓡∂ (NN k)) p) (f := (D.ambDomChange x))
      (g := (D.domChange x y)) hdDom' hdAmbDomx]
    rw [hv1]
    simp only [Cof.Tdom, Cof.Delta, Cof.domExt, Cof.ambExt]
  have hchainR : fderiv ℝ ((D.ambDomChange y) ∘ (D.ambChange x y))
        ((D.ambChart x).extend (𝓡∂ (NN k)) p)
      = (D.Delta y p).comp (D.Tex x y p) := by
    rw [fderiv_comp (x := (D.ambChart x).extend (𝓡∂ (NN k)) p) (f := (D.ambChange x y))
      (g := (D.ambDomChange y)) hdAmbDomy' hdAmbCh]
    rw [hv2]
    simp only [Cof.Delta, Cof.Tex, Cof.ambExt]
  rw [← hchainL, hfderiv, hchainR]

end

end Work.ThomBordism.CofAtlas
