import Mathlib
import Submission.Work.ThomBordism.CofAtlas.Signs
import Submission.Work.ThomBordism.CofAtlas.Tdom_comp_Delta

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The chart change `ambChart x → domChart x` and its inverse

`Work.ThomBordism.CofAtlas.Delta_comp_DeltaInv`: the derivative of the change of coordinates from
the *ambient* chart at `x` to the *normal-form* chart at `x`, composed with the derivative of the
reverse change, is the identity.

Both maps are `ModelWithCorners.extendCoordChange` of the two charts, hence inverse to each other;
the point is that at a point of the level set lying over an interior point of `M` the two extended
charts are honest charts of an ordinary manifold, so the chain rule applies.

The file also proves the general helper `tcD_self_eventuallyEq`: the transition `e → e` of the
extended chart of a single chart `e` is the identity near the image of a point of `e.source` whose
image lies in the interior of the model.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter ModelWithCorners
open Work.PTGeometric
open Work.PTGeometric.Lvl

namespace Work.ThomBordism.CofAtlas

noncomputable section

/-! ## The transition `e → e` of an extended chart is the identity near an interior image -/

section SelfTransition

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]

/-- **The transition `e → e` of an extended chart is locally the identity.**  For a chart point
`x` of `e` whose image in the model space lies in the interior of the model, the transition
`I.extendCoordChange e e` agrees with the identity in a neighbourhood of `(e.extend I) x`. -/
theorem tcD_self_eventuallyEq (I : ModelWithCorners 𝕜 E H) (e : OpenPartialHomeomorph M H)
    {x : M} (hx : x ∈ e.source) (hint : (e.extend I) x ∈ interior (range (I : H → E))) :
    I.extendCoordChange e e =ᶠ[𝓝 ((e.extend I) x)] id := by
  have htarget : (e.extend I).target ∈ 𝓝 ((e.extend I) x) := by
    rw [OpenPartialHomeomorph.extend_target]
    refine Filter.inter_mem ?_ ?_
    · refine I.continuous_symm.continuousAt.preimage_mem_nhds ?_
      have h1 : I.symm ((e.extend I) x) = e x := by
        rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply, ModelWithCorners.left_inv]
      rw [h1]
      exact e.open_target.mem_nhds (e.map_source hx)
    · exact mem_of_superset (isOpen_interior.mem_nhds hint) interior_subset
  filter_upwards [htarget] with z hz
  show (e.extend I) ((e.extend I).symm z) = z
  exact (e.extend I).right_inv hz

end SelfTransition

/-! ## The target -/

/-- **The chart change and its inverse are mutually inverse linear maps.** -/
theorem Delta_comp_DeltaInv
    {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) ((⊤ : ENat) : WithTop ENat) M]
    (D : Work.ThomBordism.CofAtlas.Cof k n M) (x : D.S.Pre) {q : D.S.Pre}
    (hx : q ∈ D.S.chartSource x) (hax : q ∈ D.ambSrc x)
    (hint : (q : M) ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).interior M) :
    (D.Delta x (q : M)).comp (D.DeltaInv x (q : M)) = 1 := by
  set p : M := (q : M) with hp
  have hn : (((⊤ : ENat) : WithTop ENat) : ℕ∞ω) ≠ 0 := by simp
  -- the two charts lie in the maximal atlas
  have hambx : D.ambChart x ∈ IsManifold.maximalAtlas (𝓡∂ (NN k)) ((⊤ : ENat) : WithTop ENat) M :=
    IsManifold.chart_mem_maximalAtlas (x : M)
  have hdomx : D.domChart x ∈ IsManifold.maximalAtlas (𝓡∂ (NN k)) ((⊤ : ENat) : WithTop ENat) M :=
    Lvl.Setup.domChartAt_mem_maximalAtlas D.S x
  -- membership of `p` in the sources
  have hxsrc : p ∈ (D.domChart x).source := hx.1
  have haxsrc : p ∈ (D.ambChart x).source := hax
  -- the images lie in the interior of the model space
  have hintDom : (D.domChart x).extend (𝓡∂ (NN k)) p ∈ interior (range (𝓡∂ (NN k))) :=
    tcD_mem_interior_range (𝓡∂ (NN k)) hn hdomx hxsrc hint
  have hintAmb : (D.ambChart x).extend (𝓡∂ (NN k)) p ∈ interior (range (𝓡∂ (NN k))) :=
    tcD_mem_interior_range (𝓡∂ (NN k)) hn hambx haxsrc hint
  -- differentiability of the two transitions
  have hdDomAmb : DifferentiableAt ℝ (D.domAmbChange x) ((D.domChart x).extend (𝓡∂ (NN k)) p) :=
    tcD_differentiableAt (𝓡∂ (NN k)) hn hdomx hambx hxsrc haxsrc hintDom
  have hdAmbDom : DifferentiableAt ℝ (D.ambDomChange x) ((D.ambChart x).extend (𝓡∂ (NN k)) p) :=
    tcD_differentiableAt (𝓡∂ (NN k)) hn hambx hdomx haxsrc hxsrc hintAmb
  -- the second transition sends the chart point to the point at which the first is evaluated
  have hv : (D.domAmbChange x) ((D.domChart x).extend (𝓡∂ (NN k)) p)
      = (D.ambChart x).extend (𝓡∂ (NN k)) p :=
    tcD_apply_extend (𝓡∂ (NN k)) (D.domChart x) (D.ambChart x) hxsrc
  -- the composite is eventually the identity
  have hev1 : ((D.ambDomChange x) ∘ (D.domAmbChange x))
      =ᶠ[𝓝 ((D.domChart x).extend (𝓡∂ (NN k)) p)]
        ((𝓡∂ (NN k)).extendCoordChange (D.domChart x) (D.domChart x)) :=
    tcD_comp_eventuallyEq (𝓡∂ (NN k)) (D.domChart x) (D.ambChart x) (D.domChart x) hxsrc haxsrc
  have hev2 : ((𝓡∂ (NN k)).extendCoordChange (D.domChart x) (D.domChart x))
      =ᶠ[𝓝 ((D.domChart x).extend (𝓡∂ (NN k)) p)] id :=
    tcD_self_eventuallyEq (𝓡∂ (NN k)) (D.domChart x) hxsrc hintDom
  have hev : ((D.ambDomChange x) ∘ (D.domAmbChange x))
      =ᶠ[𝓝 ((D.domChart x).extend (𝓡∂ (NN k)) p)] id := hev1.trans hev2
  -- the chain rule
  have hchain : fderiv ℝ ((D.ambDomChange x) ∘ (D.domAmbChange x))
        ((D.domChart x).extend (𝓡∂ (NN k)) p)
      = (D.Delta x p).comp (D.DeltaInv x p) := by
    rw [fderiv_comp (x := (D.domChart x).extend (𝓡∂ (NN k)) p) (f := (D.domAmbChange x))
      (g := (D.ambDomChange x)) (by rw [hv]; exact hdAmbDom) hdDomAmb]
    rw [hv]
    rfl
  -- the derivative of the identity
  have hid : fderiv ℝ ((D.ambDomChange x) ∘ (D.domAmbChange x))
        ((D.domChart x).extend (𝓡∂ (NN k)) p) = 1 := by
    rw [hev.fderiv_eq, fderiv_id]
    exact ContinuousLinearMap.one_def.symm
  rw [← hchain, hid]

end

end Work.ThomBordism.CofAtlas
