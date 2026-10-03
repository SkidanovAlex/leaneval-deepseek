import Mathlib
import Submission.Lib.Unif2.Work.Analysis.Complex.punctured_ball_connected
import Submission.Work.Horn.HB.image_connectedComponent_eq_of_isCoveringMap

/-!
# The component of `D ∩ g ⁻¹' V` over a domain `V ∋ v` maps onto `V ∖ {v}`

Let `g : ℂ → ℂ` be holomorphic on the open set `D` and a covering map on `D` over the twice
punctured plane `ℂ ∖ {0, v}` (restricted to `D`).  Let `V` be an open connected set with
`0 ∉ V` and `v ∈ V`, and let `W` be the connected component of `D ∩ g ⁻¹' V` through `x`.  If `W`
contains a point `z₀` with `g z₀ ≠ v`, then `g` maps `W` onto `V ∖ {v}`.

The proof is the standard monodromy argument for the covering of the punctured domain
`Z = V ∖ {v}`: the restriction `p : ↥(g ⁻¹' Z) → ↥Z` of `g` to the preimage of `Z` is a covering
map, and the connected component of the base point `z₀` in its total space maps onto the whole
connected component of `p z₀` in the base
(`Work.Horn.HB.image_connectedComponent_eq_of_isCoveringMap`).  Since `V` is an open connected
subset of `ℂ`, `Z = V ∖ {v}` is connected
(`Work.Analysis.Complex.isConnected_diff_singleton_of_mem_interior`), so that component is all of
`↥Z`, and every `y ∈ Z` is the image of a point of the component.  That point lies in `D`, its
image under `g` lies in `Z ⊆ V`, and its component is a preconnected subset of `D ∩ g ⁻¹' V`
containing `z₀ ∈ W`, hence contained in `W`.
-/

namespace Work.Horn.HB

open Set Metric Filter Topology
open scoped Topology

theorem exists_mem_W_of_mem_ball {g : ℂ → ℂ} {D V : Set ℂ} {v y z₀ : ℂ}
    (hDo : IsOpen D) (hgd : DifferentiableOn ℂ g D)
    (hcov : IsCoveringMapOn (fun z : ↥D => g z) {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ v})
    (hVo : IsOpen V) (hVc : IsConnected V) (h0V : (0 : ℂ) ∉ V) (hvV : v ∈ V)
    {x : ℂ} (hxD : x ∈ D) (hxV : g x ∈ V) {W : Set ℂ}
    (hW : W = connectedComponentIn (D ∩ g ⁻¹' V) x)
    {z₀ : ℂ} (hz₀W : z₀ ∈ W) (hz₀v : g z₀ ≠ v)
    {y : ℂ} (hyV : y ∈ V) (hyv : y ≠ v) :
    ∃ z ∈ W, g z = y := by
  classical
  set f : ↥D → ℂ := fun z => g z with hf
  set Z : Set ℂ := V \ {v} with hZdef
  -- `W` consists of points of `D` whose image lies in `V`
  have hWsub : W ⊆ D ∩ g ⁻¹' V := by rw [hW]; exact connectedComponentIn_subset _ _
  have hz₀D : z₀ ∈ D := (hWsub hz₀W).1
  have hz₀V : g z₀ ∈ V := (hWsub hz₀W).2
  have hz₀Z : g z₀ ∈ Z := by rw [hZdef]; exact ⟨hz₀V, hz₀v⟩
  have hZsubV : Z ⊆ V := by intro w hw; rw [hZdef] at hw; exact hw.1
  -- the covering is a covering over `Z` as well, since `Z` avoids `0` and `v`
  have hZsub : Z ⊆ {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ v} := by
    intro w hw
    exact ⟨fun h => h0V (h ▸ hZsubV hw), by intro h; rw [hZdef] at hw; exact hw.2 h⟩
  have hZo : IsOpen Z := by rw [hZdef]; exact hVo.sdiff isClosed_singleton
  -- `Z = V ∖ {v}` is connected because `V` is an open connected subset of `ℂ`
  have hZc : IsConnected Z := by
    rw [hZdef]
    exact Work.Analysis.Complex.isConnected_diff_singleton_of_mem_interior hVc
      (by rw [hVo.interior_eq]; exact hvV)
  have hcovZ : IsCoveringMapOn f Z := by rw [hf]; exact hcov.mono hZsub
  have hP : IsCoveringMap (Z.restrictPreimage f) := hcovZ.isCoveringMap_restrictPreimage
  -- the base point of the total space of the restricted covering
  let e₀ : ↥(f ⁻¹' Z) := ⟨⟨z₀, hz₀D⟩, hz₀Z⟩
  -- the total space and the base are locally path connected, so components of the total space
  -- are open and closed in the base
  have hfZo : IsOpen (f ⁻¹' Z) := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    exact (hcov.continuousAt (hZsub hz)).preimage_mem_nhds (hZo.mem_nhds hz)
  haveI : LocallyPathConnectedSpace ↥D := hDo.locallyPathConnectedSpace
  haveI : LocallyPathConnectedSpace ↥(f ⁻¹' Z) := hfZo.locallyPathConnectedSpace
  haveI : LocallyPathConnectedSpace ↥Z := hZo.locallyPathConnectedSpace
  haveI : PreconnectedSpace ↥Z := isPreconnected_iff_preconnectedSpace.mp hZc.isPreconnected
  -- the component of `e₀` in the total space maps onto all of the (connected) base
  have hyZ : y ∈ Z := by rw [hZdef]; exact ⟨hyV, hyv⟩
  have hb : (⟨y, hyZ⟩ : ↥Z) ∈ (Z.restrictPreimage f) '' connectedComponent e₀ := by
    rw [image_connectedComponent_eq_of_isCoveringMap hP e₀,
      PreconnectedSpace.connectedComponent_eq_univ]
    exact Set.mem_univ _
  obtain ⟨e, he, hpe⟩ := hb
  have hgy : g e.1.1 = y := by
    have h1 := congrArg (fun w : ↥Z => (w : ℂ)) hpe
    simpa [Set.restrictPreimage] using h1
  -- `e` is a point of `D` lying over `y`; it remains to see that it belongs to `W`
  refine ⟨e.1.1, ?_, hgy⟩
  have hcont : Continuous (fun e' : ↥(f ⁻¹' Z) => e'.1.1) :=
    continuous_subtype_val.comp continuous_subtype_val
  have himg : IsPreconnected ((fun e' : ↥(f ⁻¹' Z) => e'.1.1) '' connectedComponent e₀) :=
    isPreconnected_connectedComponent.image _ hcont.continuousOn
  have hsub : ((fun e' : ↥(f ⁻¹' Z) => e'.1.1) '' connectedComponent e₀) ⊆ W := by
    have h1 : ((fun e' : ↥(f ⁻¹' Z) => e'.1.1) '' connectedComponent e₀) ⊆
        connectedComponentIn (D ∩ g ⁻¹' V) z₀ :=
      himg.subset_connectedComponentIn ⟨e₀, mem_connectedComponent, rfl⟩ (by
        rintro _ ⟨e', he', rfl⟩
        exact ⟨e'.1.2, hZsubV e'.2⟩)
    have hz₀W' : z₀ ∈ connectedComponentIn (D ∩ g ⁻¹' V) x := hW ▸ hz₀W
    rw [hW, connectedComponentIn_eq hz₀W']
    exact h1
  exact hsub ⟨e, he, rfl⟩

end Work.Horn.HB
