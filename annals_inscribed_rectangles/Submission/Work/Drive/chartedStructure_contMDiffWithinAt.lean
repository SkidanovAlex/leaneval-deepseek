import Mathlib

/-!
# Smoothness is transported by a homeomorphism-transported `ChartedSpace`

If `e : M ≃ₜ M'` is a homeomorphism and `M'` is given the `ChartedSpace` structure pushed
forward from `M` along `e` (`Homeomorph.chartedSpace e`), then a map `f : Z → M'` is `C^n`
within `s` at `z` for that structure exactly when `e.symm ∘ f` is `C^n` within `s` at `z`
for the original structure on `M`.

The point is that the pushed-forward preferred chart at `q : M'` is `L ≫ₕ chartAt H (e.symm q)`
where `L` is a local inverse of `e` at `e.symm q`; on a neighbourhood of the relevant point
`L` agrees with `e.symm`, which is precisely the change of charts relating `f` to `e.symm ∘ f`.
-/

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold Topology Filter

theorem chartedStructure_contMDiffWithinAt
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H')
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {M' : Type*} [TopologicalSpace M'] (e : M ≃ₜ M')
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace H' Z]
    {n : WithTop ℕ∞} (f : Z → M') (s : Set Z) (z : Z) :
    @ContMDiffWithinAt 𝕜 _ E' _ _ H' _ I' Z _ _ E _ _ H _ I M' _ (Homeomorph.chartedSpace e)
        n f s z ↔
      ContMDiffWithinAt I' I n (fun y => e.symm (f y)) s z := by
  let : ChartedSpace H M' := Homeomorph.chartedSpace e
  -- The right inverse of `e` used by `Homeomorph.chartedSpace e` agrees with `e.symm`.
  let g : M' → M := (Function.Surjective.hasRightInverse e.surjective).choose
  have hg : Function.RightInverse g ⇑e :=
    (Function.Surjective.hasRightInverse e.surjective).choose_spec
  have hgq : g (f z) = e.symm (f z) :=
    e.injective (by rw [hg (f z), e.apply_symm_apply])
  -- The preferred chart of the pushed-forward structure at `f z`, and the chart of `M` at
  -- the point `e.symm (f z)` it reduces to.
  let L : OpenPartialHomeomorph M' M := e.isLocalHomeomorph.localInverseAt (g (f z))
  let C : OpenPartialHomeomorph M H := chartAt H (e.symm (f z))
  let φ : OpenPartialHomeomorph Z H' := chartAt H' z
  have hCeq : (chartAt H (g (f z)) : OpenPartialHomeomorph M H) = chartAt H (e.symm (f z)) := by
    rw [hgq]
  have hchart : (chartAt H (f z) : OpenPartialHomeomorph M' H) = L ≫ₕ C := by
    change (e.isLocalHomeomorph.localInverseAt (g (f z))) ≫ₕ (chartAt H (g (f z))) = _
    rw [hCeq]
  have hmemz : f z ∈ L.source := by
    have := IsLocalHomeomorph.apply_self_mem_localInverseAt_source e.isLocalHomeomorph (x := g (f z))
    simpa [L, hg (f z)] using this
  have hLz : L (f z) = e.symm (f z) := by
    apply e.injective
    rw [IsLocalHomeomorph.apply_localInverseAt_of_mem (hf := e.isLocalHomeomorph) (x := g (f z)) hmemz,
      e.apply_symm_apply]
  have hcont : ContinuousWithinAt f s z ↔ ContinuousWithinAt (fun y => e.symm (f y)) s z :=
    Homeomorph.comp_continuousWithinAt_iff e.symm f s z
  -- The two charts differ by the change of variable `e.symm`, which is legitimate near `z`.
  have hprop (hf : ContinuousWithinAt f s z) :
      ContDiffWithinAtProp I' I n (⇑(chartAt H (f z)) ∘ f ∘ ⇑(chartAt H' z).symm)
          (⇑(chartAt H' z).symm ⁻¹' s) (⇑(chartAt H' z) z) ↔
      ContDiffWithinAtProp I' I n (⇑(chartAt H (e.symm (f z))) ∘ (fun y => e.symm (f y)) ∘
          ⇑(chartAt H' z).symm) (⇑(chartAt H' z).symm ⁻¹' s) (⇑(chartAt H' z) z) := by
    rw [hchart, ContDiffWithinAtProp, ContDiffWithinAtProp]
    -- `Φ` is `f` read in the source chart of `Z`, as a function of the point of the model space.
    have hΦ : ContinuousAt (fun y : E' => ⇑φ.symm (⇑I'.symm y)) (I' (⇑φ z)) := by
      have h1 : ContinuousAt (⇑I'.symm) (I' (⇑φ z)) := I'.continuous_symm.continuousAt
      have h2 : ContinuousAt (⇑φ.symm) (⇑I'.symm (I' (⇑φ z))) := by
        simpa only [ModelWithCorners.left_inv] using
          φ.continuousAt_symm (φ.map_source (mem_chart_source H' z))
      exact h2.comp h1
    have hf' : ContinuousWithinAt f s (⇑φ.symm (⇑I'.symm (I' (⇑φ z)))) := by
      simpa only [ModelWithCorners.left_inv, φ.left_inv (mem_chart_source H' z)] using hf
    have hfs : ContinuousWithinAt (fun y : E' => f (⇑φ.symm (⇑I'.symm y)))
        (⇑I'.symm ⁻¹' ⇑φ.symm ⁻¹' s ∩ Set.range ⇑I') (I' (⇑φ z)) :=
      ContinuousWithinAt.comp (f := fun y : E' => ⇑φ.symm (⇑I'.symm y)) (x := I' (⇑φ z))
        hf' hΦ.continuousWithinAt (fun y hy => hy.1)
    have hLmem : L.source ∈ 𝓝 (f (⇑φ.symm (⇑I'.symm (I' (⇑φ z))))) := by
      simpa only [ModelWithCorners.left_inv, φ.left_inv (mem_chart_source H' z)] using
        L.open_source.mem_nhds hmemz
    have hmem : ∀ᶠ y in 𝓝[⇑I'.symm ⁻¹' ⇑φ.symm ⁻¹' s ∩ Set.range ⇑I'] (I' (⇑φ z)),
        f (⇑φ.symm (⇑I'.symm y)) ∈ L.source :=
      hfs.preimage_mem_nhdsWithin hLmem
    have hkey : (I ∘ (⇑(L ≫ₕ C) ∘ f ∘ ⇑φ.symm) ∘ ⇑I'.symm)
        =ᶠ[𝓝[⇑I'.symm ⁻¹' ⇑φ.symm ⁻¹' s ∩ Set.range ⇑I'] (I' (⇑φ z))]
        (I ∘ (⇑C ∘ (fun y => e.symm (f y)) ∘ ⇑φ.symm) ∘ ⇑I'.symm) := by
      filter_upwards [hmem] with y hy
      simp only [Function.comp_apply]
      rw [OpenPartialHomeomorph.trans_apply]
      have hw : ⇑L (f (⇑φ.symm (⇑I'.symm y))) = e.symm (f (⇑φ.symm (⇑I'.symm y))) := by
        apply e.injective
        rw [IsLocalHomeomorph.apply_localInverseAt_of_mem (hf := e.isLocalHomeomorph)
          (x := g (f z)) hy, e.apply_symm_apply]
      rw [hw]
    have hpt : (I ∘ (⇑(L ≫ₕ C) ∘ f ∘ ⇑φ.symm) ∘ ⇑I'.symm) (I' (⇑φ z))
        = (I ∘ (⇑C ∘ (fun y => e.symm (f y)) ∘ ⇑φ.symm) ∘ ⇑I'.symm) (I' (⇑φ z)) := by
      simp only [Function.comp_apply, ModelWithCorners.left_inv, φ.left_inv (mem_chart_source H' z),
        OpenPartialHomeomorph.trans_apply, hLz]
    constructor
    · intro h; exact h.congr_of_eventuallyEq hkey.symm hpt.symm
    · intro h; exact h.congr_of_eventuallyEq hkey hpt
  rw [ContMDiffWithinAt, ChartedSpace.liftPropWithinAt_iff', ContMDiffWithinAt,
    ChartedSpace.liftPropWithinAt_iff']
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨hcont.mp h1, (hprop h1).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨hcont.mpr h1, (hprop (hcont.mpr h1)).mpr h2⟩

end Work.Drive
