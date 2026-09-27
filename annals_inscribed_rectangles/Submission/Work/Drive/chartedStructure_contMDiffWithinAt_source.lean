import Mathlib

namespace Work.Drive

open Manifold in
open scoped Manifold ContDiff in
/-- **Smoothness is transported by a homeomorphism-transported `ChartedSpace`, on the source side.**
This is the source-side counterpart of `Work.Drive.chartedStructure_contMDiffWithinAt`
(`Submission/Work/Drive/chartedStructure_contMDiffWithinAt.lean`), which handles the target side.

If `e : M ≃ₜ M'` is a homeomorphism and `M'` is given the `ChartedSpace` structure pushed forward
from `M` along `e` (`Homeomorph.chartedSpace e`), then a map `f : M' → Z` is `C^n` within `s` at `z`
for that structure exactly when `f ∘ e` is `C^n` within `e ⁻¹' s` at `e.symm z` for the original
structure on `M`.

Together with the target-side statement this says that `e` is a diffeomorphism between `M` (original
structure) and `M'` (pushed-forward structure), which is what lets a concrete map on a space with a
transported smooth structure be checked in the model. -/
theorem chartedStructure_contMDiffWithinAt_source
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H')
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {M' : Type*} [TopologicalSpace M'] (e : M ≃ₜ M')
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace H' Z]
    {n : WithTop ℕ∞} (f : M' → Z) (s : Set M') (z : M') :
    @ContMDiffWithinAt 𝕜 _ E _ _ H _ I M' _ (Homeomorph.chartedSpace e) E' _ _ H' _ I' Z _ _ n f s z ↔
      ContMDiffWithinAt I I' n (fun y : M => f (e y)) (e ⁻¹' s) (e.symm z) := by
  let : ChartedSpace H M' := Homeomorph.chartedSpace e
  -- `Homeomorph.chartedSpace e` uses an arbitrary right inverse `g` of `e`; on the relevant
  -- point it agrees with `e.symm`.
  let g : M' → M := (Function.Surjective.hasRightInverse e.surjective).choose
  have hg : Function.RightInverse g ⇑e :=
    (Function.Surjective.hasRightInverse e.surjective).choose_spec
  have hgq : g z = e.symm z := e.injective (by rw [hg z, e.apply_symm_apply])
  -- The preferred chart of the pushed-forward structure at `z`, and the chart of `M` at the
  -- point `e.symm z` it reduces to.
  let L : OpenPartialHomeomorph M' M := e.isLocalHomeomorph.localInverseAt (g z)
  let C : OpenPartialHomeomorph M H := chartAt H (e.symm z)
  have hCeq : (chartAt H (g z) : OpenPartialHomeomorph M H) = chartAt H (e.symm z) := by
    rw [hgq]
  have hchart : (chartAt H z : OpenPartialHomeomorph M' H) = L ≫ₕ C := by
    change (e.isLocalHomeomorph.localInverseAt (g z)) ≫ₕ (chartAt H (g z)) = _
    rw [hCeq]
  have hmemz : z ∈ L.source := by
    have := IsLocalHomeomorph.apply_self_mem_localInverseAt_source e.isLocalHomeomorph (x := g z)
    simpa [L, hg z] using this
  have hLz : L z = e.symm z := by
    apply e.injective
    rw [IsLocalHomeomorph.apply_localInverseAt_of_mem (hf := e.isLocalHomeomorph) (x := g z) hmemz,
      e.apply_symm_apply]
  -- The three ingredients of the chart change: the inverse chart of the pushed structure is
  -- `e ∘ (chartAt H (e.symm z)).symm`, the pushed chart sends `z` to the same point of `H` as the
  -- original chart sends `e.symm z`, and the two sets are the same.
  let χ : H → M' := (chartAt H z).symm
  let η : H → M := C.symm
  let ψ : Z → H' := chartAt H' (f z)
  have hsymm : χ = fun y => e (η y) := by
    have h' : (⇑(chartAt H z).symm : H → M') = fun y => e (C.symm y) := by
      rw [hchart, OpenPartialHomeomorph.coe_trans_symm]
      funext y
      simp [L, IsLocalHomeomorph.localInverseAt_symm]
    exact h'
  have hpt : (chartAt H z) z = C (e.symm z) := by
    rw [hchart, OpenPartialHomeomorph.trans_apply, hLz]
  have hset : χ ⁻¹' s = η ⁻¹' (e ⁻¹' s) := by
    rw [hsymm]
    rfl
  have hfun : ψ ∘ f ∘ χ = ψ ∘ (f ∘ ⇑e) ∘ η := by
    funext y
    simp only [Function.comp_apply]
    rw [congrFun hsymm y]
  have hprop : ContDiffWithinAtProp I I' n (ψ ∘ f ∘ χ) (χ ⁻¹' s) ((chartAt H z) z) ↔
      ContDiffWithinAtProp I I' n (ψ ∘ (f ∘ ⇑e) ∘ η) (η ⁻¹' (e ⁻¹' s)) (C (e.symm z)) := by
    rw [hfun, hpt, hset]
  have hcont : ContinuousWithinAt f s z ↔
      ContinuousWithinAt (fun y : M => f (e y)) (e ⁻¹' s) (e.symm z) := by
    constructor
    · intro h
      have h' : ContinuousWithinAt (fun y : M' => f y) s (⇑e (e.symm z)) := by
        simpa using h
      exact h'.comp e.continuous.continuousWithinAt (fun y hy => hy)
    · intro h
      have h' : ContinuousWithinAt ((fun y : M => f (e y)) ∘ ⇑e.symm) s z :=
        h.comp e.symm.continuous.continuousWithinAt (fun y hy => by simpa using hy)
      simpa [Function.comp_def] using h'
  rw [ContMDiffWithinAt, ChartedSpace.liftPropWithinAt_iff', ContMDiffWithinAt,
    ChartedSpace.liftPropWithinAt_iff']
  simp only [Homeomorph.apply_symm_apply]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨hcont.mp h1, hprop.mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨hcont.mpr h1, hprop.mpr h2⟩

end Work.Drive
