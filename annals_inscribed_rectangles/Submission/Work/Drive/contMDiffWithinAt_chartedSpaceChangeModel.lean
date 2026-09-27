import Mathlib
import Submission.Work.Drive.chartedSpaceChangeModel

/-!
# Smoothness is invariant under the model change `chartedSpaceChangeModel`

`Work.Drive.chartedSpaceChangeModel φ` pushes the atlas of a charted space `M` over `E` forward
along a homeomorphism `φ : E ≃ₜ E'` of model spaces, producing a charted space over `E'` whose
preferred chart at `x` is `(chartAt E x).trans φ.toOpenPartialHomeomorph`.

The main result of this file, `Work.Drive.contMDiffWithinAt_chartedSpaceChangeModel`, says that when
`φ` is a `C^n` homeomorphism with `C^n` inverse, the notion of being `C^n` within a set at a point
for a map `f : Z → M` is the same in the pushed-forward structure as in the original one.  The proof
is a direct unfolding: in both structures `ContMDiffWithinAt` is a conjunction of
`ContinuousWithinAt f s z` (which does not involve the target structure) and a `ContDiffWithinAt`
condition, and the two versions of the latter differ exactly by left composition with `φ`.
-/

namespace Work.Drive

open Manifold Function Set
open scoped Manifold ContDiff

/-- Composing on the left with a global `C^n` homeomorphism `φ` (with `C^n` inverse) does not
change `C^n`-regularity within a set at a point. -/
theorem contDiffWithinAt_comp_homeomorph_iff
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    (φ : E ≃ₜ E') {n : WithTop ℕ∞}
    (hφ : ContDiff 𝕜 n (φ : E → E')) (hφ' : ContDiff 𝕜 n (φ.symm : E' → E))
    {F : E' → E} {T : Set E'} {p : E'} :
    ContDiffWithinAt 𝕜 n (⇑φ ∘ F) T p ↔ ContDiffWithinAt 𝕜 n F T p := by
  constructor
  · intro h
    have h1 : ContDiffWithinAt 𝕜 n (φ.symm : E' → E) univ (φ (F p)) :=
      hφ'.contDiffAt.contDiffWithinAt
    have h2 := h1.comp p h (Set.mapsTo_univ _ _)
    refine h2.congr (fun y _ => ?_) ?_
    · simp only [Function.comp_apply, Homeomorph.symm_apply_apply]
    · simp only [Function.comp_apply, Homeomorph.symm_apply_apply]
  · intro h
    have h1 : ContDiffWithinAt 𝕜 n (φ : E → E') univ (F p) := hφ.contDiffAt.contDiffWithinAt
    exact h1.comp p h (Set.mapsTo_univ _ _)

/-- The preferred chart of `M` in the pushed-forward structure is the old preferred chart followed
by `φ`. -/
theorem chartAt_chartedSpaceChangeModel
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    (φ : E ≃ₜ E') (y : M) :
    (⇑(@chartAt E' _ M _ (chartedSpaceChangeModel (𝕜 := 𝕜) (M := M) φ) y) : M → E') =
      ⇑φ ∘ ⇑(chartAt E y) := by
  show (↑((chartAt E y).trans φ.toOpenPartialHomeomorph) : M → E') = ⇑φ ∘ ⇑(chartAt E y)
  rfl

set_option linter.style.haveILetI false in
theorem contMDiffWithinAt_chartedSpaceChangeModel
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] (I : ModelWithCorners 𝕜 E' H')
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    (φ : E ≃ₜ E') {n : WithTop ℕ∞}
    (hφ : ContDiff 𝕜 n (φ : E → E')) (hφ' : ContDiff 𝕜 n (φ.symm : E' → E))
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace H' Z]
    (f : Z → M) (s : Set Z) (z : Z) :
    @ContMDiffWithinAt 𝕜 _ E' _ _ H' _ I Z _ _ E' _ _ E' _ (modelWithCornersSelf 𝕜 E') M _
        (Work.Drive.chartedSpaceChangeModel (𝕜 := 𝕜) (M := M) φ) n f s z ↔
      ContMDiffWithinAt I (modelWithCornersSelf 𝕜 E) n f s z := by
  letI : ChartedSpace E' M := Work.Drive.chartedSpaceChangeModel (𝕜 := 𝕜) (M := M) φ
  change ContMDiffWithinAt I (modelWithCornersSelf 𝕜 E') n f s z ↔
      ContMDiffWithinAt I (modelWithCornersSelf 𝕜 E) n f s z
  have hchart : ∀ y : M, (⇑(chartAt E' y) : M → E') = ⇑φ ∘ ⇑(chartAt E y) :=
    chartAt_chartedSpaceChangeModel φ
  constructor
  · intro h
    refine ⟨h.continuousWithinAt, ?_⟩
    have hh := h.prop
    rw [contDiffWithinAtProp_self_target] at hh
    rw [contDiffWithinAtProp_self_target]
    have key : (↑(chartAt E' (f z)) ∘ f ∘ ↑(chartAt H' z).symm) ∘ I.symm
        = ⇑φ ∘ ((↑(chartAt E (f z)) ∘ f ∘ ↑(chartAt H' z).symm) ∘ I.symm) := by
      rw [hchart (f z)]
      simp only [Function.comp_assoc]
    rw [key] at hh
    exact (contDiffWithinAt_comp_homeomorph_iff φ hφ hφ').mp hh
  · intro h
    refine ⟨h.continuousWithinAt, ?_⟩
    have hh := h.prop
    rw [contDiffWithinAtProp_self_target] at hh
    rw [contDiffWithinAtProp_self_target]
    have key : (↑(chartAt E' (f z)) ∘ f ∘ ↑(chartAt H' z).symm) ∘ I.symm
        = ⇑φ ∘ ((↑(chartAt E (f z)) ∘ f ∘ ↑(chartAt H' z).symm) ∘ I.symm) := by
      rw [hchart (f z)]
      simp only [Function.comp_assoc]
    rw [key]
    exact (contDiffWithinAt_comp_homeomorph_iff φ hφ hφ').mpr hh

end Work.Drive
