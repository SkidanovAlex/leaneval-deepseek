import Mathlib
import Submission.Work.ANALYTIC.Basic

namespace Work.ANALYTIC

open CategoryTheory Limits LightCondensed

/-- **A cochain complex all of whose terms are solid lifts to a complex of solid objects.**
Given `H : CochainComplex LightCondAb ℤ` with `isSolid (H.X q)` for every `q`, there is a complex
`M : CochainComplex Solid ℤ` whose degreewise inclusion is isomorphic to `H`.

Concretely take `M.X q := ⟨H.X q, hH q⟩` and `M.d i j := ObjectProperty.homMk (H.d i j)`, with
`shape`/`d_comp_d'` inherited from `H` via `ObjectProperty.hom_ext` (the inclusion of the full
subcategory is `rfl` on morphisms, so `ιC.obj M ≅ H` is `HomologicalComplex.Hom.isoOfComponents`
with identity components). -/
theorem solidComplexLift (H : CochainComplex LightCondAb ℤ)
    (hH : ∀ q : ℤ, LightCondensed.isSolid (H.X q)) :
    ∃ M : CochainComplex LightCondensed.Solid ℤ,
      Nonempty (Submission.Blueprint.ιC.obj M ≅ H) := by
  let M : CochainComplex LightCondensed.Solid ℤ :=
    { X := fun q => ⟨H.X q, hH q⟩
      d := fun i j => ObjectProperty.homMk (H.d i j)
      shape := fun i j hij => by
        refine ObjectProperty.hom_ext _ ?_
        rw [ObjectProperty.homMk_hom, H.shape i j hij]
        rfl
      d_comp_d' := fun i j k hij hjk => by
        refine ObjectProperty.hom_ext _ ?_
        simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom]
        rw [H.d_comp_d]
        rfl }
  refine ⟨M, ⟨?_⟩⟩
  dsimp only [M]
  exact HomologicalComplex.Hom.isoOfComponents (fun i => Iso.refl _)
    (fun i j hij => by simp)

end Work.ANALYTIC
