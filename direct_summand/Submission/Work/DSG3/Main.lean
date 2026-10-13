import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSG3.Basic
import Submission.Work.DSG3.exists_mem_closure_eq_singleton
import Submission.Work.DSG3.isIntegral_image_fromSpecResidueField
import Submission.Work.DSG3.surjective_imageIota_comp
import Submission.Work.DSG3.isGenFinite_imageIota_comp

/-!
# DSG3 — the multisection reduction (area G3 of the `direct_summand` proof map), proved

This is the deliverable of subproject DSG3: a proof of the frozen statement
`DSMap.area_G3_multisection` (in `Submission/Work/DSMap/Map.lean`), named
`DSMap.area_G3_multisection_proved`.

## The argument

Let `A` be a local Noetherian domain, `η = genericPointOfSpec A` the generic point of `Spec A`
(the point defined by the zero ideal), `f : X ⟶ Spec A` proper and surjective with `X ⊆ ℙᴺ_A`
closed (`IsProjOver`).

1. `X` is a Noetherian topological space (`IsNoetherian` follows from `LocallyOfFiniteType` and
   properness); the topological lemma `Work.DSG3.exists_mem_closure_eq_singleton` produces a point
   `z ∈ f ⁻¹' {η}` which is minimal for specialisation inside the generic fibre:
   `closure {z} ∩ f ⁻¹' {η} = {z}`.
2. Let `Z := (X.fromSpecResidueField z).image` and `ι : Z ⟶ X` its closed immersion into `X`
   (the scheme-theoretic image of the canonical map `Spec κ(z) ⟶ X`). Then `Z` is integral
   (`Work.DSG3.isIntegral_image_fromSpecResidueField`), `ι ≫ f` is proper (closed immersion
   after a proper map), surjective (`Work.DSG3.surjective_imageIota_comp`, using that its image is
   closed and contains `η = f z`, whose closure is everything), and generically finite
   (`Work.DSG3.isGenFinite_imageIota_comp`, using that the fibre of `ι ≫ f` over `η` is `{z}`,
   hence finite, so Zariski's main theorem makes it finite over an open neighbourhood of `η`).
   Finally `IsProjOver A (ι ≫ f)` is inherited from `IsProjOver A f` by composing the given
   closed immersion `X ⟶ ℙᴺ_A` with `ι`.
-/

open CategoryTheory AlgebraicGeometry

namespace DSMap

/-- **Area G3, proved**: over a local Noetherian domain, a proper surjective projective `X` admits
a closed integral subscheme `Z` which is still surjective and projective over `Spec A` and
generically finite over `Spec A`. -/
theorem area_G3_multisection_proved.{a} (A : Type a) [CommRing A] [IsLocalRing A] [IsDomain A]
    [IsNoetherianRing A] (X : Scheme.{a}) (f : X ⟶ Spec (.of A)) [IsProper f]
    (hs : Function.Surjective f) (hp : IsProjOver A f) :
    ∃ (Z : Scheme.{a}) (ι : Z ⟶ X), IsClosedImmersion ι ∧ IsIntegral Z ∧
      Function.Surjective (ι ≫ f) ∧ IsProper (ι ≫ f) ∧ IsGenFinite A (ι ≫ f) ∧
      IsProjOver A (ι ≫ f) := by
  -- X is a Noetherian topological space
  have hnoeth : TopologicalSpace.NoetherianSpace ↥X := by
    have h2 : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    have hcomp : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : IsNoetherian X := AlgebraicGeometry.IsNoetherian.mk
    infer_instance
  haveI := hnoeth
  -- a point of the generic fibre, minimal for specialisation inside it
  obtain ⟨x, hx⟩ := hs (genericPointOfSpec A)
  obtain ⟨z, hzS, hzmin⟩ :=
    Work.DSG3.exists_mem_closure_eq_singleton (f ⁻¹' {genericPointOfSpec A}) ⟨x, hx⟩
  have hzη : f z = genericPointOfSpec A := hzS
  obtain ⟨N, i, hi, hif⟩ := hp
  exact ⟨(X.fromSpecResidueField z).image, (X.fromSpecResidueField z).imageι,
    inferInstance, Work.DSG3.isIntegral_image_fromSpecResidueField z,
    Work.DSG3.surjective_imageIota_comp A X f z hzη, inferInstance,
    Work.DSG3.isGenFinite_imageIota_comp A X f z hzη hzmin,
    ⟨N, (X.fromSpecResidueField z).imageι ≫ i, inferInstance, by rw [Category.assoc, hif]⟩⟩

end DSMap
