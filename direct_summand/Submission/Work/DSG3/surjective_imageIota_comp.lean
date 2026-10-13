import Mathlib
import Submission.Work.DSG3.Basic

namespace Work.DSG3

open CategoryTheory AlgebraicGeometry in
lemma surjective_imageIota_comp (A : Type*) [CommRing A] [IsDomain A] (X : AlgebraicGeometry.Scheme)
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) [AlgebraicGeometry.IsProper f] (x : X)
    (hx : f x = DSMap.genericPointOfSpec A) :
    Function.Surjective ((X.fromSpecResidueField x).imageι ≫ f) := by
  -- `f` is proper, hence (universally) closed; and its underlying map is continuous.
  intro y
  have hclosed : IsClosedMap f := Scheme.Hom.isClosedMap f
  have hcont : Continuous f := Scheme.Hom.continuous f
  -- The generic point of `Spec A` is the image of `x`, so `f` maps the closure of `{x}`
  -- onto the closure of `{f x}`, which is all of `Spec A`.
  have h1 : f '' closure ({x} : Set X) = ⊤ := by
    rw [← IsClosedMap.closure_image_eq_of_continuous hclosed hcont ({x} : Set X)]
    rw [Set.image_singleton, hx, DSMap.closure_singleton_genericPointOfSpec]
  -- `y` therefore has a preimage `w` inside the closure of `{x}`.
  have hy : y ∈ f '' closure ({x} : Set X) := by rw [h1]; trivial
  obtain ⟨w, hw, hwy⟩ := hy
  -- The scheme-theoretic image of `Spec κ(x) → X` is exactly `closure {x}`,
  -- so `w` lifts to a point `z` of that image.
  rw [← DSMap.range_imageι_fromSpecResidueField x] at hw
  obtain ⟨z, hz⟩ := hw
  exact ⟨z, by rw [Scheme.Hom.comp_apply, hz]; exact hwy⟩

end Work.DSG3
