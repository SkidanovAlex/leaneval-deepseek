import Mathlib
import Submission.Work.DSEQ0.CechImageModel

/-!
# Vanishing of the Čech homology of the empty cover

If the index type `ι` of the cover `U : ι → X.Opens` is empty, then in every degree `n` the
Čech complex is the product, over all maps `Fin (n + 1) → ι`, of the presheaf values; that
index type is empty, so every term of the complex is an empty product, hence a terminal — hence
zero — object of `ModuleCat A`.  Consequently the homology vanishes in every degree.
-/

open CategoryTheory Limits Opposite

universe a

namespace Work.DSEQ0

theorem cech_homology_isZero_of_isEmpty {A : Type a} [CommRing A] {X : AlgebraicGeometry.Scheme.{a}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) {ι : Type a} [Finite ι] [IsEmpty ι]
    (U : ι → X.Opens) (n : ℕ) :
    CategoryTheory.Limits.IsZero ((DSMap.cech A X f U).homology n) := by
  rw [HomologicalComplex.homology]
  apply CategoryTheory.ShortComplex.isZero_homology_of_isZero_X₂
  show CategoryTheory.Limits.IsZero ((DSMap.cech A X f U).X n)
  rw [DSMap.cech, CategoryTheory.cechComplexFunctor,
    CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor_obj_X]
  change CategoryTheory.Limits.IsZero
    (∏ᶜ (fun i : Fin (n + 1) → ι =>
      (DSMap.cechPresheaf A X f).obj (op (∏ᶜ (fun a : Fin (n + 1) => U (i a))))))
  exact CategoryTheory.Limits.IsZero.of_iso (ModuleCat.isZero_of_subsingleton _) (ModuleCat.piIsoPi _)

end Work.DSEQ0
