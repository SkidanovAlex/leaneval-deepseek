import Mathlib
import Submission.Work.DSEQ0.CurrySpecResolution

namespace Work.DSEQ0

universe u

theorem isZero_homology_cech_of_cechZ (R : Type u) [CommRing R] {ι : Type u} [Finite ι]
    (U : ι → (AlgebraicGeometry.Spec (CommRingCat.of R)).Opens)
    (h : ∀ i : ℤ, 0 < i → CategoryTheory.Limits.IsZero
      ((DSMap.cechZ R (AlgebraicGeometry.Spec (CommRingCat.of R))
        (CategoryTheory.CategoryStruct.id _) U).homology i)) :
    ∀ n : ℕ, 0 < n → CategoryTheory.Limits.IsZero
      ((DSMap.cech R (AlgebraicGeometry.Spec (CommRingCat.of R))
        (CategoryTheory.CategoryStruct.id _) U).homology n) := by
  intro n hn
  -- `cechZ` is `cech`, extended to `ℤ`-degrees by zero in negative degrees; in nonnegative
  -- degrees (`(n : ℤ)` with `n : ℕ`) this extension does not change homology.
  have hj : ComplexShape.embeddingUpNat.f n = (n : ℤ) := rfl
  exact ((HomologicalComplex.extendHomologyIso
      (DSMap.cech R (AlgebraicGeometry.Spec (CommRingCat.of R))
        (CategoryTheory.CategoryStruct.id _) U)
      ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) hj).isZero_iff).mp
    (h (n : ℤ) (by exact_mod_cast hn))

end Work.DSEQ0
