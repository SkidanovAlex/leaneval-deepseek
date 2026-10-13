import Mathlib
import Submission.Work.DSEQ0.eulerCharDefs

universe u

namespace Work.DSEQ0

theorem isZero_homology_extend_of_pos (A : Type u) [CommRing A]
    (C : CochainComplex (ModuleCat.{u} A) ℕ)
    (h : ∀ n : ℕ, 0 < n → CategoryTheory.Limits.IsZero (C.homology n)) :
    ∀ i : ℤ, 0 < i →
      CategoryTheory.Limits.IsZero
        ((C.extend ComplexShape.embeddingUpNat).homology i) := by
  intro i hi
  -- `i > 0` lies in the image of the embedding `ℕ ↪ ℤ`.
  have hpos : 0 < i.toNat := by omega
  have hj : ComplexShape.embeddingUpNat.f i.toNat = i := by
    rw [ComplexShape.embeddingUpNat_f]
    exact Int.toNat_of_nonneg (le_of_lt hi)
  -- In degrees in the image of the embedding, extending does not change homology.
  exact CategoryTheory.Limits.IsZero.of_iso (h i.toNat hpos)
    (HomologicalComplex.extendHomologyIso C ComplexShape.embeddingUpNat hj)

end Work.DSEQ0
