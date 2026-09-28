import Mathlib
import Submission.Work.Cohomology.pd_glue_defs
import Submission.Work.Thom.Cohomology
import Submission.Work.Cohomology.relComplex_empty_homology_iso

open CategoryTheory

namespace Work.Thom

/-- For the empty set the relative cohomology `H^k(B,∅)` of the pair `(B,∅)` agrees with the
absolute singular cohomology `H^k(B)`: the inclusion of the relative cochain complex
`relIncl ℤ B ∅ : C^*(B,∅) ⟶ C^*(B)` is an isomorphism of cochain complexes, hence induces an
isomorphism on homology. -/
theorem pdCoh_empty_iso (B : Type) [TopologicalSpace B] (k : ℕ) :
    Nonempty (Work.Cohomology.pdCoh (TopCat.of B) (∅ : Set B) k ≅ Work.Thom.Coh ℤ k B) := by
  have h : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relIncl ℤ (TopCat.of B) (∅ : Set B)) k) :=
    Work.Cohomology.relComplex_empty_homology_iso (TopCat.of B) k
  exact ⟨@asIso _ _ _ _ _ h⟩

end Work.Thom
