import Mathlib
import Submission.Work.DSG4a.BaseChange

namespace Work.DSG4a

open CategoryTheory AlgebraicGeometry Limits
universe u
-- `baseChangeOpen X f W = (baseChangeFst X f) ⁻¹ᵁ W`. Reviewer advice: this is one line from
-- Mathlib's `Scheme.Hom.iSup_preimage_eq_top` (Mathlib/AlgebraicGeometry/Scheme.lean), or
-- `← Scheme.Hom.preimage_iSup` with `hcov` and `Scheme.Hom.preimage_top`.
theorem iSup_baseChangeOpen {A : Type u} [CommRing A] {A' : Type u} [CommRing A']
    [Algebra A A'] (X : AlgebraicGeometry.Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    {ι : Type u} (U : ι → X.Opens) (hcov : ⨆ i, U i = ⊤) :
    (⨆ i, Work.DSG4a.baseChangeOpen (A := A) (A' := A') X f (U i)) = ⊤ := by
  simp only [Work.DSG4a.baseChangeOpen]
  rw [← Scheme.Hom.preimage_iSup, hcov, Scheme.Hom.preimage_top]

end Work.DSG4a
