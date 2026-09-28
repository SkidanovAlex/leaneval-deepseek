import Mathlib
import Submission.Work.Cohomology.wsfDefs

/-!
# Vanishing of `H^{j+1}(U, U∩A)` in terms of cycles and boundaries

For the relative cochain complex `rcSet A U = C^*(U, U ∩ A)` of the pair `(U, U ∩ A)`,
the `(j+1)`-st cohomology is a subsingleton (i.e. vanishes) exactly when every relative
`(j+1)`-cocycle is a coboundary, i.e. lies in the image of the differential
`rcDiff A U j : C^j(U, U∩A) → C^{j+1}(U, U∩A)`.

This is the elementwise description of the homology of a cochain complex of modules:
`H^{j+1} = ker (d^{j+1}) / im (d^j)`, so `H^{j+1}` vanishes iff `im (d^j) = ker (d^{j+1})`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace Work.Cohomology

theorem rcSet_homology_succ_subsingleton_iff {X : Type} [TopologicalSpace X] (A : Set X) (U : Set X) (j : ℕ) :
    Subsingleton ((rcSet A U).homology (j+1)) ↔
      (∀ z : ↥(rcKern A U (j+1)), rcDiff A U (j+1) z = 0 →
        ∃ w : ↥(rcKern A U j), rcDiff A U j w = z) := by
  -- `Subsingleton` of a module is `IsZero`, i.e. exactness of the complex at `j+1`.
  rw [← ModuleCat.isZero_iff_subsingleton, ← HomologicalComplex.exactAt_iff_isZero_homology]
  -- Identify `ExactAt (j+1)` with the exactness of the short complex
  -- `C^j ⟶ C^{j+1} ⟶ C^{j+2}`.
  rw [HomologicalComplex.exactAt_iff' (rcSet A U) j (j+1) (j+2)
    (ComplexShape.prev_eq' _ (show (ComplexShape.up ℕ).Rel j (j+1) from rfl))
    (ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel (j+1) (j+2) from by
      simp [ComplexShape.up, ComplexShape.up']))]
  -- Exactness of a short complex of modules, elementwise.
  rw [CategoryTheory.ShortComplex.moduleCat_exact_iff]
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', rcSet_d]
  simp only [ModuleCat.hom_ofHom, relComplex, relKern, rcSet, rcKern]

end Work.Cohomology
