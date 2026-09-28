import Mathlib
import Submission.Work.Cohomology.RelCup
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Cohomology.dualZ
import Submission.Work.Cohomology.relComplexIsoDualZ
import Submission.Work.Cohomology.excisionDualZ

/-!
# Excision for singular cohomology

**Cohomological excision.**  For a topological space `X`, subsets `A, Z ⊆ X` with
`closure Z ⊆ interior A`, and any commutative ring `R`, the inclusion of pairs
`(X ∖ Z, A ∖ Z) ↪ (X, A)` induces an isomorphism

`H^n(X, A; R) ≅ H^n(X ∖ Z, A ∖ Z; R)`

on relative singular cohomology (`Work.Cohomology.relCohomology`, the cohomology of the relative
cochain complex `Work.Cohomology.relComplex`).

The proof decomposes into three statements.  Writing `V = X ∖ Z` and `A' = A ∩ V`:

* `Work.Cohomology.relComplexIsoDualZ` identifies the relative cochain complex `C^*(X,A;R)`
  (the kernel of the restriction `C^*(X;R) ⟶ C^*(A;R)`) with the `ℤ`-dual
  `Hom_ℤ(C_*(X,A), R)` of the relative `ℤ`-chain complex, and likewise for `(V, A')`;
* `Work.Cohomology.dualZ_excision` (`Submission/Work/Cohomology/excisionDualZ.lean`) proves the
  excision statement for these `ℤ`-duals, `H^n(Hom_ℤ(C_*(X,A), R)) ≅ H^n(Hom_ℤ(C_*(V,A'), R))`,
  by the five lemma applied to the small-chains model of the pair and the homotopy equivalence
  `smallToSing A V` (`Work.Cohomology.smallChainsHomotopyEquivInt`);
* the two identifications are then composed.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

theorem cohomologicalExcision (R : Type) [CommRing R] (X : TopCat) (A Z : Set X)
    (hZ : closure Z ⊆ interior A) (n : ℕ) :
    Nonempty (relCohomology R X A n ≅
      relCohomology R (TopCat.of {y : X | y ∉ Z})
        {y : {y : X | y ∉ Z} | (y : X) ∈ A} n) := by
  obtain ⟨e₁⟩ := relComplexIsoDualZ R X A
  obtain ⟨e₂⟩ := relComplexIsoDualZ R (TopCat.of {y : X | y ∉ Z})
    {y : {y : X | y ∉ Z} | (y : X) ∈ A}
  obtain ⟨e₃⟩ := dualZ_excision R X A Z hZ n
  exact ⟨(HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n).mapIso e₁
      ≪≫ e₃ ≪≫
    ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n).mapIso e₂).symm⟩

end

end Work.Cohomology
