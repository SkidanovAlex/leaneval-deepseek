import Mathlib
import Submission.Work.Cohomology.Singular
import Submission.Work.Cohomology.homotopyEquiv
import Submission.Work.Cohomology.homotopyEquiv_prod_fst

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicTopology

namespace Work.Cohomology

noncomputable section

/-- If `C` is contractible then the projection `C × X → X` is a homotopy equivalence, and hence
induces an isomorphism on singular cohomology with coefficients in any commutative ring `R`:
`Hⁿ(C × X; R) ≅ Hⁿ(X; R)`. -/
theorem cohomology_prod_contractible (R : Type) [CommRing R] (C X : TopCat)
    [ContractibleSpace ↥C] (n : ℕ) :
    Nonempty (Work.Cohomology.singularCohomology R n (TopCat.of (↥C × ↥X)) ≅
      Work.Cohomology.singularCohomology R n X) := by
  obtain ⟨e⟩ := homotopyEquiv_prod_fst ↥X ↥C
  have e' : ContinuousMap.HomotopyEquiv (↥C × ↥X) ↥X :=
    (Homeomorph.prodComm ↥C ↥X).toHomotopyEquiv.trans e
  let f : TopCat.of (↥C × ↥X) ⟶ X := TopCat.ofHom e'.toFun
  let g : X ⟶ TopCat.of (↥C × ↥X) := TopCat.ofHom e'.invFun
  have h1 : TopCat.Homotopy (f ≫ g) (𝟙 (TopCat.of (↥C × ↥X))) := e'.left_inv.some
  have h2 : TopCat.Homotopy (g ≫ f) (𝟙 X) := e'.right_inv.some
  haveI := homotopyEquiv R (TopCat.of (↥C × ↥X)) X f g h1 h2 n
  exact ⟨(CategoryTheory.asIso (singularCohomologyMap R (TopCat.of (↥C × ↥X)) X f n)).symm⟩

end

end Work.Cohomology
