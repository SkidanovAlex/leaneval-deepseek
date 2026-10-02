import Mathlib
import Submission.Work.Cohomology.cohomology_prod_contractible
import Submission.Work.Cohomology.homologyContractible

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology

namespace Work.Cohomology

noncomputable section

/-- If `C` is contractible then the projection `C × X → X` is a homotopy equivalence, and hence
induces an isomorphism on singular homology with `ℤ` coefficients:
`Hₙ(C × X; ℤ) ≅ Hₙ(X; ℤ)`. -/
theorem homology_prod_contractible (C X : TopCat) [ContractibleSpace ↥C] (n : ℕ) :
    Nonempty ((Work.Cohomology.singularChains ℤ (TopCat.of (↥C × ↥X))).homology n ≅
      (Work.Cohomology.singularChains ℤ X).homology n) := by
  obtain ⟨e⟩ := homotopyEquiv_prod_fst ↥X ↥C
  have e' : ContinuousMap.HomotopyEquiv (↥C × ↥X) ↥X :=
    (Homeomorph.prodComm ↥C ↥X).toHomotopyEquiv.trans e
  let f : TopCat.of (↥C × ↥X) ⟶ X := TopCat.ofHom e'.toFun
  let g : X ⟶ TopCat.of (↥C × ↥X) := TopCat.ofHom e'.invFun
  have h1 : TopCat.Homotopy (f ≫ g) (𝟙 (TopCat.of (↥C × ↥X))) := e'.left_inv.some
  have h2 : TopCat.Homotopy (g ≫ f) (𝟙 X) := e'.right_inv.some
  haveI : IsIso (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of (↥C × ↥X)) X f) n) :=
    homologyEquiv ℤ (TopCat.of (↥C × ↥X)) X f g h1 h2 n
  exact ⟨CategoryTheory.asIso
    (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of (↥C × ↥X)) X f) n)⟩

end

end Work.Cohomology
