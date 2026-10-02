import Mathlib
import Submission.Work.Cohomology.homotopyInvariance
import Submission.Work.Cohomology.punit
import Submission.Work.Cohomology.homotopyEquiv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The positive-degree singular cohomology of a contractible space

A contractible space `X` is homotopy equivalent to the one-point space (Mathlib's
`ContractibleSpace.hequiv` witnesses `X ≃ₕ PUnit`).  Homotopy equivalences induce isomorphisms on
singular cohomology (`Work.Cohomology.homotopyEquiv`), so

  `Hⁿ⁺¹(X; R) ≅ Hⁿ⁺¹(PUnit; R)`,

and the latter vanishes in positive degrees (`Work.Cohomology.punit`).  Since the zero object is
characterised up to isomorphism, `Hⁿ⁺¹(X; R)` is a zero object as well.
-/

set_option linter.style.haveILetI false

open CategoryTheory

namespace Work.Cohomology

noncomputable section

/-- The positive-degree singular cohomology of a contractible space vanishes. -/
theorem contractible (R : Type) [CommRing R] (X : TopCat) [ContractibleSpace X] (n : ℕ) :
    CategoryTheory.Limits.IsZero (Work.Cohomology.singularCohomology R (n + 1) X) := by
  -- `X` is homotopy equivalent to (the one-point space) `PUnit`
  obtain ⟨e⟩ := ContractibleSpace.hequiv X PUnit
  let f : X ⟶ TopCat.of PUnit := TopCat.ofHom e.toFun
  let g : TopCat.of PUnit ⟶ X := TopCat.ofHom e.invFun
  have h1 : TopCat.Homotopy (f ≫ g) (𝟙 X) := e.left_inv.some
  have h2 : TopCat.Homotopy (g ≫ f) (𝟙 (TopCat.of PUnit)) := e.right_inv.some
  -- so the pullback `Hⁿ⁺¹(PUnit; R) ⟶ Hⁿ⁺¹(X; R)` is an isomorphism
  haveI : CategoryTheory.IsIso (singularCohomologyMap R X (TopCat.of PUnit) f (n + 1)) :=
    homotopyEquiv R X (TopCat.of PUnit) f g h1 h2 (n + 1)
  -- and `Hⁿ⁺¹(PUnit; R)` is a zero object
  exact CategoryTheory.Limits.IsZero.of_iso (punit R n)
    (CategoryTheory.asIso (singularCohomologyMap R X (TopCat.of PUnit) f (n + 1))).symm

end

end Work.Cohomology
