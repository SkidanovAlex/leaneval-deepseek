import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `p`-torsion representations over `ℤ`, and the sub/quotient pair `pX ⊆ X`

Infrastructure for the proof of `Work.SSGRoute.PT.tensor_tateCohomology_acyclic`.  For a
representation `X` of `G` over `ℤ`, multiplication by `p` is the endomorphism `p • 𝟙 X` of `X`; its
abelian-category image and cokernel are the objects of the short exact sequence

`0 → pX → X → X/pX → 0`,

with `pSubRepIncl`, `pQuotRepProj` the two maps and `pCorestrict` the corestriction
`X → pX` of `p • 𝟙 X` (so that `pCorestrict p X ≫ pSubRepIncl p X = p • 𝟙 X`).

Everything is phrased with the abelian-category API rather than with `Submodule`s: this avoids the
`Rep.hV2` / `AddCommGroup.toIntModule` diamond on the carrier of a `Rep ℤ G`, and the statements
below mention no instances at all.
-/

namespace Work.CohomologicallyTrivial

open CategoryTheory

variable {G : Type} [Group G]

/-- A representation of `G` over `ℤ` is `p`-torsion if `p` kills every element. -/
def IsPTorsion (p : ℕ) (A : Rep.{0, 0, 0} ℤ G) : Prop := ∀ a : A.V, p • a = 0

/-- The image of `p • 𝟙 X`, i.e. the subrepresentation `pX`. -/
noncomputable def pSubRep (p : ℕ) (X : Rep.{0, 0, 0} ℤ G) : Rep.{0, 0, 0} ℤ G :=
  Abelian.image (p • 𝟙 X)

/-- The cokernel of `p • 𝟙 X`, i.e. the quotient `X/pX`. -/
noncomputable def pQuotRep (p : ℕ) (X : Rep.{0, 0, 0} ℤ G) : Rep.{0, 0, 0} ℤ G :=
  Limits.cokernel (p • 𝟙 X)

/-- The inclusion `pX → X`. -/
noncomputable def pSubRepIncl (p : ℕ) (X : Rep.{0, 0, 0} ℤ G) : pSubRep p X ⟶ X :=
  Abelian.image.ι (p • 𝟙 X)

/-- The projection `X → X/pX`. -/
noncomputable def pQuotRepProj (p : ℕ) (X : Rep.{0, 0, 0} ℤ G) : X ⟶ pQuotRep p X :=
  Limits.cokernel.π (p • 𝟙 X)

/-- The corestriction `X → pX` of `p • 𝟙 X`. -/
noncomputable def pCorestrict (p : ℕ) (X : Rep.{0, 0, 0} ℤ G) : X ⟶ pSubRep p X :=
  Abelian.factorThruImage (p • 𝟙 X)

/-- The corestriction is a corestriction: `X → pX → X` is `p • 𝟙 X`. -/
theorem pCorestrict_comp_pSubRepIncl (p : ℕ) (X : Rep.{0, 0, 0} ℤ G) :
    pCorestrict p X ≫ pSubRepIncl p X = p • 𝟙 X :=
  Abelian.image.fac (p • 𝟙 X)

/-- The short complex `0 → pX → X → X/pX → 0`. -/
noncomputable def pShortComplex (p : ℕ) (X : Rep.{0, 0, 0} ℤ G) :
    ShortComplex (Rep.{0, 0, 0} ℤ G) :=
  ShortComplex.mk (pSubRepIncl p X) (pQuotRepProj p X)
    (Abelian.image_ι_comp_eq_zero (Limits.cokernel.condition (p • 𝟙 X)))

end Work.CohomologicallyTrivial
