import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.CoCore.FundamentalClass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The reciprocity isomorphism from the class-formation axioms

This file proves **Artin's reciprocity law** for a finite Galois extension `L/K` of number fields
from the class-formation axioms (`NK.GlobalCFT.CohomologicalFieldAxiom K L`) and the `H⁰`-computation
(`NK.GlobalCFT.globalCFT_H0Computation`, unconditional).

The isomorphism produced is the canonical one: it is the composite

  `C_K ⧸ N_{L/K}C_L ≅ Ĥ⁰(G, C_L) ≅ Ĥ⁻²(G, ℤ) ≅ Gᵃᵇ`,

where the first map is the `H⁰`-computation (Milne, *CFT*, Lemma 4.1, proved on disk), the second
is **Tate's theorem** (cup product with the fundamental class, in the isomorphism form
`Commons.NumberTheory.NumberField.Completion.ArtinMap.addEquiv_tateCohomology_of_fundamental_class`),
and the third is the canonical identification `Ĥ⁻²(G, ℤ) ≅ Gᵃᵇ`
(`Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_two_iso_abelianization`).

For a commutative `Gal(L/K)` this is `ArtinReciprocity K L` of the delivered chapter, i.e. the
isomorphism `C_K ⧸ N_{L/K}C_L ≅ Gal(L/K)` whose kernel properties are the reciprocity law.

## Status

The reciprocity law is therefore *proved* for every finite Galois extension for which the
class-formation axioms are available; by `CoCore/FundamentalClass.lean` this includes every
extension from the two inputs `HerbrandQuotient` and `SecondInequality` together with Milne's
reduction 5.3–5.4, and it is unconditional in the cyclic prime-degree case.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- **The reciprocity isomorphism `C_K ⧸ N_{L/K}C_L ≅ Gᵃᵇ`** from the class-formation axioms: the
canonical composite of the `H⁰`-computation, Tate's theorem for the fundamental class, and the
identification `Ĥ⁻²(G, ℤ) ≅ Gᵃᵇ`. -/
def galoisReciprocity_of_cohomologicalFieldAxiom [IsGalois K L] (h : CohomologicalFieldAxiom K L)
    [Group.IsSolvable (L ≃ₐ[K] L)] : GaloisReciprocity K L where
  iso := by
    let α := Classical.choose h.fundamentalClass
    have hα : addOrderOf α = Nat.card (L ≃ₐ[K] L) := Classical.choose_spec h.fundamentalClass
    let e0 := Classical.choice (globalCFT_H0Computation (K := K) (L := L)).quotientEquiv
    let e1 := Classical.choice
      (Commons.RepresentationTheory.TateCohomology.tateCohomology_zero_iso
        (IdeleClassGroup.rep K L).ρ)
    let e2 := Classical.choice
      (Commons.NumberTheory.NumberField.Completion.ArtinMap.addEquiv_tateCohomology_of_fundamental_class
        (IdeleClassGroup.rep K L) h.h1_trivial h.h2_card α hα)
    let e3 := Classical.choice
      (Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_two_iso_abelianization
        (L ≃ₐ[K] L))
    exact e0.trans ((AddEquiv.toMultiplicative e1.toAddEquiv).symm.trans
      ((AddEquiv.toMultiplicative e2).symm.trans
        ((AddEquiv.toMultiplicative e3).trans (MulEquiv.refl _))))

/-- **Artin's reciprocity law** for a finite **abelian** extension, from the class-formation
axioms: the canonical isomorphism `C_K ⧸ N_{L/K}C_L ≅ Gal(L/K)`. -/
def artinReciprocity_of_cohomologicalFieldAxiom [IsGalois K L] (h : CohomologicalFieldAxiom K L)
    [IsMulCommutative (L ≃ₐ[K] L)] : ArtinReciprocity K L := by
  letI : CommGroup (L ≃ₐ[K] L) := IsMulCommutative.instCommGroup
  haveI : Group.IsSolvable (L ≃ₐ[K] L) := inferInstance
  exact (galoisReciprocity_of_cohomologicalFieldAxiom h).toArtinReciprocity

/-- **Reciprocity for every finite Galois extension**, from the cyclic prime-degree case and
Milne's reduction 5.3–5.4, together with the two chapter inputs. -/
def galoisReciprocity_of_inputs (hred : CyclicPrimeReduction)
    (hH : ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
      [Fact (Nat.Prime (Nat.card (L ≃ₐ[K] L)))], HerbrandQuotient K L)
    (h2 : SecondInequality) [IsGalois K L] [Group.IsSolvable (L ≃ₐ[K] L)] :
    GaloisReciprocity K L :=
  galoisReciprocity_of_cohomologicalFieldAxiom (cohomologicalFieldAxiom_of_inputs hred hH h2)

/-- **Artin reciprocity for every finite abelian extension**, from the cyclic prime-degree case,
Milne's reduction 5.3–5.4, the Herbrand-quotient computation and the second inequality. -/
def artinReciprocity_of_inputs (hred : CyclicPrimeReduction)
    (hH : ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
      [Fact (Nat.Prime (Nat.card (L ≃ₐ[K] L)))], HerbrandQuotient K L)
    (h2 : SecondInequality) [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] :
    ArtinReciprocity K L :=
  artinReciprocity_of_cohomologicalFieldAxiom (cohomologicalFieldAxiom_of_inputs hred hH h2)

end NK.GlobalCFTdeep
