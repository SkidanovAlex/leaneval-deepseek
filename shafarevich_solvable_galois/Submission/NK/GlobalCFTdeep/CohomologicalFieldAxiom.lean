/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFTdeep.SecondInequality.FundamentalClass
import Submission.NK.GlobalCFTdeep.H1All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The class-formation axioms from Hasse's fundamental class alone

`NK.GlobalCFT.CohomologicalFieldAxiom K L` has three fields:

* `h1_trivial` — `H¹(H, C_L) = 0` for every subgroup `H ≤ Gal(L/K)`;
* `h2_card` — `|H²(H, C_L)| = |H|` for every subgroup `H`;
* `fundamentalClass` — an element of `H²(Gal(L/K), C_L)` of order `[L:K]`.

The first is now **proved unconditionally** in this chapter
(`NK.GlobalCFTdeep.subsingleton_groupCohomology_one_res_ideleClassGroup`, Milne's Theorem
5.1(b); see `H1All.lean`), so the axioms follow from **Hasse's fundamental class alone** — the
Brauer-group content `H²(Gal(L/K), C_L) ≅ Br(L/K)` of order `[L:K]`
(`HasseFundamentalClass`, Milne, *CFT*, Remark 5.5 and Theorem VIII.4.7).  In particular neither
Hecke's theorem (the analytic second inequality) nor Hasse's norm principle is needed any more on
this route.

## Main results

* `NK.GlobalCFTdeep.cohomologicalFieldAxiom_of_fundamentalClass` — `CohomologicalFieldAxiom K L`
  from `HasseFundamentalClass`;
* `NK.GlobalCFTdeep.galoisReciprocity_of_fundamentalClass` — the reciprocity isomorphism
  `C_K ⧸ N_{L/K}C_L ≅ Gal(L/K)ᵃᵇ` from `HasseFundamentalClass`;
* `NK.GlobalCFTdeep.artinReciprocity_of_fundamentalClass` — Artin's reciprocity law for abelian
  extensions from `HasseFundamentalClass`.
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

/-- **The class-formation axioms for every finite Galois extension of number fields, from Hasse's
fundamental class alone.**  The vanishing of `H¹(H, C_L)` is *proved*
(`subsingleton_groupCohomology_one_res_ideleClassGroup`); the order of `H²` and the fundamental
class are transported from the extension `L / L^H` along the equivariant identification
`Gal(L/L^H) ≅ H`. -/
theorem cohomologicalFieldAxiom_of_fundamentalClass
    (hfc : SecondInequality.HasseFundamentalClass) {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    CohomologicalFieldAxiom K L where
  h1_trivial H := subsingleton_groupCohomology_one_res_ideleClassGroup H
  h2_card H := by
    classical
    let K' : IntermediateField K L := IntermediateField.fixedField H
    haveI : NumberField ↥K' := inferInstance
    haveI : FiniteDimensional ↥K' L := inferInstance
    haveI : IsGalois ↥K' L := inferInstance
    have hiso := groupCohomology.mapIso (G := ↥H) (H := (L ≃ₐ[↥K'] L))
      (A := IdeleClassGroup.rep ↥K' L)
      (B := Rep.res H.subtype (IdeleClassGroup.rep K L))
      (IntermediateField.subgroupEquivAlgEquiv H) (LinearEquiv.refl ℤ _)
      (by intro g; rfl) 2
    have hcard : Nat.card (groupCohomology (Rep.res H.subtype (IdeleClassGroup.rep K L)) 2)
        = Nat.card (groupCohomology (IdeleClassGroup.rep ↥K' L) 2) :=
      Nat.card_congr hiso.toLinearEquiv.toEquiv
    rw [hcard, hfc.order (K := ↥K') (L := L)]
    exact (Nat.card_congr (IntermediateField.subgroupEquivAlgEquiv H).toEquiv).symm
  fundamentalClass := hfc.fundamentalClass

/-- **Artin's reciprocity law for every finite solvable Galois extension**, from Hasse's
fundamental class alone. -/
noncomputable def galoisReciprocity_of_fundamentalClass
    (hfc : SecondInequality.HasseFundamentalClass) {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Group.IsSolvable (L ≃ₐ[K] L)] : GaloisReciprocity K L :=
  galoisReciprocity_of_cohomologicalFieldAxiom (cohomologicalFieldAxiom_of_fundamentalClass hfc)

/-- **Artin's reciprocity law for abelian extensions**, from Hasse's fundamental class alone. -/
noncomputable def artinReciprocity_of_fundamentalClass
    (hfc : SecondInequality.HasseFundamentalClass) {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative (L ≃ₐ[K] L)] : ArtinReciprocity K L :=
  artinReciprocity_of_cohomologicalFieldAxiom (cohomologicalFieldAxiom_of_fundamentalClass hfc)

end NK.GlobalCFTdeep
