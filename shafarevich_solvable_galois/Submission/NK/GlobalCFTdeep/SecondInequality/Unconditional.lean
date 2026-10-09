/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFTdeep.SecondInequality.Corollaries
import Submission.NK.HassePrinciple.subsingleton_groupCohomology_one_ideleClassGroup_all
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The vanishing of `H¹(Gal(L/K), C_L)` from the second inequality

This file discharges the cyclic input of the workspace's `NK.HassePrinciple` development and
hence obtains the **vanishing of `H¹` of the idèle class group for every finite Galois extension of
number fields**:

  `H¹(Gal(L/K), C_L) = 0`.

The inputs are

* `HeckeRegularity` — Hecke's theorem, the analytic input of the second inequality, which yields
  the second inequality and hence (with the proved first inequality) the index formula
  `[C_K : N_{L/K}C_L] = [L:K]` for cyclic `L/K`;
* `NK.GlobalCFTdeep.HasseNormPrinciple` — the licensed local–global principle for norms (Hasse's
  norm theorem proper), which is *not* a consequence of the index formula.

Both are `Prop`-valued structures, so everything here is a proved conditional theorem.  The
cohomological argument (`NK.HassePrinciple.subsingleton_groupCohomology_one_ideleClassGroup_all`)
is Milne, *Class Field Theory*, Theorem 5.1(b), via the inflation–restriction sequence, the Sylow
reduction and the corestriction identity.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep.SecondInequality

open NK.GlobalCFT

/-- **The cyclic input of `NK.HassePrinciple`, from Hecke's regularity and the licensed Hasse
norm principle**: the index formula `[C_K : N_{L/K}C_L] = [L:K]` for cyclic `L/K` (which no longer
needs any input beyond `HeckeRegularity`), together with the local–global principle for norms. -/
theorem cyclicHasseInput_of_heckeRegularity (hH : HeckeRegularity)
    (h : NK.GlobalCFTdeep.HasseNormPrinciple) : NK.HassePrinciple.CyclicHasseInput where
  hasse_norm := hasseNormTheorem_of_heckeRegularity hH h
  herbrand := fun {_ _} _ _ _ _ _ _ _ _ =>
    NK.GlobalCFTdeep.cyclicHerbrandQuotient.herbrand

/-- **`H¹(Gal(L/K), C_L) = 0` for every finite Galois extension of number fields**, from Hecke's
regularity and the licensed Hasse norm principle.

This is Milne, *Class Field Theory*, Theorem 5.1(b): the first half of the class-formation axioms
for the idèle class group. -/
theorem subsingleton_groupCohomology_one_ideleClassGroup (hH : HeckeRegularity)
    (h : NK.GlobalCFTdeep.HasseNormPrinciple) {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    Subsingleton (groupCohomology (IdeleClassGroup.rep K L) 1) :=
  NK.HassePrinciple.subsingleton_groupCohomology_one_ideleClassGroup_all
    (cyclicHasseInput_of_heckeRegularity hH h)

/-- **`H¹(H, C_L) = 0` for every subgroup `H ≤ Gal(L/K)`**, from Hecke's regularity and the
licensed Hasse norm principle.  The subgroup `H` need not be normal: `L / L^H` is Galois with group
`H` (the fundamental theorem of finite Galois theory), so the previous result applies to the
extension `L^H ⊆ L` and is transported along the equivariant identification
`Gal(L/L^H) ≅ H`.

This is the `h1` field of `NK.GlobalCFT.CohomologicalFieldAxiom`. -/
theorem subsingleton_groupCohomology_one_res_ideleClassGroup (hH : HeckeRegularity)
    (h : NK.GlobalCFTdeep.HasseNormPrinciple) {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup (L ≃ₐ[K] L)) :
    Subsingleton (groupCohomology (Rep.res H.subtype (IdeleClassGroup.rep K L)) 1) := by
  classical
  let K' : IntermediateField K L := IntermediateField.fixedField H
  haveI : NumberField ↥K' := inferInstance
  haveI : FiniteDimensional ↥K' L := inferInstance
  haveI : IsGalois ↥K' L := inferInstance
  have hK' : Subsingleton (groupCohomology (IdeleClassGroup.rep ↥K' L) 1) :=
    subsingleton_groupCohomology_one_ideleClassGroup hH h (K := ↥K') (L := L)
  haveI : Subsingleton (groupCohomology (IdeleClassGroup.rep ↥K' L) 1) := hK'
  exact ((groupCohomology.mapIso (G := ↥H) (H := (L ≃ₐ[↥K'] L))
      (A := IdeleClassGroup.rep ↥K' L)
      (B := Rep.res H.subtype (IdeleClassGroup.rep K L))
      (IntermediateField.subgroupEquivAlgEquiv H) (LinearEquiv.refl ℤ _)
      (by intro g; rfl) 1).toLinearEquiv).injective.subsingleton

end NK.GlobalCFTdeep.SecondInequality
