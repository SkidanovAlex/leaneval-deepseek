import Mathlib
import Submission.Commons.RepresentationTheory.GroupCohomology.res_comp_inf_eq_zero_of_ord
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_pgroup_intermediate_field
import Submission.NK.GlobalCFT.Cohomology
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliaries for `NK.CFTLib.Existence.arl_arithmetic_input`

The target `NK.CFTLib.Existence.arl_arithmetic_input` is the cohomological comparison
`range(inf_{Msub}) ≤ ker(res_{Nsub})` for the idèle class group representation `C_Ω`.

This file contains the two structural inputs of the comparison that are independent of the
arithmetic of the idèle class group:

* `arlIncl` — the coefficient inclusion `A^M ↪ A` as a morphism of `N`-representations;
* `arlIncl_mackey` — the Mackey identity identifying `res_N ∘ inf_M` with the map on `H²` induced by
  `arlIncl` (this is `Commons.NumberTheory.NumberField.Completion.resNatTrans_comp_infNatTrans_eq_map`).

## A recorded obstruction (do not re-derive)

The "monomorphism of valuation" engine
`Commons.RepresentationTheory.GroupCohomology.res_comp_inf_eq_zero_of_ord` — which is the tool used
for the *local* analogues of this comparison (`unitsValLog` on the units of an adic completion,
see `Commons.NumberTheory.NumberField.Completion.exists_addOrderOf_eq_finrank_groupCohomology_two_units`)
— **cannot be applied to the global idèle class group**.  Its input is an `N`-invariant map
`ord₂ : C_Ω ⟶ ℤ` of `ℤ`-representations, i.e. a group homomorphism `C_Ω → ℤ`, whose induced map
`H²(N, C_Ω) → H²(N, ℤ)` must be injective.  But **`Hom(C_F, ℤ) = 0` for every number field `F`**:
`C_F = C_F⁰ · C_F¹` with `C_F⁰` (the connected component, a quotient of the idèle class group
modulo the compact group `C_F¹`) divisible and `C_F¹ = ker |·|` compact, so any homomorphism
`C_F → ℤ` vanishes on both factors.  Hence `ord₂ = 0`, `hmono` would force `H²(N, C_Ω) = 0`, and
the engine's hypothesis is unsatisfiable.  (The two lemmas below remain valid and useful; the
`ArlOrdData` route to the target is *not*.)

The comparison itself is equivalent, via the `H⁰`-computation
(`NK.GlobalCFT.globalCFT_H0Computation`), to the arithmetic statement
`C_K ⊆ N_{Ω/F} C_Ω` for `F = fixedField Nsub` — the classical input of Route B.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory

-- Prefer the `Module`/`AddCommGroup` structures coming from a representation over the generic
-- `ℤ`-module structure, so that the `Rep ℤ G`-diamonds do not produce `isDefEq` failures.
attribute [local instance 5000] Rep.hV1 Rep.hV2
attribute [local instance 100] AddCommGroup.toIntModule

namespace NK.CFTLib.Existence

/-- The coefficient inclusion `A^M ↪ A` (the invariants of `A` under `M` inside `A`), viewed as a
morphism of `N`-representations via the quotient map `N → G ⧸ M`. -/
noncomputable abbrev arlIncl {K Ω : Type} [Field K] [NumberField K] [Field Ω] [NumberField Ω]
    [Algebra K Ω] (Msub Nsub : Subgroup Gal(Ω/K)) [Msub.Normal] :
    Rep.res ((QuotientGroup.mk' Msub).comp Nsub.subtype)
        ((NK.GlobalCFT.IdeleClassGroup.rep K Ω).quotientToInvariants Msub) ⟶
      Rep.res Nsub.subtype (NK.GlobalCFT.IdeleClassGroup.rep K Ω) :=
  Rep.resMap Nsub.subtype
    (Rep.ofHom ((NK.GlobalCFT.IdeleClassGroup.rep K Ω).ρ.quotientToInvariants_lift Msub))

/-- **Mackey identity for the pair `(Msub, Nsub)`.**  The composite `res_{Nsub} ∘ inf_{Msub}` is the
map on `H²` induced by the coefficient inclusion `arlIncl`. -/
lemma arlIncl_mackey {K Ω : Type} [Field K] [NumberField K] [Field Ω] [NumberField Ω]
    [Algebra K Ω] (Msub Nsub : Subgroup Gal(Ω/K)) [Msub.Normal] [Nsub.Normal] :
    (groupCohomology.infNatTrans ℤ Msub 2).app (NK.GlobalCFT.IdeleClassGroup.rep K Ω) ≫
        (groupCohomology.resNatTrans ℤ Nsub.subtype 2).app
          (NK.GlobalCFT.IdeleClassGroup.rep K Ω)
      = groupCohomology.map ((QuotientGroup.mk' Msub).comp Nsub.subtype) (arlIncl Msub Nsub) 2 :=
  Commons.NumberTheory.NumberField.Completion.resNatTrans_comp_infNatTrans_eq_map Msub Nsub _

/-- The image of the norm map of the restriction of `A = C_Ω` to `Nsub`, as a submodule of `A`.
This is the submodule appearing in the arithmetic input
`NK.CFTLib.Existence.rep_invariants_le_range_norm_of_auxiliary`. -/
noncomputable abbrev arlNormImage (K Ω : Type) [Field K] [NumberField K] [Field Ω] [NumberField Ω]
    [Algebra K Ω] (Nsub : Subgroup Gal(Ω/K)) [Nsub.Normal] [Fintype Nsub] :
    Submodule ℤ (NK.GlobalCFT.IdeleClassGroup.rep K Ω).V :=
  LinearMap.range ((Rep.res Nsub.subtype (NK.GlobalCFT.IdeleClassGroup.rep K Ω)).ρ.norm)

end NK.CFTLib.Existence
