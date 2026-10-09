import Mathlib
import Submission.NK.GlobalCFTdeep.hasseNorm_index_eq_universe
import Submission.NK.GlobalCFTdeep.hasseNorm_form_universe
import Submission.NK.HassePrinciple.Norm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Hasse's norm theorem for cyclic extensions of number fields, in an arbitrary universe

`NK.HassePrinciple.HasseNormTheorem.{u}` bundles the two classical faces of the Hasse norm
theorem for a cyclic extension `L/K` of number fields:

* `index_eq` — the reciprocity isomorphism in index form,
  `[C_K : N_{L/K} C_L] = [L : K]`;
* `hasse_norm` — the local–global principle for norms, `Kˣ ∩ N_{L/K}𝕀_L = N_{L/K}Lˣ`.

Both halves are proved in this chapter, unconditionally, at *every* universe:

* the index half is `NK.GlobalCFTdeep.hasseNorm_index_eq_universe`, which compares the number
  fields with their countable `Type 0` models `Shrink` and uses the invariance of the norm index
  under a compatible pair of ring equivalences of extensions
  (`NK.GlobalCFTdeep.normClassSubgroup_index_eq_of_ringEquiv`);
* the norm half is `NK.GlobalCFTdeep.hasseNorm_form_universe`, the transport of the `Type 0`
  local–global principle (`NK.GlobalCFTdeep.hasseNormTheorem`, proved from the vanishing
  `Ĥ⁻¹(Gal(L/K), C_L) = 0` and the five-term Tate sequence) along the same models.

Consequently this file **discharges** the field `NK.HasseTwist.Sha2Input.hasse_norm` (and the
corresponding field of the untwisted `NK.HassePrinciple` input catalogue) with no additional
hypotheses.  The purpose of the universe generality is exactly this: the twisted Hasse principle
`NK.HasseTwist.Sha2Input p K K' κ κ'` is stated for `K K' κ κ' : Type u`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

namespace NK.GlobalCFTdeep

/-- **Hasse's norm theorem for cyclic extensions of number fields, at an arbitrary universe**
(`NK.HassePrinciple.HasseNormTheorem.{u}`): the norm index formula
`[C_K : N_{L/K}C_L] = [L:K]` and the local–global principle for norms
`Kˣ ∩ N_{L/K}𝕀_L = N_{L/K}Lˣ`, for every cyclic extension of number fields.

Both fields are proved in this chapter (see the module docstring); this is the assembled
`structure`, i.e. the licensed input discharged. -/
theorem hasseNormTheoremUniverse : NK.HassePrinciple.HasseNormTheorem.{u} where
  index_eq := fun {K L} _ _ _ _ _ _ _ (hcyc : IsCyclic (L ≃ₐ[K] L)) =>
    @hasseNorm_index_eq_universe K L _ _ _ _ _ _ _ hcyc
  hasse_norm := fun {K L} _ _ _ _ _ _ _ (hcyc : IsCyclic (L ≃ₐ[K] L)) a ha =>
    @hasseNorm_form_universe K L _ _ _ _ _ _ _ hcyc a ha

/-- The `Type 0` Hasse norm theorem of `NK.GlobalCFTdeep.hasseNormTheorem` is an instance of the
universe-polymorphic one: at `u = 0` the assembled structure is (definitionally) the same data. -/
theorem hasseNormTheoremUniverse_zero : NK.HassePrinciple.HasseNormTheorem.{0} :=
  hasseNormTheoremUniverse

end NK.GlobalCFTdeep
