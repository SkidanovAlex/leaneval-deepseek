import Mathlib
import Submission.Work.SSGRoute.local_lifting_setup
import Submission.Work.SSGRoute.RamifiedPlacesAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# From the global inertia condition to the local inertia subgroup

This file proves `Work.SSGRoute.inertia_of_isInertia`, the "one half" of the identification of the
global inertia subgroup `I_A = {σ ∈ D_A : σ acts trivially on the residue field of A}` of a finite
place `A` of `ℚ̄` with the local inertia subgroup
`NK.LocalAnabelian.inertiaSubgroup p ≤ Gal(κ̄/κ)`, κ = ℚ_𝔭`, under the local–global
identification `NK.FrobeniusBridge.localGaloisEquiv`.

The mathematics is the projective-limit description of the inertia subgroup: an element of the
decomposition group acting trivially on the residue field of the *place* `A` acts trivially on the
residue field of every finite normal level below `A`, and an element of the decomposition group
acting trivially on the residue field of every finite level lies in the local inertia subgroup
(`NK.ResidueFrob.inertia_of_levels_of_tameData`).

The level-wise residue-triviality is the precise bookkeeping between the valuation condition of
`SSGRoute.IsInertia` and the prime `P_L` of `𝓞 L` below `A`, whose elements are exactly those of
`A`-adic value `< 1` (`Work.SSGRoute.primeOfLevel_mem_iff`).  For `x ∈ 𝓞 L`, the element `σ x` of
`ℚ̄` is the image of `galRestrict (𝓞 ℚ) ℚ L (𝓞 L) (σ|_L) x` (`algebraMap_galRestrict_apply`), so
`σ|_L x - x ∈ P_L` because `x ∈ A` (`ringOfIntegers_mem_of_isFinPlace`) and `σ` acts trivially on
the residue field of `A`.

The companion direction (`Work.SSGRoute.isInertia_of_mem_inertia`) is the other half.
-/

namespace Work.SSGRoute

set_option linter.unusedVariables false

theorem inertia_of_isInertia
    (A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar)
    (p q : ℕ) (hT : NK.LocalTame.TameData p q (NK.FrobeniusBridge.localField A')
      (NK.FrobeniusBridge.localClosure A'))
    (hq : NK.ResidueFrob.ResidueCardMatches A' q)
    (hp : p = Work.SSGRoute.residueChar A')
    (σ : ↥(SSGRoute.decomp ℚ A'.1))
    (h : SSGRoute.IsInertia ℚ A'.1 (σ : SSGRoute.QBar ≃ₐ[ℚ] SSGRoute.QBar)) :
    NK.FrobeniusBridge.localGaloisEquiv A' σ ∈
      NK.LocalAnabelian.inertiaSubgroup (κ := NK.FrobeniusBridge.localField A')
        (K' := NK.FrobeniusBridge.localClosure A') p := by
  refine NK.ResidueFrob.inertia_of_levels_of_tameData A' hT hq σ.1 ?_ h.1
  -- `σ` acts trivially on the residue field of every finite normal level below `A'`
  intro L hFD hN hNF x
  rw [Work.SSGRoute.primeOfLevel_mem_iff L A'.1 A'.2, map_sub]
  rw [IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥L) ↥L SSGRoute.QBar,
    algebraMap_galRestrict_apply,
    Submission.NeukirchUchida.Local.restrictNormalHom_apply_algebraMap,
    IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥L) ↥L SSGRoute.QBar]
  exact h.2 (algebraMap (NumberField.RingOfIntegers ↥L) SSGRoute.QBar x)
    (ringOfIntegers_mem_of_isFinPlace L A'.1 A'.2 x)

end Work.SSGRoute
