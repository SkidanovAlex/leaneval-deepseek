import Mathlib
import Submission.NK.GlobalCFT.GaloisIdelesAction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Associativity of the action of `Gal(L/K)` on the idèle group

The group `Gal(L/K) = (L ≃ₐ[K] L)` acts on the idèle group `𝕀 L` componentwise by
`(σ · x)_w = σ_*(x_{σ⁻¹ w})`, where `σ_* : L_w ≃+* L_{σ w}` is the canonical isomorphism of local
fields.  This file proves that the operation is a genuine (left) action, i.e. that

`(σ * σ') • x = σ • (σ' • x)`

for all `σ σ' : Gal(L/K)` and `x : 𝕀 L`.

The only non-formal input is the *composition law for the local isomorphisms*: the local field
isomorphism attached to `(σ * σ')⁻¹` is the composite of the ones attached to `σ'⁻¹` and `σ⁻¹`
(transported along the equality `σ'⁻¹ • (σ⁻¹ • w) = (σ * σ')⁻¹ • w` of places).  Because the local
field `L_w` is a `match` on the place `w`, that equality is not definitional and the resulting
transport has to be handled carefully; the local statement is proved by a density argument exactly
as in `NK.GlobalCFT.Galois.globalCFT_localRingEquiv_comp`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT.Galois

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The component of a dependent function at two equal indices agree, after the tautological
transport of the index.  Stated as its own lemma so that `cases` sees the two indices as variables
(they are normally composite `match`-expressions on a place, where dependent elimination is
stuck). -/
lemma globalCFT_cast_dep_apply {α : Type*} {P : α → Type*} (x : (a : α) → P a) {a b : α}
    (h : a = b) : h ▸ x a = x b := by
  cases h; rfl

/-- **Composition law for the inverse local isomorphisms.**  For `σ σ' : Gal(L/K)`, a place `w` of
`L` and the tautological equality `h : σ'⁻¹ • (σ⁻¹ • w) = (σ * σ')⁻¹ • w` of places, the canonical
local isomorphism attached to `(σ * σ')⁻¹` at `w` is the composite of the ones attached to `σ'⁻¹`
(at `σ⁻¹ • w`) and to `σ⁻¹` (at `w`), transported along `h`.

This is the analogue of `NK.GlobalCFT.Galois.globalCFT_localRingEquiv_comp` for the inverses
`(σ * σ')⁻¹ = σ'⁻¹ * σ⁻¹`; as there, the proof is a density argument. -/
lemma globalCFT_localRingEquiv_inv_mul (σ σ' : L ≃ₐ[K] L) (w : Place L)
    (h : σ'⁻¹ • (σ⁻¹ • w) = (σ * σ')⁻¹ • w) (y : Place.localField L w) :
    Place.localRingEquiv (σ * σ')⁻¹ w y =
      h ▸ (Place.localRingEquiv (σ')⁻¹ (σ⁻¹ • w)) ((Place.localRingEquiv σ⁻¹ w) y) := by
  refine (localField_cast_eq_iff h _ _).mpr ?_
  have hdense : DenseRange (algebraMap L (Place.localField L w)) :=
    denseRange_algebraMap_localField w
  have hcont₁ : Continuous (fun y => h.symm ▸ ((Place.localRingEquiv (σ * σ')⁻¹ w) y)) :=
    continuous_localField_cast h.symm (continuous_localRingEquiv (σ * σ')⁻¹ w)
  have hcont₂ : Continuous (fun y => (Place.localRingEquiv (σ')⁻¹ (σ⁻¹ • w))
      ((Place.localRingEquiv σ⁻¹ w) y)) :=
    (continuous_localRingEquiv (σ')⁻¹ (σ⁻¹ • w)).comp (continuous_localRingEquiv σ⁻¹ w)
  have hfun : (fun y => h.symm ▸ ((Place.localRingEquiv (σ * σ')⁻¹ w) y)) =
      fun y => (Place.localRingEquiv (σ')⁻¹ (σ⁻¹ • w)) ((Place.localRingEquiv σ⁻¹ w) y) := by
    refine DenseRange.equalizer hdense hcont₁ hcont₂ ?_
    funext y
    simp only [Function.comp_apply]
    rw [Place.localRingEquiv_algebraMap (σ * σ')⁻¹ w y,
      localField_cast_algebraMap h.symm ((σ * σ')⁻¹ y),
      Place.localRingEquiv_algebraMap σ⁻¹ w y,
      Place.localRingEquiv_algebraMap (σ')⁻¹ (σ⁻¹ • w) ((σ⁻¹) y)]
    simp [mul_inv_rev]
  exact congrFun hfun y

/-- The `RingEquiv.symm` form of `globalCFT_localRingEquiv_inv_mul`: the inverse of the local
isomorphism attached to `(σ * σ')⁻¹` is the composite of the inverses attached to `σ⁻¹` and
`σ'⁻¹`. -/
lemma globalCFT_symm_localRingEquiv_inv_mul (σ σ' : L ≃ₐ[K] L) (w : Place L)
    (h : σ'⁻¹ • (σ⁻¹ • w) = (σ * σ')⁻¹ • w)
    (v : Place.localField L (σ'⁻¹ • (σ⁻¹ • w))) :
    (Place.localRingEquiv (σ * σ')⁻¹ w).symm (h ▸ v) =
      (Place.localRingEquiv σ⁻¹ w).symm
        ((Place.localRingEquiv (σ')⁻¹ (σ⁻¹ • w)).symm v) := by
  have key : (Place.localRingEquiv (σ * σ')⁻¹ w)
      ((Place.localRingEquiv σ⁻¹ w).symm
        ((Place.localRingEquiv (σ')⁻¹ (σ⁻¹ • w)).symm v)) = h ▸ v := by
    rw [globalCFT_localRingEquiv_inv_mul σ σ' w h]
    rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  rw [← key, RingEquiv.symm_apply_apply]

theorem globalCFT_mul_smul_idele {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (σ σ' : L ≃ₐ[K] L) (x : NK.GlobalCFT.Idele L) :
    (σ * σ') • x = σ • (σ' • x) := by
  ext w
  simp only [Idele.smul_apply]
  simp only [Units.coe_map]
  have h : σ'⁻¹ • (σ⁻¹ • w) = (σ * σ')⁻¹ • w :=
    (globalCFT_smul_place_smul σ⁻¹ σ'⁻¹ w).trans (congrArg (· • w) (mul_inv_rev σ σ').symm)
  have hval : (↑(x ((σ * σ')⁻¹ • w)) : Place.localField L ((σ * σ')⁻¹ • w)) =
      h ▸ (↑(x (σ'⁻¹ • (σ⁻¹ • w))) : Place.localField L (σ'⁻¹ • (σ⁻¹ • w))) :=
    (globalCFT_cast_dep_apply (fun v => (↑(x v) : Place.localField L v)) h).symm
  rw [hval]
  exact globalCFT_symm_localRingEquiv_inv_mul σ σ' w h ↑(x (σ'⁻¹ • (σ⁻¹ • w)))

end NK.GlobalCFT.Galois
