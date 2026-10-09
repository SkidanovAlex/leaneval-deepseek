import Submission.NK.GlobalCFTdeep.Transport.PlaceDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transport of the idèle group along a bijection of places

This file contains the *general* transport of the idèle group `𝕀 K = ∏ʳ_v K_vˣ` along a
bijection `σ : Place K ≃ Place K'` of places, together with a compatible family of ring
equivalences `Φ v : K_v ≃+* K'_{σ v}` of the local fields carrying the local units onto the local
units (`hU`).  The result is a group isomorphism `Idele K ≃* Idele K'`.

The construction goes through the underlying product of unit groups
(`Equiv.piCongr`, which handles the dependent indexing correctly) and restricts to the subgroups
defined by the "eventually in the local units" condition.  The key evaluation lemma
`ideleEquiv_apply_placeEquiv` states that the transported idèle at the place `σ v` is the local
transport of the component at `v`, so that all downstream proofs can avoid the dependent casts.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.Transport

namespace IdeleTransport

open NK.GlobalCFT

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K']

/-- Reindexing of "eventually in `cofinite`" statements along a bijection of places. -/
theorem eventually_placeEquiv (σ : Place K ≃ Place K') (p : Place K' → Prop) :
    (∀ᶠ j in Filter.cofinite, p j) ↔ (∀ᶠ v in Filter.cofinite, p (σ v)) := by
  rw [Filter.eventually_cofinite, Filter.eventually_cofinite]
  constructor
  · intro h
    refine (h.image σ.symm).subset (fun v hv => ⟨σ v, ?_, σ.symm_apply_apply v⟩)
    simpa only [Set.mem_setOf_eq] using hv
  · intro h
    refine (h.image σ).subset (fun j hj => ⟨σ.symm j, ?_, σ.apply_symm_apply j⟩)
    simpa only [Set.mem_setOf_eq, σ.apply_symm_apply] using hj

/-- The transport of the product `∏_v K_vˣ` of local unit groups along a bijection of places and
a compatible family of local field equivalences. -/
noncomputable def piEquiv (σ : Place K ≃ Place K')
    (Φ : ∀ v : Place K, Place.localField K v ≃+* Place.localField K' (σ v)) :
    (Π v : Place K, (Place.localField K v)ˣ) ≃ (Π j : Place K', (Place.localField K' j)ˣ) :=
  Equiv.piCongr σ (fun v => (Units.mapEquiv (Φ v)).toEquiv)

/-- **The evaluation lemma for `piEquiv`**: at the place `σ v`, the transport is the local
transport of the component at `v`. -/
theorem piEquiv_apply_place (σ : Place K ≃ Place K')
    (Φ : ∀ v : Place K, Place.localField K v ≃+* Place.localField K' (σ v))
    (x : Π v : Place K, (Place.localField K v)ˣ) (v : Place K) :
    piEquiv σ Φ x (σ v) = Units.map (Φ v).toMonoidHom (x v) := by
  simp only [piEquiv, Equiv.piCongr, Equiv.trans_apply, Equiv.piCongrLeft_apply_apply,
    Equiv.piCongrRight_apply, Pi.map_apply, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
    MonoidHom.coe_coe]
  rfl

/-- `piEquiv` is multiplicative. -/
theorem piEquiv_mul (σ : Place K ≃ Place K')
    (Φ : ∀ v : Place K, Place.localField K v ≃+* Place.localField K' (σ v))
    (f g : Π v : Place K, (Place.localField K v)ˣ) :
    piEquiv σ Φ (f * g) = piEquiv σ Φ f * piEquiv σ Φ g := by
  funext j
  obtain ⟨v, rfl⟩ := σ.surjective j
  rw [piEquiv_apply_place, Pi.mul_apply, Pi.mul_apply, piEquiv_apply_place, piEquiv_apply_place,
    map_mul]

/-- The restricted-product condition transports under `piEquiv`. -/
theorem ideleEventually_iff (σ : Place K ≃ Place K')
    (Φ : ∀ v : Place K, Place.localField K v ≃+* Place.localField K' (σ v))
    (hU : ∀ (v : Place K) (u : (Place.localField K v)ˣ),
      u ∈ Place.localUnits K v ↔ Units.map (Φ v).toMonoidHom u ∈ Place.localUnits K' (σ v))
    (x : Π v : Place K, (Place.localField K v)ˣ) :
    (∀ᶠ j in Filter.cofinite, piEquiv σ Φ x j ∈ Place.localUnits K' j) ↔
      (∀ᶠ v in Filter.cofinite, x v ∈ Place.localUnits K v) := by
  rw [eventually_placeEquiv σ (fun j => piEquiv σ Φ x j ∈ Place.localUnits K' j)]
  exact Filter.eventually_congr (Filter.Eventually.of_forall fun v => by
    rw [piEquiv_apply_place, hU])

/-- **Transport of the idèle group along a bijection of places** and a compatible family of local
field equivalences: `𝕀 K ≃* 𝕀 K'`. -/
noncomputable def ideleEquiv (σ : Place K ≃ Place K')
    (Φ : ∀ v : Place K, Place.localField K v ≃+* Place.localField K' (σ v))
    (hU : ∀ (v : Place K) (u : (Place.localField K v)ˣ),
      u ∈ Place.localUnits K v ↔ Units.map (Φ v).toMonoidHom u ∈ Place.localUnits K' (σ v)) :
    Idele K ≃* Idele K' where
  toFun := (Equiv.subtypeEquiv (piEquiv σ Φ) (fun a => (ideleEventually_iff σ Φ hU a).symm)).toFun
  invFun := (Equiv.subtypeEquiv (piEquiv σ Φ) (fun a => (ideleEventually_iff σ Φ hU a).symm)).invFun
  left_inv := (Equiv.subtypeEquiv (piEquiv σ Φ)
    (fun a => (ideleEventually_iff σ Φ hU a).symm)).left_inv
  right_inv := (Equiv.subtypeEquiv (piEquiv σ Φ)
    (fun a => (ideleEventually_iff σ Φ hU a).symm)).right_inv
  map_mul' x y := by
    apply Subtype.ext
    exact piEquiv_mul σ Φ (x : Π v : Place K, (Place.localField K v)ˣ)
      (y : Π v : Place K, (Place.localField K v)ˣ)

/-- **The evaluation lemma for the idèle transport.** -/
theorem ideleEquiv_apply_placeEquiv (σ : Place K ≃ Place K')
    (Φ : ∀ v : Place K, Place.localField K v ≃+* Place.localField K' (σ v))
    (hU : ∀ (v : Place K) (u : (Place.localField K v)ˣ),
      u ∈ Place.localUnits K v ↔ Units.map (Φ v).toMonoidHom u ∈ Place.localUnits K' (σ v))
    (x : Idele K) (v : Place K) :
    ideleEquiv σ Φ hU x (σ v) = Units.map (Φ v).toMonoidHom (x v) := by
  change piEquiv σ Φ (x : Π v : Place K, (Place.localField K v)ˣ) (σ v) =
    Units.map (Φ v).toMonoidHom (x v)
  exact piEquiv_apply_place σ Φ x v

/-- The inverse direction of the evaluation lemma: at the place `σ v`, the inverse transport of a
component is the local inverse transport. -/
theorem ideleEquiv_symm_apply_placeEquiv (σ : Place K ≃ Place K')
    (Φ : ∀ v : Place K, Place.localField K v ≃+* Place.localField K' (σ v))
    (hU : ∀ (v : Place K) (u : (Place.localField K v)ˣ),
      u ∈ Place.localUnits K v ↔ Units.map (Φ v).toMonoidHom u ∈ Place.localUnits K' (σ v))
    (y : Idele K') (v : Place K) :
    (ideleEquiv σ Φ hU).symm y v = Units.map (Φ v).symm.toMonoidHom (y (σ v)) := by
  have h : Units.map (Φ v).toMonoidHom ((ideleEquiv σ Φ hU).symm y v) = y (σ v) := by
    rw [← ideleEquiv_apply_placeEquiv σ Φ hU ((ideleEquiv σ Φ hU).symm y) v,
      MulEquiv.apply_symm_apply]
  apply Units.ext
  rw [← h]
  simp [Units.coe_map]

end IdeleTransport

end NK.GlobalCFTdeep.Transport
