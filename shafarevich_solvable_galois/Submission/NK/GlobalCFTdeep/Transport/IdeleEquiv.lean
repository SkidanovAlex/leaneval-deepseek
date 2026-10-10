import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.Transport.IdeleTransport
import Submission.NK.GlobalCFTdeep.Transport.NormTransportAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transport of the local fields and of the idèle group along a ring equivalence

We take the transport of the local fields to be the canonical one constructed in
`Transport/NormTransportAux.lean` (`NormTransport.localFieldIso`, the lift of the ring equivalence
to the completions at each place), which is compatible with the structure maps, continuous and
preserves the local units.  Feeding it into the general restricted-product transport
`IdeleTransport.ideleEquiv` gives the transport `ideleEquiv e : 𝕀 K ≃* 𝕀 K'` of the idèle group.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.Transport

open NK.GlobalCFT

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K']

/-- **Transport of the local field** at a place along a ring equivalence of number fields. -/
noncomputable def localFieldEquiv (e : K ≃+* K') (v : Place K) :
    Place.localField K v ≃+* Place.localField K' (placeEquiv e v) :=
  NormTransport.localFieldIso e v

/-- The transported local field equivalence is compatible with the structure maps. -/
theorem localFieldEquiv_algebraMap (e : K ≃+* K') (v : Place K) (x : K) :
    localFieldEquiv e v (algebraMap K (Place.localField K v) x) =
      algebraMap K' (Place.localField K' (placeEquiv e v)) (e x) :=
  NormTransport.localFieldIso_algebraMap e v x

/-- The transported local field equivalence carries local units onto local units. -/
theorem localFieldEquiv_localUnits (e : K ≃+* K') (v : Place K)
    (u : (Place.localField K v)ˣ) :
    u ∈ Place.localUnits K v ↔
      Units.map (localFieldEquiv e v).toMonoidHom u ∈ Place.localUnits K' (placeEquiv e v) :=
  NormTransport.localFieldIso_localUnits e v u

/-- **Transport of the idèle group along a ring equivalence of number fields**: `𝕀 K ≃* 𝕀 K'`. -/
noncomputable def ideleEquiv (e : K ≃+* K') : Idele K ≃* Idele K' :=
  IdeleTransport.ideleEquiv (placeEquiv e) (localFieldEquiv e)
    (fun v u => localFieldEquiv_localUnits e v u)

/-- **Evaluation of the idèle transport**: at the place `σ v = placeEquiv e v`, the transported
idèle is the local transport of the component at `v`. -/
theorem ideleEquiv_apply_placeEquiv (e : K ≃+* K') (x : Idele K) (v : Place K) :
    ideleEquiv e x (placeEquiv e v) = Units.map (localFieldEquiv e v).toMonoidHom (x v) :=
  IdeleTransport.ideleEquiv_apply_placeEquiv (placeEquiv e) (localFieldEquiv e)
    (fun v u => localFieldEquiv_localUnits e v u) x v

/-- The idèle transport sends the principal idèle of `a` to the principal idèle of `e a`. -/
theorem ideleEquiv_principalIdele (e : K ≃+* K') (a : Kˣ) :
    ideleEquiv e (Idele.principalIdele K a) = Idele.principalIdele K' (Units.map e a) := by
  ext v
  obtain ⟨w, rfl⟩ := (placeEquiv e).surjective v
  rw [ideleEquiv_apply_placeEquiv, Idele.principalIdele_apply, Idele.principalIdele_apply]
  simp only [Units.coe_map, MonoidHom.coe_coe]
  exact localFieldEquiv_algebraMap e w (a : K)

end NK.GlobalCFTdeep.Transport
