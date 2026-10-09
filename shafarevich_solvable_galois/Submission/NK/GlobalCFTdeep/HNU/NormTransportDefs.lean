import Mathlib
import Submission.NK.GlobalCFT.GlobalCFT
import Submission.NK.GlobalCFTdeep.Transport.PlaceDefs
import Submission.NK.GlobalCFTdeep.Transport.IdeleTransport
import Submission.NK.GlobalCFTdeep.Transport.NormTransportAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The idèle transport along a ring equivalence of number fields, built from *explicit* local
isomorphisms

`NK.GlobalCFTdeep.Transport.localFieldEquiv` (in `Transport/IdeleEquiv.lean`) chooses the local
isomorphisms of completions from an existence statement that records only compatibility with the
structure maps and with the local units.  That is enough for transporting the *principal* idèles,
but not for the transport of the *norm*: to compare `N_{L_w/K_v}` with `N_{L'_{w'}/K'_{v'}}` one
needs the chosen local isomorphism to be *continuous* (a density argument identifies it with the
completion of `L → L'`).

This module therefore builds the idèle transport from the explicit local isomorphisms of
`NK.GlobalCFTdeep.Transport.NormTransport.localFieldIso`, whose existence statement *does* record
continuity (`NormTransport.localFieldIso_continuous`), so that the local norms can be compared.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.HNU

open NK.GlobalCFT

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K']

/-- **The idèle transport** `𝕀 K ≃* 𝕀 K'` attached to a ring equivalence of number fields, built
from the explicit local isomorphisms `Transport.NormTransport.localFieldIso`. -/
noncomputable def ideleEquivExplicit (e : K ≃+* K') : Idele K ≃* Idele K' :=
  Transport.IdeleTransport.ideleEquiv (Transport.placeEquiv e)
    (Transport.NormTransport.localFieldIso e)
    (fun v u => Transport.NormTransport.localFieldIso_localUnits e v u)

/-- The evaluation lemma for `ideleEquivExplicit`: at the transported place, the transported idèle
is the local transport of the component. -/
theorem ideleEquivExplicit_apply (e : K ≃+* K') (x : Idele K) (v : Place K) :
    ideleEquivExplicit e x (Transport.placeEquiv e v) =
      Units.map (Transport.NormTransport.localFieldIso e v).toMonoidHom (x v) :=
  Transport.IdeleTransport.ideleEquiv_apply_placeEquiv (Transport.placeEquiv e)
    (Transport.NormTransport.localFieldIso e)
    (fun v u => Transport.NormTransport.localFieldIso_localUnits e v u) x v

/-- **The idèle transport is compatible with the diagonal embeddings.** -/
theorem ideleEquivExplicit_principalIdele (e : K ≃+* K') (a : Kˣ) :
    ideleEquivExplicit e (Idele.principalIdele K a) =
      Idele.principalIdele K' (Units.map e.toMonoidHom a) := by
  refine Idele.ext fun v => ?_
  obtain ⟨v₀, rfl⟩ := (Transport.placeEquiv e).surjective v
  apply Units.ext
  rw [ideleEquivExplicit_apply, Idele.principalIdele_apply, Idele.principalIdele_apply,
    Units.coe_map, Units.coe_map, Units.coe_map]
  change (Transport.NormTransport.localFieldIso e v₀)
      ((algebraMap K (Place.localField K v₀)) (a : K)) =
    (algebraMap K' (Place.localField K' (Transport.placeEquiv e v₀))) (e (a : K))
  rw [Transport.NormTransport.localFieldIso_algebraMap]

end NK.GlobalCFTdeep.HNU
