/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFT.IdeleClassGroup
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_idealClassMap_exists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local–global exact sequence `1 → 𝒪_Kˣ → ∏_v 𝒪_vˣ → C_K → Cl(K) → 1`

The **divisor map** `x ↦ ∏_q q ^ (exp_q x)` of an idèle
(`NK.GlobalCFT.IdeleClassGroup.idealOf`, in
`Submission/Work/GlobalCFT/IdeleClassGroup/globalCFT_exists_finset_isBoundedIntegral.lean`) is
well defined on idèle classes because the divisor of a principal idèle is principal
(`NK.GlobalCFT.IdeleClassGroup.idealClassMap_principalIdele`) and yields the classical exact
sequence

`1 → 𝒪_Kˣ → ∏_v 𝒪_vˣ → C_K → Cl(K) → 1`,

where

* `∏_v 𝒪_vˣ` is the group `NK.GlobalCFT.Idele.integralIdeles K` of idèles which are local units
  at every finite place (there is no condition at the archimedean places),
* the map `∏_v 𝒪_vˣ → C_K` is the restriction of the quotient map `𝕀 K → C_K`,
* the kernel `𝒪_Kˣ` consists of the integral idèles that are principal, and
* the map `C_K → Cl(K)` is the induced divisor-class map.

## Main results

* `NK.GlobalCFT.IdeleClassGroup.idealClassMap`: the divisor-class map `𝕀 K →* Cl(K)`.
* `NK.GlobalCFT.IdeleClassGroup.idealClassMap_eq_one_iff`: an idèle has principal divisor iff it
  lies in `∏_v 𝒪_vˣ · Kˣ`.
* `NK.GlobalCFT.IdeleClassGroup.local_global_exact_sequence`: the induced map on `C_K` is
  surjective with kernel the image of `∏_v 𝒪_vˣ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT

namespace IdeleClassGroup

variable {K : Type*} [Field K] [NumberField K]

/-- **The local–global exact sequence**: the divisor-class map descends to a surjection
`C_K →* Cl(K)` whose kernel is the image of the integral idèles `∏_v 𝒪_vˣ`.  Equivalently,
`∏_v 𝒪_vˣ ⧸ 𝒪_Kˣ → C_K → Cl(K) → 1` is exact at `C_K` and `Cl(K)`. -/
theorem local_global_exact_sequence (K : Type*) [Field K] [NumberField K] :
    ∃ (f : IdeleClassGroup K →* ClassGroup (𝓞 K)),
      f.ker = (Idele.integralIdeles K).map (IdeleClassGroup.mk K) ∧ Function.Surjective f :=
  globalCFT_idealClassMap_exists

end IdeleClassGroup

end NK.GlobalCFT
