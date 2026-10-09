import Mathlib
import Submission.NK.CFTLib.ArtinReciprocityIdeal.LangDefs
import Submission.NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_idealClassMap_exists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary vocabulary for the Lang cyclic norm-index inequality

This module sets up the idèle-theoretic vocabulary used in the proof of
`NK.CFTLib.ArtinReciprocityIdeal.langCyclicRelIndex`:

* `rho`: the map `𝕀 K →* (fractional ideals of K)ˣ`, `x ↦ (x)`;
* the index comparison between the ideal-theoretic quotient `I(m)/P(m)` and the idèle-theoretic
  quotient `𝕀 K ⧸ Kˣ·W(m)`, where `W(m)` is the congruence subgroup of the modulus `m` (idèles
  which are `≡ 1` modulo the primes dividing `m`, units at all other finite places, and positive
  at the real places).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.ArtinReciprocityIdeal

open NK.GlobalCFT

variable {K : Type*} [Field K] [NumberField K]

/-- The idèle group maps to the group of non-zero fractional ideals (`x ↦ (x)`).  This is the map
`NK.GlobalCFT.Idele.idealOfUnitHom` of the library, named `rho` here for brevity. -/
noncomputable def rho : Idele K →* Frac K := IdeleClassGroup.idealOfUnitHom K

@[simp] lemma rho_apply (x : Idele K) :
    ((rho x : Frac K) : FractionalIdeal (𝓞 K)⁰ K) = x.idealOf := by
  rw [rho, IdeleClassGroup.idealOfUnitHom_apply, Units.val_mk0]

lemma rho_principalIdele (a : Kˣ) : rho (Idele.principalIdele K a) = spanUnit a := by
  refine Units.ext ?_
  rw [rho_apply, coe_spanUnit, Idele.idealOf_principalIdele]

lemma ker_rho : (rho (K := K)).ker = Idele.integralIdeles K := by
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    rw [Idele.mem_integralIdeles]
    intro v hv
    have h2 := congrArg (fun u : Frac K => ((u : FractionalIdeal (𝓞 K)⁰ K))) h
    rw [rho_apply, Units.val_one] at h2
    exact (Idele.idealOf_eq_one_iff x).mp h2 v hv
  · intro h
    refine Units.ext ?_
    rw [Units.val_one, rho_apply]
    exact (Idele.idealOf_eq_one_iff x).mpr h

end NK.CFTLib.ArtinReciprocityIdeal
