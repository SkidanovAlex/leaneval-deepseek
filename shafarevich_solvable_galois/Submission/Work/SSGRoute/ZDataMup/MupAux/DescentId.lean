import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.FractionalIdeal.Basic
import Submission.NK.CFTLib.ARLAlt.Descent
import Submission.NK.CFTLib.ARLAlt.Setup
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.normIdeleHom_mem_congruenceSubgroupId
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Descent of the principal ray along the relative norm (ideal moduli)

Ideal-modulus version of `NK.NUV2.ArtinBridge.spanUnit_norm_mem_principalRay_of_congrOne` and
`NK.CFTLib.ARLAlt.principalRay_map_relNormUnit_le`: if `β ∈ Eˣ` is congruent to `1` modulo the
ideal modulus `𝔠` of `E`, and `𝔠 ≤ 𝔪·𝓞_E` (so that the congruence of `β` is finer than the
`𝔪`-congruence of the *norm*), then the principal ideal of `N_{E/K}(β)` lies in the principal ray
`P(𝔪) ⊆ Frac K`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup.MupAux

open NK.GlobalCFT

/-- **Norm descent for the principal ray.**  If `𝔠 ≤ 𝔪·𝓞_E` and `β ≡ 1 mod* 𝔠`, then the
principal ideal of the norm `N_{E/K}β` is in the principal ray of `𝔪`. -/
theorem spanUnit_norm_mem_principalRayId_of_congrOneId {K E : Type} [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra K E] [FiniteDimensional K E]
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) (𝔠 : Ideal (NumberField.RingOfIntegers E))
    (h𝔪 : 𝔪 ≠ ⊥) (h𝔠ne : 𝔠 ≠ ⊥)
    (hle : 𝔠 ≤ Ideal.map (algebraMap (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers E)) 𝔪)
    (β : Eˣ) (hcong : NK.CFTLib.ArtinReciprocityIdeal.CongrOneId 𝔠 β) :
    NK.CFTLib.ArtinReciprocityIdeal.spanUnit (K := K) (Units.map (Algebra.norm K) β) ∈
      NK.CFTLib.ArtinReciprocityIdeal.principalRayId 𝔪 := by
  -- the principal idèle of `β` lies in `U(𝔠)`, hence in `U(𝔪·𝓞_E)`
  have hmem : Idele.principalIdele E β ∈
      NK.CFTLib.ArtinReciprocityIdeal.congruenceSubgroupId E 𝔠 :=
    (NK.CFTLib.ArtinReciprocityIdeal.principalIdele_mem_congruenceSubgroupId_iff h𝔠ne β).mpr hcong
  have hmem' : Idele.principalIdele E β ∈
      NK.CFTLib.ArtinReciprocityIdeal.congruenceSubgroupId E
        (Ideal.map (algebraMap (𝓞 K) (𝓞 E)) 𝔪) :=
    NK.CFTLib.ArtinReciprocityIdeal.congruenceSubgroupId_mono h𝔠ne hle hmem
  -- its idèlic norm is congruent to `1` modulo `𝔪`
  have hnorm : Idele.normIdeleHom K E (Idele.principalIdele E β) ∈
      NK.CFTLib.ArtinReciprocityIdeal.congruenceSubgroupId K 𝔪 :=
    Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.normIdeleHom_mem_congruenceSubgroupId
      𝔪 h𝔪 hmem'
  rw [Idele.normIdeleHom_principalIdele (K := K) (L := E)] at hnorm
  -- back to the principal ray
  exact Subgroup.subset_closure ⟨Units.map (Algebra.norm K) β,
    (NK.CFTLib.ArtinReciprocityIdeal.principalIdele_mem_congruenceSubgroupId_iff h𝔪
      (Units.map (Algebra.norm K) β)).mp hnorm, rfl⟩

/-- **The relative norm maps the principal ray of `E` into the principal ray of `K`**, provided
`𝔠 ≤ 𝔪·𝓞_E`. -/
theorem principalRayId_map_relNormUnit_le {K E : Type} [Field K] [NumberField K] [Field E]
    [NumberField E] [Algebra K E] [FiniteDimensional K E]
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) (𝔠 : Ideal (NumberField.RingOfIntegers E))
    (h𝔪 : 𝔪 ≠ ⊥) (h𝔠ne : 𝔠 ≠ ⊥)
    (hle : 𝔠 ≤ Ideal.map (algebraMap (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers E)) 𝔪) :
    (NK.CFTLib.ArtinReciprocityIdeal.principalRayId 𝔠).map
        (NK.CFTLib.ARL.relNormUnit (K := K) (L := E))
      ≤ NK.CFTLib.ArtinReciprocityIdeal.principalRayId 𝔪 := by
  rw [NK.CFTLib.ArtinReciprocityIdeal.principalRayId,
    Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
  rintro A ⟨β, hβ, rfl⟩
  change NK.CFTLib.ARL.relNormUnit (K := K) (L := E)
    (NK.CFTLib.ArtinReciprocityIdeal.spanUnit β) ∈
      NK.CFTLib.ArtinReciprocityIdeal.principalRayId 𝔪
  have hspanE : NK.CFTLib.ArtinReciprocityIdeal.spanUnit β = NK.CFTLib.ARL.unitsToIdealUnits E β :=
    Units.ext rfl
  have hspanK : NK.CFTLib.ARL.unitsToIdealUnits K (Units.map (Algebra.norm K) β)
      = NK.CFTLib.ArtinReciprocityIdeal.spanUnit (Units.map (Algebra.norm K) β) := Units.ext rfl
  have h : NK.CFTLib.ARL.relNormUnit (K := K) (L := E)
      (NK.CFTLib.ArtinReciprocityIdeal.spanUnit β) =
      NK.CFTLib.ArtinReciprocityIdeal.spanUnit (Units.map (Algebra.norm K) β) := by
    rw [hspanE, NK.CFTLib.ARLAlt.relNormUnit_unitsToIdealUnits, hspanK]
  rw [h]
  exact spanUnit_norm_mem_principalRayId_of_congrOneId 𝔪 𝔠 h𝔪 h𝔠ne hle β hβ

end Work.SSGRoute.ZDataMup.MupAux
