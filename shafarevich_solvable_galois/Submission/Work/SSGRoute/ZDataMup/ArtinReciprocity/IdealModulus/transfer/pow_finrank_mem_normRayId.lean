import Mathlib
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.Defs
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.CoreId
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.mem_idealCoprimeGroupId_iff
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.count_map_eq_ramificationIdx_mul_count
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.transfer

open NK.CFTLib.ArtinReciprocityIdeal

/-- Coprimality to the base-changed modulus for a single prime ideal. -/
lemma fracCoprimeId_map_prime {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] {𝔪 : Ideal (𝓞 K)} {𝔭 : HeightOneSpectrum (𝓞 K)}
    (h𝔭 : ¬ DvdPrime 𝔪 𝔭) :
    FracCoprimeId (K := L) (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) 𝔪)
      (idealUnit (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) 𝔭.asIdeal)
        (Ideal.map_ne_bot_of_ne_bot 𝔭.ne_bot)) := by
  intro 𝓟 h𝓟
  show FractionalIdeal.count L 𝓟
    (((Ideal.map (algebraMap (𝓞 K) (𝓞 L)) 𝔭.asIdeal : Ideal (𝓞 L)) :
      FractionalIdeal (𝓞 L)⁰ L)) = 0
  rw [count_map_prime 𝔭 𝓟]
  rw [if_neg]
  intro hlies
  have h1 : 𝔪 ≤ Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) 𝓟.asIdeal :=
    (Ideal.map_le_iff_le_comap).mp h𝓟
  have h2 : Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) 𝓟.asIdeal = 𝔭.asIdeal := hlies.over.symm
  rw [h2] at h1
  exact h𝔭 h1

/-- The `[L:K]`-th power of a prime ideal is the relative norm of its base change. -/
lemma idealUnit_prime_pow_finrank_eq_relNorm {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (𝔭 : HeightOneSpectrum (𝓞 K)) :
    idealUnit 𝔭.asIdeal 𝔭.ne_bot ^ Module.finrank K L =
      idealUnit (Ideal.relNorm (𝓞 K) (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) 𝔭.asIdeal))
        (fun h => Ideal.map_ne_bot_of_ne_bot 𝔭.ne_bot ((Ideal.relNorm_eq_bot_iff).mp h)) := by
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, idealUnit, Units.val_mk0]
  rw [← FractionalIdeal.coeIdeal_pow]
  rw [show Module.finrank K L = Module.finrank (𝓞 K) (𝓞 L) from
    IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L]
  rw [← Ideal.relNorm_algebraMap (𝓞 L) 𝔭.asIdeal]

theorem pow_finrank_mem_normRayId {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) {A : NK.CFTLib.ArtinReciprocityIdeal.Frac K}
    (hA : NK.CFTLib.ArtinReciprocityIdeal.FracCoprimeId 𝔪 A) :
    A ^ Module.finrank K L ∈ NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K) (L := L) 𝔪 := by
  have hmem : A ∈ idealCoprimeGroupId 𝔪 :=
    (Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.mem_idealCoprimeGroupId_iff 𝔪 A).mpr hA
  let φ : Frac K →* Frac K :=
    { toFun := fun x => x ^ Module.finrank K L
      map_one' := one_pow _
      map_mul' := fun a b => mul_pow a b _ }
  have hle : idealCoprimeGroupId 𝔪 ≤ (normRayId (K := K) (L := L) 𝔪).comap φ := by
    rw [idealCoprimeGroupId, Subgroup.closure_le]
    rintro B ⟨𝔭, h𝔭, rfl⟩
    show idealUnit 𝔭.asIdeal 𝔭.ne_bot ^ Module.finrank K L ∈
      normRayId (K := K) (L := L) 𝔪
    rw [idealUnit_prime_pow_finrank_eq_relNorm 𝔭]
    exact Subgroup.subset_closure
      ⟨Ideal.map (algebraMap (𝓞 K) (𝓞 L)) 𝔭.asIdeal,
       Ideal.map_ne_bot_of_ne_bot 𝔭.ne_bot,
       fracCoprimeId_map_prime h𝔭, rfl⟩
  exact hle hmem

end Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.transfer
