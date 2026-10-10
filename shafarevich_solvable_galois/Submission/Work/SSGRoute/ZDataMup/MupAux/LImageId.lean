import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RamificationInertia.Ramification
import Submission.NK.NUV2.ARL.transferSelfContained
import Submission.Work.SSGRoute.ZDataMup.MupAux.Base
import Submission.Work.SSGRoute.ZDataMup.MupAux.normRayId_le_of_algEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The image of `L` inside `Ω = L(ζ_M)`: norm ray and ramification (ideal moduli)

Ideal-modulus versions of the two transport statements of the Lang transfer:

* `normRayId_LImage_eq`: the norm ray of `L`, viewed inside `Ω = CyclotomicField M L`, is the norm
  ray of `L` (via `normRayId_le_of_algEquiv` and `LImageEquiv`);
* `isUnramified_LImageId`: `L`, viewed inside `Ω`, is unramified over `K` at the primes which are
  coprime to `𝔪` and to `(M)`.
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

/-- **The norm ray of `Ω/K` at the image `LΩ` of `L` is the norm ray of `L/K`.** -/
theorem normRayId_LImage_eq {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (M : ℕ) [NeZero M]
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) :
    NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K)
        (L := ↥(NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M)) 𝔪
      = NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K) (L := L) 𝔪 :=
  le_antisymm
    (normRayId_le_of_algEquiv (NK.CFTLib.ARLAlt.LImageEquiv (K := K) (L := L) M).symm 𝔪)
    (normRayId_le_of_algEquiv (NK.CFTLib.ARLAlt.LImageEquiv (K := K) (L := L) M) 𝔪)

/-- **`L`, viewed inside `Ω = L(ζ_M)`, is unramified at `p` over `K` whenever `p` is prime to `𝔪`
and to `(M)`.** -/
theorem isUnramified_LImageId {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (M : ℕ) [NeZero M]
    (𝔪 : Ideal (NumberField.RingOfIntegers K))
    (hram : NK.CFTLib.ArtinReciprocityIdeal.ContainsRamified (K := K) (L := L) 𝔪)
    (p : NK.Chebotarev.PrimeIdeal K) (hpm : ¬ NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 p)
    (hpM : (M : NumberField.RingOfIntegers K) ∉ p.asIdeal) :
    NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K)
      (L := ↥(NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M)) p := by
  set L' : IntermediateField K (CyclotomicField M L) :=
    NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M with hL'
  have hunrL : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p :=
    NK.CFTLib.ArtinReciprocityIdeal.isUnramified_of_not_dvdPrime (K := K) (L := L) hram hpm
  intro P' hP'
  have key : ∀ 𝔓 : NK.Chebotarev.PrimeIdeal (CyclotomicField M L),
      𝔓.asIdeal.LiesOver p.asIdeal →
      𝔓.asIdeal.ramificationIdx (𝓞 K) = 1 := by
    intro 𝔓 h𝔓
    set 𝔮 : HeightOneSpectrum (𝓞 L) := 𝔓.under (𝓞 L) with h𝔮
    have h𝔮lies : 𝔮.asIdeal.LiesOver p.asIdeal :=
      Ideal.LiesOver.mk (by rw [h𝔮]; exact h𝔓.over)
    have hM𝔮 : (M : 𝓞 L) ∉ 𝔮.asIdeal := by
      intro hmem
      refine hpM ?_
      rw [h𝔮lies.over]
      exact (Ideal.mem_under (𝓞 K) 𝔮.asIdeal).mpr (by rw [map_natCast]; exact hmem)
    have h1 : 𝔮.asIdeal.ramificationIdx (𝓞 K) = 1 := hunrL 𝔮 h𝔮lies
    have h2 : 𝔓.asIdeal.ramificationIdx (𝓞 L) = 1 :=
      NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension (k := L)
        (Ω := CyclotomicField M L) M 𝔮 hM𝔮 𝔓 (by rw [h𝔮]; exact ⟨rfl⟩)
    haveI : 𝔓.asIdeal.LiesOver 𝔮.asIdeal := by rw [h𝔮]; exact ⟨rfl⟩
    have htower := Ideal.ramificationIdx_tower (R := 𝓞 K) (S := 𝓞 L)
      (T := 𝓞 (CyclotomicField M L)) (q := 𝔮.asIdeal) (r := 𝔓.asIdeal)
    rw [h1, h2, one_mul] at htower
    exact htower
  obtain ⟨𝔓, h𝔓⟩ := Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
    (K := ↥L') (L := CyclotomicField M L) P'
  have h𝔓p : 𝔓.asIdeal.LiesOver p.asIdeal :=
    Ideal.LiesOver.trans (𝔓 := 𝔓.asIdeal) (P := P'.asIdeal) (p := p.asIdeal)
  have h1 : 𝔓.asIdeal.ramificationIdx (𝓞 K) = 1 := key 𝔓 h𝔓p
  haveI := h𝔓
  have htower := Ideal.ramificationIdx_tower (R := 𝓞 K) (S := 𝓞 ↥L')
    (T := 𝓞 (CyclotomicField M L)) (q := P'.asIdeal) (r := 𝔓.asIdeal)
  rw [h1] at htower
  exact Nat.eq_one_of_mul_eq_one_right htower.symm

end Work.SSGRoute.ZDataMup.MupAux
