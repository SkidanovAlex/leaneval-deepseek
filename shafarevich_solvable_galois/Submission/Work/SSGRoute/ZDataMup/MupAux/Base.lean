import Mathlib.NumberTheory.RamificationInertia.Galois
import Submission.NK.CFTLib.ArtinReciprocityIdeal.frobAtPrime_prod_relNorm_eq_one
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary base lemmas for the ideal-modulus Lang conductor (MupAux lane)

This module collects the small dictionary lemmas shared by the pieces of the ideal-modulus
version of Lang's norm index formula (`langCyclicRelIndexId`).

The main content is the bridge between the two formulations of "unramified": `IsUnramified 𝔭`
(quoted at a prime of `L` above `𝔭`) and `𝔭.asIdeal.ramificationIdxIn (𝓞 L) = 1` — the form in
which `ContainsRamified 𝔪` is stated.  The bridge
`isUnramified_iff_ramificationIdxIn_eq_one` already exists in
`Submission.NK.CFTLib.ArtinReciprocityIdeal.kernelLe_of_auxField`, but that module transitively
imports the ℕ-modulus `adjIdMod`, which collides with the ideal-modulus `adjIdMod` of
`IdealModulus/AdjustId.lean`; we reproduce the short proof here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.ArtinReciprocityIdeal

/-- **`IsUnramified` and `ramificationIdxIn = 1` agree** for a finite Galois extension of number
fields.  (Copy of `isUnramified_iff_ramificationIdxIn_eq_one` from
`kernelLe_of_auxField.lean`, kept here to avoid the `adjIdMod` name collision.) -/
theorem isUnramified_iff_ramificationIdxIn_eq_one_Id {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : NK.Chebotarev.PrimeIdeal K) :
    IsUnramified (K := K) (L := L) p ↔
      p.asIdeal.ramificationIdxIn (𝓞 L) = 1 := by
  classical
  letI hMSA : MulSemiringAction (L ≃ₐ[K] L) (𝓞 L) :=
    IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  haveI hGG : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  constructor
  · intro hunr
    obtain ⟨Q, hQ⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := L) p
    haveI : Q.asIdeal.IsPrime := Q.isPrime
    haveI : Q.asIdeal.LiesOver p.asIdeal := hQ
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal Q.asIdeal (L ≃ₐ[K] L)]
    exact hunr Q hQ
  · intro h Q hQ
    haveI : Q.asIdeal.IsPrime := Q.isPrime
    haveI : Q.asIdeal.LiesOver p.asIdeal := hQ
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal Q.asIdeal (L ≃ₐ[K] L)]
    exact h

/-- **A prime not dividing `𝔪` is unramified**, when `𝔪` contains all the ramified primes. -/
theorem isUnramified_of_not_dvdPrime {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {𝔪 : Ideal (𝓞 K)}
    (hram : ContainsRamified (K := K) (L := L) 𝔪) {𝔭 : NK.Chebotarev.PrimeIdeal K}
    (h𝔭 : ¬ DvdPrime 𝔪 𝔭) : IsUnramified (K := K) (L := L) 𝔭 := by
  rw [isUnramified_iff_ramificationIdxIn_eq_one_Id (K := K) (L := L) 𝔭]
  by_contra h
  exact h𝔭 (hram 𝔭 h)

end NK.CFTLib.ArtinReciprocityIdeal
