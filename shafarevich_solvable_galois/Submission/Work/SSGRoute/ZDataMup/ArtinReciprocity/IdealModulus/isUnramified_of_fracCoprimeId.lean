import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.Factorization
import Submission.NK.CFTLib.ArtinReciprocityIdeal.normRayLeKer
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `𝔮 ∤ 𝔪` for a prime below a prime of a modulus-coprime ideal implies unramifiedness

Let `L / K` be a finite Galois extension of number fields and `𝔪` an ideal modulus of `K` which
**contains every ramified prime** (`ContainsRamified 𝔪`).  If `I ≠ ⊥` is an ideal of `𝓞 L` coprime
to the extension `𝔪 𝓞 L` of `𝔪` (`FracCoprimeId (𝔪 𝓞 L) (idealUnit I hI)`) and `𝔮` is a prime of
`L` dividing `I` (`count L 𝔮 I ≠ 0`), then the prime `𝔭 := 𝔮 ∩ 𝓞 K` of `K` below `𝔮` is
unramified in `L / K`.

The mathematical content is one line: `𝔮 | I` and `gcd(I, 𝔪 𝓞 L) = 1` give `𝔮 ∤ 𝔪 𝓞 L`, i.e.
`¬ (𝔪 𝓞 L ≤ 𝔮)`;  since `𝔪 ≤ 𝔭` would imply `𝔪 𝓞 L ≤ 𝔭 𝓞 L ≤ 𝔮` (`𝔮` lies over `𝔭`), this shows
`𝔪 ⊄ 𝔭`, so by `ContainsRamified` the prime `𝔭` is unramified.  Formally, `ContainsRamified`
records unramifiedness as `Ideal.ramificationIdxIn 𝔭 (𝓞 L) = 1`, and the passage from that single
number to the definition `IsUnramified 𝔭` (all primes above `𝔭` have ramification index one) is
Hilbert's ramification theory in the Galois case
(`Ideal.ramificationIdxIn_eq_ramificationIdx`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus

/-- **A prime of `L` dividing an ideal coprime to `𝔪 𝓞 L` is unramified over `K`.** -/
theorem isUnramified_of_fracCoprimeId
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (𝔪 : Ideal (NumberField.RingOfIntegers K))
    (hram : NK.CFTLib.ArtinReciprocityIdeal.ContainsRamified (K := K) (L := L) 𝔪)
    (I : Ideal (NumberField.RingOfIntegers L)) (hI : I ≠ ⊥)
    (hcop : NK.CFTLib.ArtinReciprocityIdeal.FracCoprimeId (K := L)
      (Ideal.map (algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L)) 𝔪)
      (NK.CFTLib.ArtinReciprocityIdeal.idealUnit I hI))
    (𝔮 : NK.Chebotarev.PrimeIdeal L)
    (h𝔮 : FractionalIdeal.count L 𝔮
      (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers L)) L) ≠ 0) :
    NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L)
      (𝔮.under (NumberField.RingOfIntegers K)) := by
  -- `𝔮` divides `I`, so it cannot divide the extension `𝔪 𝓞 L` (to which `I` is coprime).
  have hnotmap : ¬ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) 𝔪 ≤ 𝔮.asIdeal) := by
    intro hle
    have h0 := hcop 𝔮 hle
    rw [NK.CFTLib.ArtinReciprocityIdeal.idealUnit, Units.val_mk0] at h0
    exact h𝔮 h0
  -- equivalently, the prime `𝔮 ∩ 𝓞 K` of `K` below `𝔮` does not divide `𝔪`.
  have hnotdvd : ¬ NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 (𝔮.under (𝓞 K)) := by
    intro hd
    apply hnotmap
    rw [Ideal.map_le_iff_le_comap]
    rw [NK.CFTLib.ArtinReciprocityIdeal.DvdPrime] at hd
    rwa [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_def] at hd
  -- hence `ContainsRamified` forces the ramification index (well defined in the Galois case) to be
  -- one.
  have heq : Ideal.ramificationIdxIn (𝔮.under (𝓞 K)).asIdeal (𝓞 L) = 1 := by
    by_contra h
    exact hnotdvd (hram (𝔮.under (𝓞 K)) h)
  intro P hP
  letI : MulSemiringAction (Gal(L/K)) (𝓞 L) :=
    IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  haveI : IsGaloisGroup (Gal(L/K)) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (Gal(L/K)) (𝓞 K) (𝓞 L) K L
  haveI : P.asIdeal.IsPrime := P.isPrime
  haveI : P.asIdeal.LiesOver (𝔮.under (𝓞 K)).asIdeal := hP
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (𝔮.under (𝓞 K)).asIdeal P.asIdeal (Gal(L/K))]
  exact heq

end Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus
