import Mathlib
import Submission.NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension
import Submission.NK.CFTLib.ARL.artinReciprocity_cyclotomic
import Submission.NK.CFTLib.ArtinReciprocityIdeal.kernelLe_of_auxField
import Submission.NK.CFTLib.ARL.transfer_of_auxField
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The two elementary leaves of `ArtinReciprocity/productFormula_cyclotomic`

`LTRecFamCrux.cellId` and `LTRecFamCrux.CyclotomicCellId` use exactly two lemmas of the module
`Work.SSGRoute.ZDataMup.ArtinReciprocity.productFormula_cyclotomic`:
`isUnramifiedIn_of_ramificationIdxIn_eq_one` and
`ramificationIdxIn_eq_one_of_notMem_span_cyclotomic`.  That module, however, also imports
`localGlobalMap_productFormula`, which (currently) imports `CycleFromReciprocityModulus`, which
imports the cell `kernelLeId` — an *import cycle*: `cellId → productFormula_cyclotomic →
localGlobalMap_productFormula → CycleFromReciprocityModulus → cyclicCaseStatement_ramifiedSupport →
kernelLeId → cellId`.

This file re-provides the two leaves with a clean import list, breaking the cycle for the clean
copy of the crux cone under `LTRecFamCrux`.  The statements and the namespace are those of the
original module.
-/

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity

open NumberField IsDedekindDomain
open scoped NumberField

/-- **`Ideal.ramificationIdxIn` and `NK.HeckeL.IsUnramifiedIn` agree.**
If the relative ramification index of `p` is one, then every prime of `𝓞 L` above `p` has
ramification index one over `𝓞 K`: `Ideal.ramificationIdxIn` is (for a Galois extension) the
ramification index of *any* prime above `p`, by `Ideal.ramificationIdxIn_eq_ramificationIdx`. -/
theorem isUnramifiedIn_of_ramificationIdxIn_eq_one {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h : Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) = 1) :
    NK.HeckeL.IsUnramifiedIn (K := K) (L := L) p := by
  intro q hq
  haveI : q.asIdeal.IsPrime := q.isPrime
  haveI : q.asIdeal.LiesOver p.asIdeal := hq
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers K)
    (B := NumberField.RingOfIntegers L) p.asIdeal q.asIdeal (Gal(L/K))]
  exact h

/-- **The ramification hypothesis at the modulus `n` for a cyclotomic extension.**
Every prime of `𝓞 K` not dividing `(n)` has relative ramification index one in `K(ζ_n) = L`
(`NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension`, the classical fact that the only primes
ramifying in a cyclotomic extension divide `n`). -/
theorem ramificationIdxIn_eq_one_of_notMem_span_cyclotomic
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} K L]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hp : (n : NumberField.RingOfIntegers K) ∉ p.asIdeal) :
    Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) = 1 := by
  have hunr := NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension (k := K) (Ω := L) n p hp
  obtain ⟨P, hP⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := L) p
  haveI : P.asIdeal.IsPrime := P.isPrime
  haveI : P.asIdeal.LiesOver p.asIdeal := hP
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers K)
    (B := NumberField.RingOfIntegers L) p.asIdeal P.asIdeal (Gal(L/K))]
  exact hunr P hP

end Work.SSGRoute.ZDataMup.ArtinReciprocity
