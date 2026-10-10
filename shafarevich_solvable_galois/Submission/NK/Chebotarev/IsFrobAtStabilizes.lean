import Mathlib.RingTheory.Frobenius
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.NK.Chebotarev.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Chebotarev

/-- **A Frobenius element fixes its own prime.**  If `σ` is an arithmetic Frobenius at a prime
`P` of `𝓞 L`, then the corresponding automorphism of the ring of integers preserves `P`.
Indeed, `IsFrobAt P σ` says `σ x ≡ x ^ #(𝓞 K / P ∩ 𝓞 K) (mod P)` for every `x : 𝓞 L`, which
means that the induced map on the residue field `𝓞 L ⧸ P` is the Frobenius `y ↦ y ^ q`; in
particular it is `𝓞 K`-linear and hence `Ideal.comap σ P = P`.  Since `galRestrict` is a ring
*equivalence* of `𝓞 L`, `Ideal.map σ P = Ideal.map σ (Ideal.comap σ P) = P`. -/
theorem IsFrobAtStabilizes {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {P : NK.Chebotarev.PrimeIdeal L} {σ : Gal(L/K)} (h : NK.Chebotarev.IsFrobAt P σ) :
    Ideal.map (galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) σ :
      NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L) P.asIdeal = P.asIdeal := by
  have hsurj : Function.Surjective
      (galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) σ :
        NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L) :=
    (galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) σ).surjective
  have hcomap : Ideal.comap
      (galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) σ :
        NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L) P.asIdeal = P.asIdeal :=
    h.comap_eq
  conv_lhs => rw [← hcomap]
  exact Ideal.map_comap_of_surjective _ hsurj P.asIdeal

end NK.Chebotarev
