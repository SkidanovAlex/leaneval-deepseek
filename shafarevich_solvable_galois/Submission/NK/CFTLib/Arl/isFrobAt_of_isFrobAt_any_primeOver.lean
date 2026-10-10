import Mathlib.NumberTheory.RamificationInertia.Galois
import Submission.NK.CFTLib.Arl.Defs
import Submission.NK.Chebotarev.IsFrobAtConj
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.CFTLib.Arl

/-- **The Frobenius element at a prime above `𝔭` does not depend on the prime** when the
extension is abelian.

Let `L/K` be a finite abelian Galois extension of number fields, `𝔭` a prime of `𝓞 K` and
`𝔓₀, 𝔓` two primes of `𝓞 L` above `𝔭`.  If `g` is a Frobenius at `𝔓₀`, then `g` is a Frobenius
at `𝔓`.

The proof is the standard one: the Galois group acts transitively on the primes above `𝔭`, so
there is `σ` with `σ • 𝔓₀ = 𝔓`; equivariance of the Frobenius (`IsFrobAtConj`) makes
`σ * g * σ⁻¹` a Frobenius at `𝔓`; and in an abelian group `σ * g * σ⁻¹ = g`. -/
theorem isFrobAt_of_isFrobAt_any_primeOver {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    {𝔭 : NK.Chebotarev.PrimeIdeal K} {𝔓₀ 𝔓 : NK.Chebotarev.PrimeIdeal L}
    (h𝔓₀ : 𝔓₀.asIdeal.LiesOver 𝔭.asIdeal) (h𝔓 : 𝔓.asIdeal.LiesOver 𝔭.asIdeal)
    {g : Gal(L/K)} (hg : NK.Chebotarev.IsFrobAt 𝔓₀ g) : NK.Chebotarev.IsFrobAt 𝔓 g := by
  -- The Galois group acts transitively on the primes above `𝔭`: there is `σ` with `σ • 𝔓₀ = 𝔓`.
  obtain ⟨σ, hσ⟩ := Ideal.exists_comap_galRestrict_eq (NumberField.RingOfIntegers K) K L
    (NumberField.RingOfIntegers L) (p := 𝔭.asIdeal) (P₁ := 𝔓.asIdeal) (P₂ := 𝔓₀.asIdeal)
    ⟨𝔓.2, h𝔓⟩ ⟨𝔓₀.2, h𝔓₀⟩
  -- Since `galRestrict σ` is bijective, taking images turns the contraction back into `𝔓₀`.
  have hmap : Ideal.map (galRestrict (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L) σ :
        NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L) 𝔓₀.asIdeal = 𝔓.asIdeal := by
    rw [← hσ]
    exact Ideal.map_comap_of_surjective _ (galRestrict (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L) σ).surjective 𝔓.asIdeal
  -- This is exactly the statement that `σ • 𝔓₀ = 𝔓` for the action on `PrimeIdeal L`.
  have hsmul : σ • 𝔓₀ = 𝔓 := IsDedekindDomain.HeightOneSpectrum.ext hmap
  -- Equivariance of the Frobenius: `σ * g * σ⁻¹` is a Frobenius at `σ • 𝔓₀ = 𝔓`.
  have hconj : NK.Chebotarev.IsFrobAt (σ • 𝔓₀) (σ * g * σ⁻¹) :=
    NK.Chebotarev.IsFrobAtConj hg
  rw [hsmul] at hconj
  -- In an abelian group the conjugate is `g` itself.
  have hfix : σ * g * σ⁻¹ = g := by
    rw [hcomm σ g, mul_assoc, mul_inv_cancel, mul_one]
  rwa [hfix] at hconj

end NK.CFTLib.Arl
