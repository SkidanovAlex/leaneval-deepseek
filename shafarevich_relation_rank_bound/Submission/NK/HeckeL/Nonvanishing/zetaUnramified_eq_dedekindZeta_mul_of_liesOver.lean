import Mathlib
import Submission.NK.HeckeL.Zeta
import Submission.NK.HeckeL.Nonvanishing.zetaUnramifiedK_eq_dedekindZeta_mul

namespace NK.HeckeL.Nonvanishing

open scoped BigOperators

/-- The Euler product of `L` over the primes not lying above any prime of the modulus `S` coincides
with the Euler product of `L` over the primes outside the finite set `T` of primes of `L` above `S`.

Indeed, by `hT` the two index sets are the same set of primes of `L`. -/
theorem zetaUnramified_eq_zetaUnramifiedK_of_liesOver {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (T : Finset (NK.HeckeL.PrimeIdeal L))
    (hT : ∀ 𝔮 : NK.HeckeL.PrimeIdeal L, 𝔮 ∈ T ↔ ∃ Q ∈ S, 𝔮.asIdeal.LiesOver Q.asIdeal)
    (s : ℝ) :
    NK.HeckeL.zetaUnramified K L S s = NK.HeckeL.zetaUnramifiedK L T s := by
  have hiff : ∀ 𝔮 : NK.HeckeL.PrimeIdeal L,
      (∀ Q ∈ S, ¬ 𝔮.asIdeal.LiesOver Q.asIdeal) ↔ 𝔮 ∉ T := by
    intro 𝔮
    constructor
    · intro h hmem
      obtain ⟨Q, hQS, hL⟩ := (hT 𝔮).mp hmem
      exact h Q hQS hL
    · intro h Q hQS hL
      exact h ((hT 𝔮).mpr ⟨Q, hQS, hL⟩)
  unfold NK.HeckeL.zetaUnramified NK.HeckeL.zetaUnramifiedK
  exact tprod_congr_subtype
    (fun 𝔮 : NK.HeckeL.PrimeIdeal L =>
      (1 - (((Ideal.absNorm 𝔮.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹) hiff

/-- **The Euler product of `L` outside the primes above the modulus `S`, expressed through the
Dedekind zeta function of `L`.**  If `T` is exactly the finite set of primes of `L` lying over a
prime of `S`, then for real `s > 1`

`∏_{𝔮 ∉ T} (1 - N𝔮^{-s})⁻¹ = ζ_L(s) · ∏_{𝔮 ∈ T} (1 - N𝔮^{-s})`. -/
theorem zetaUnramified_eq_dedekindZeta_mul_of_liesOver {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (T : Finset (NK.HeckeL.PrimeIdeal L))
    (hT : ∀ 𝔮 : NK.HeckeL.PrimeIdeal L, 𝔮 ∈ T ↔ ∃ Q ∈ S, 𝔮.asIdeal.LiesOver Q.asIdeal)
    {s : ℝ} (hs : 1 < s) :
    NK.HeckeL.zetaUnramified K L S s =
      ((NumberField.dedekindZeta L (s : ℂ)).re : ℂ) *
        ∏ 𝔮 ∈ T, (1 - (((Ideal.absNorm 𝔮.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)) := by
  rw [zetaUnramified_eq_zetaUnramifiedK_of_liesOver (K := K) (L := L) S T hT s]
  exact zetaUnramifiedK_eq_dedekindZeta_mul (K := L) T hs

end NK.HeckeL.Nonvanishing
