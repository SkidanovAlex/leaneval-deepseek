import Mathlib
import Submission.Work.Tower.Chebotarev.Defs

namespace Work.Tower.Chebotarev

open NumberField Ideal
open scoped Classical nonZeroDivisors NumberField

/-- If `θ : 𝓞 K` generates the number field `K` over `ℚ`, then the conductor of `ℤ[θ]` in `𝓞 K`
is nonzero: there is a positive integer `N` with `N 𝓞 K ⊆ ℤ[θ]`.  The number field exponent
`RingOfIntegers.exponent θ` (the positive generator of the conductor intersected with `ℤ`)
divides such an `N`. -/
theorem exists_conductor_index {K : Type} [Field K] [NumberField K] (θ : 𝓞 K)
    (h : Algebra.adjoin ℚ ({(θ : K)} : Set K) = ⊤) :
    ∃ N : ℕ, 0 < N ∧ (N : 𝓞 K) ∈ conductor ℤ θ ∧ RingOfIntegers.exponent θ ∣ N := by
  -- Restate the generating hypothesis for the algebra map `𝓞 K → K`.
  have hgen : Algebra.adjoin ℚ ({algebraMap (𝓞 K) K θ} : Set K) = ⊤ := by
    simpa using h
  -- `f'(θ) ≠ 0` where `f = minpoly ℤ θ`, because `K/ℚ` is separable and `θ` generates it.
  have hf' : Polynomial.aeval θ (Polynomial.derivative (minpoly ℤ θ)) ≠ 0 := by
    have hAx : IsIntegral ℤ θ := θ.isIntegral
    have hne₁ : Polynomial.aeval (algebraMap (𝓞 K) K θ)
        (Polynomial.derivative (minpoly ℚ (algebraMap (𝓞 K) K θ))) ≠ 0 :=
      (Algebra.IsSeparable.isSeparable ℚ (algebraMap (𝓞 K) K θ)).aeval_derivative_ne_zero
        (minpoly.aeval ℚ (algebraMap (𝓞 K) K θ))
    have hmap : algebraMap (𝓞 K) K
        (Polynomial.aeval θ (Polynomial.derivative (minpoly ℤ θ))) ≠ 0 := by
      rwa [minpoly.isIntegrallyClosed_eq_field_fractions ℚ K hAx, Polynomial.derivative_map,
        Polynomial.aeval_map_algebraMap, Polynomial.aeval_algebraMap_apply] at hne₁
    exact fun hz => hmap (by rw [hz, map_zero])
  -- The conductor is nonzero, by the conductor–different identity
  -- `(conductor ℤ θ) * 𝔇 = (f'(θ))` together with `f'(θ) ≠ 0`.
  have hcond : conductor ℤ θ ≠ ⊥ := by
    intro hbot
    have key := conductor_mul_differentIdeal ℤ ℚ K θ hgen
    rw [hbot, bot_mul] at key
    exact hf' (span_singleton_eq_bot.mp key.symm)
  -- Hence `exponent θ = absNorm (under ℤ (conductor ℤ θ))` is positive.
  have hexp_ne : RingOfIntegers.exponent θ ≠ 0 := by
    have habs : Ideal.absNorm (conductor ℤ θ) ≠ 0 :=
      fun hz => hcond (Ideal.absNorm_eq_zero_iff.mp hz)
    have hdvd : Ideal.absNorm (Ideal.under ℤ (conductor ℤ θ)) ∣ Ideal.absNorm (conductor ℤ θ) :=
      Int.absNorm_under_dvd_absNorm _
    exact ne_zero_of_dvd_ne_zero habs hdvd
  -- `exponent θ` itself is the required `N`.
  exact ⟨RingOfIntegers.exponent θ, Nat.pos_of_ne_zero hexp_ne, Int.absNorm_under_mem _, dvd_rfl⟩

end Work.Tower.Chebotarev
