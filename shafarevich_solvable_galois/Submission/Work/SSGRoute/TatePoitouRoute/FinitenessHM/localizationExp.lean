import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local exponent of the different at a prime, via the localization at `P`

For a number field `K`, a rational prime `p` and a prime `P | p` of `𝓞 K`, let
`A := ℤ_(p) = Localization.AtPrime (span {p}) ℤ` and `B := 𝓞 K_P = Localization.AtPrime P (𝓞 K)`
be the localization at `P`, a discrete valuation ring.

`locExp p P hP hlies` is the exponent of the maximal ideal in the relative different of the
localization, `𝔡_{B/A}`.

The two facts needed to bound the *global* exponent `count_P (𝔡_{K/ℤ})` are

* `count_P (𝔡_{K/ℤ}) ≤ locExp p P …`, i.e. the exponent of `P` in the global different is the
  exponent of the maximal ideal in the localized different (equivalently: the different commutes
  with localisation at `P`);
* `locExp p P … ≤ e (1 + e · v_p(e))`, `e = e(P/p)`.

The second is the classical local bound; its proof goes through the `P`-adic completion
`L := K_P`, where the inertia field `ℚ_p(ζ)` exists (see the module docstring of
`differentIdeal_count_le_proved`), the totally ramified case is handled by the congruence argument
`aeval_derivative_sum` + `ordAt_sum_le`, and the exponent of the localized different agrees with
the exponent of the different of the completion.

**This replaces the false global "inertia field inside `K`" reduction**, see
`PING_exists_inertiaField_FALSE.md`.
-/

open scoped NumberField

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- **The local exponent of the different at `P`.**  The exponent of the maximal ideal in the
relative different of the localization `𝓞 K_P / ℤ_(p)`. -/
noncomputable def locExp (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 K)) (hP : P.IsPrime)
    (hlies : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))) : ℕ :=
  haveI hp : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsPrime :=
    (Ideal.span_singleton_prime
        (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p))
  haveI hP' : P.IsPrime := hP
  let A := Localization.AtPrime (R := ℤ) (Ideal.span ({(p : ℤ)} : Set ℤ))
  let B := Localization.AtPrime (R := 𝓞 K) P
  letI : Algebra A B := Localization.AtPrime.algebraOfLiesOver
    (A := ℤ) (B := 𝓞 K) (Ideal.span ({(p : ℤ)} : Set ℤ)) P
  haveI hTF : Module.IsTorsionFree A B := Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
    by_cases hr : r = 0
    · exact Or.inl hr
    · refine Or.inr ?_
      have h1 : algebraMap A B r * m = 0 := by
        rwa [Algebra.smul_def] at h
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 (by
          intro h3
          exact hr (FaithfulSMul.algebraMap_injective A B (by rw [h3, map_zero])))
      · exact h2
  (UniqueFactorizationMonoid.normalizedFactors (differentIdeal A B)).count
    (IsLocalRing.maximalIdeal B)

end

end Work.SSGRoute.TatePoitouRoute.FinitenessHM
