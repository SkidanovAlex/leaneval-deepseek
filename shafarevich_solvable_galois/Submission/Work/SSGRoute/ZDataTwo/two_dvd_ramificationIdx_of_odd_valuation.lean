import Mathlib.NumberTheory.RamificationInertia.Valuation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute.ZDataTwo

/-- **Ramification at a prime of odd valuation.**

Let `L/K` be a finite extension of number fields and let `β ∈ L` satisfy `β ^ 2 = b` for some
`b ∈ Kˣ`.  If `b` has odd `𝔭`-adic valuation at a height-one prime `𝔭` of `𝓞 K`, then every prime
`P` of `𝓞 L` lying over `𝔭` has even ramification index over `𝓞 K`.

The proof is the classical one.  Comparing the `𝔭`-adic valuation of `b` in `K` with the
`P`-adic valuation of `β` in `L` via `HeightOneSpectrum.valuation_liesOver` gives
`v_𝔭(b) ^ e = v_P(β) ^ 2`, where `e = P.ramificationIdx (𝓞 K)` is the ramification index.
Taking `WithZero.log` turns this into `e · v_𝔭(b) = 2 · v_P(β)`; since `v_𝔭(b)` is odd it is
coprime to `2`, so `2 ∣ e`. -/
theorem two_dvd_ramificationIdx_of_odd_valuation
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (b : Kˣ) (β : L) (hβ : β ^ 2 = algebraMap K L (b : K))
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    [P.asIdeal.LiesOver 𝔭.asIdeal]
    (hodd : Odd (-(𝔭.valuation K (b : K)).log)) :
    2 ∣ P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) := by
  haveI := P.isPrime
  -- Comparison of the two adic valuations: the ramification index is the exponent.
  have hvl := IsDedekindDomain.HeightOneSpectrum.valuation_liesOver L 𝔭 P (b : K)
  -- Replace the legacy ramification index `ramificationIdx'` by the new `ramificationIdx`.
  have heq : 𝔭.asIdeal.ramificationIdx' P.asIdeal =
      P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) :=
    Ideal.ramificationIdx'_eq_ramificationIdx 𝔭.asIdeal P.asIdeal 𝔭.ne_bot
  try rw [heq] at hvl
  -- The right-hand side is the valuation of `β ^ 2`.
  rw [← hβ, map_pow] at hvl
  -- Take logs: `e * v_𝔭(b) = 2 * v_P(β)`.
  have hlog := congrArg WithZero.log hvl
  rw [WithZero.log_pow, WithZero.log_pow, nsmul_eq_mul, nsmul_eq_mul] at hlog
  set c : ℤ := (𝔭.valuation K (b : K)).log with hc_def
  set d : ℤ := (P.valuation L β).log with hd_def
  -- `c` is odd, hence not divisible by `2`.
  have hc : ¬ (2 : ℤ) ∣ c := by
    intro hd
    obtain ⟨k, hk⟩ := hd
    obtain ⟨j, hj⟩ := hodd
    omega
  -- From `e * c = 2 * d` and `2 ∤ c` we deduce `2 ∣ e`.
  have h2 : (2 : ℤ) ∣ (P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) : ℤ) := by
    have : (2 : ℤ) ∣ (P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) : ℤ) * c :=
      ⟨d, hlog⟩
    rcases Int.prime_two.dvd_mul.mp this with h | h
    · exact h
    · exact absurd h hc
  exact Int.natCast_dvd_natCast.mp h2

end Work.SSGRoute.ZDataTwo
