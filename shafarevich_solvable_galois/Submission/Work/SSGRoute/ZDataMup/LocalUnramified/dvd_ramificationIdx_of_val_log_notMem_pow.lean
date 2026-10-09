import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute.ZDataMup.LocalUnramified

/-- **The ramification index is divisible by `p` at a prime of `𝔭`-valuation not divisible by
`p`.**

Let `L/K` be a finite extension of number fields and let `β ∈ L` satisfy `β ^ p = b` for some
`b ∈ Kˣ`.  If the `𝔭`-adic valuation of `b` (for a height one prime `𝔭` of `𝓞 K`) is not divisible
by `p`, then every prime `P` of `𝓞 L` above `𝔭` has ramification index over `𝓞 K` divisible by `p`.

The proof is the classical one.  Mathlib's `HeightOneSpectrum.valuation_liesOver` compares the
`𝔭`-adic valuation of `b` in `K` with the `P`-adic valuation of `β` in `L` (with the legacy index
`ramificationIdx'` replaced by `ramificationIdx`), giving
`v_𝔭(b) ^ e = v_P(β) ^ p` where `e = P.ramificationIdx (𝓞 K)`.  Taking `WithZero.log` turns this
into `e · v_𝔭(b) = p · v_P(β)`; since `p ∤ v_𝔭(b)` and `p` is prime, `p ∣ e`. -/
theorem dvd_ramificationIdx_of_val_log_notMem_pow
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (p : ℕ) (hp : p.Prime) (b : Kˣ) (β : L) (hβ : β ^ p = algebraMap K L (b : K))
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    [P.asIdeal.LiesOver 𝔭.asIdeal]
    (h : ¬ (p : ℤ) ∣ (𝔭.valuation K (b : K)).log) :
    p ∣ P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) := by
  haveI := P.isPrime
  -- Comparison of the two adic valuations: the ramification index is the exponent.
  have hvl := IsDedekindDomain.HeightOneSpectrum.valuation_liesOver L 𝔭 P (b : K)
  -- Replace the legacy ramification index `ramificationIdx'` by the new `ramificationIdx`.
  have heq : 𝔭.asIdeal.ramificationIdx' P.asIdeal =
      P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) :=
    Ideal.ramificationIdx'_eq_ramificationIdx 𝔭.asIdeal P.asIdeal 𝔭.ne_bot
  try rw [heq] at hvl
  -- The right-hand side is the valuation of `β ^ p`.
  rw [← hβ, map_pow] at hvl
  -- Take logs: `e * v_𝔭(b) = p * v_P(β)`.
  have hlog := congrArg WithZero.log hvl
  set c : ℤ := (𝔭.valuation K (b : K)).log with hc_def
  set d : ℤ := (P.valuation L β).log with hd_def
  rw [WithZero.log_pow, WithZero.log_pow, nsmul_eq_mul, nsmul_eq_mul] at hlog
  -- `p` is a prime of `ℤ`.
  have hpz : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  -- `p` divides `e * c` because `e * c = p * d`.
  have hpc : (p : ℤ) ∣ ((P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) : ℕ) : ℤ) * c := by
    rw [hlog]
    exact dvd_mul_right _ _
  rcases hpz.dvd_mul.mp hpc with h' | h'
  · exact Int.natCast_dvd_natCast.mp h'
  · exact absurd h' h

end Work.SSGRoute.ZDataMup.LocalUnramified
