import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

namespace Commons.Analysis.Nonarchimedean

/-- If `exp` is, on the ball of radius `exp (-M)`, given by the exponential series
`∑ x^n / n!`, then every continuous ring automorphism `τ` of the adic completion which
preserves the valuation commutes with `exp` on that ball.

The proof is formal: `τ` fixes the rational numbers (hence all the factorials), so the
partial sums of the series for `τ x` are the images under `τ` of the partial sums of the
series for `x`; by continuity of `τ` the limit is `τ (exp x)`, and by uniqueness of limits
this equals `exp (τ x)`. -/
theorem exp_map_ringEquiv {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (M : ℕ) (exp : v.adicCompletion K → v.adicCompletion K)
    (hconv : ∀ x : v.adicCompletion K,
      Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) x ≤
          (WithZero.exp (-(M : ℤ)) : WithZero (Multiplicative ℤ)) →
        HasSum (fun n : ℕ => x ^ n / ((n.factorial : ℕ) : v.adicCompletion K)) (exp x))
    (τ : v.adicCompletion K ≃+* v.adicCompletion K) (hτc : Continuous τ)
    (hτv : ∀ x : v.adicCompletion K,
      Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (τ x) =
        Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) x)
    (x : v.adicCompletion K)
    (hx : Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) x ≤
          (WithZero.exp (-(M : ℤ)) : WithZero (Multiplicative ℤ))) :
    τ (exp x) = exp (τ x) := by
  -- `τ x` is again in the ball of convergence, by valuation preservation
  have hxτ : Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (τ x) ≤
      (WithZero.exp (-(M : ℤ)) : WithZero (Multiplicative ℤ)) := by
    rw [hτv x]; exact hx
  -- the exponential series of `τ x` converges to `exp (τ x)`
  have h1 : HasSum (fun n : ℕ => (τ x) ^ n / ((n.factorial : ℕ) : v.adicCompletion K))
      (exp (τ x)) := hconv (τ x) hxτ
  -- pushing the exponential series of `x` through the continuous ring automorphism `τ`
  have h2 : HasSum (fun n : ℕ => (τ x) ^ n / ((n.factorial : ℕ) : v.adicCompletion K))
      (τ (exp x)) := by
    have hmap : HasSum
        (fun n : ℕ => τ (x ^ n / ((n.factorial : ℕ) : v.adicCompletion K))) (τ (exp x)) :=
      (hconv x hx).map τ hτc
    simpa only [map_div₀, map_pow, map_natCast] using hmap
  -- both series have the same terms, so their sums agree
  exact (h1.unique h2).symm

end Commons.Analysis.Nonarchimedean