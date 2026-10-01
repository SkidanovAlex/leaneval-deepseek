import Mathlib

/-!
# Vocabulary for the second moment of the truncated Möbius (sieve) symbol

This file collects the objects used in the proof of
`Work.ZeroDensity.Jutila.secondMomentSieveSymbol`:

* `rad n` — the radical of `n` (product of the distinct primes dividing `n`);
* `U y l = Σ_{m ≤ y, (m,l)=1} μ(m)/m` — the Möbius reciprocal sum over the integers
  coprime to `l`;
* `W t l = Σ_{l ∣ d ≤ t} μ(d)/d` — a diagonal entry of the Selberg diagonalization of the
  quadratic form below;
* `A t = Σ_{d,e ≤ t} μ(d) μ(e) / lcm(d,e)` — the Selberg quadratic form whose boundedness
  gives the `O(N)` bound for `Σ_{n ≤ N} M(n,t)²`.
-/

namespace Work.ZeroDensity.Jutila

open Finset

noncomputable section

/-- The radical of `n`: the product of the distinct primes dividing `n`. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

/-- `U y l = Σ_{m ≤ y, (m,l)=1} μ(m)/m`: the Möbius reciprocal sum restricted to the integers
coprime to `l`. -/
def U (y l : ℕ) : ℝ :=
  ∑ m ∈ (Finset.Icc 1 y).filter (fun m => Nat.Coprime m l),
    (ArithmeticFunction.moebius m : ℝ) / (m : ℝ)

/-- `W t l = Σ_{l ∣ d ≤ t} μ(d)/d`, the diagonal entry of the Selberg diagonalization of `A t`. -/
def W (t l : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 t).filter (fun d => l ∣ d),
    (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)

/-- The Selberg quadratic form `A t = Σ_{d,e ≤ t} μ(d) μ(e) / lcm(d,e)`. -/
def A (t : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 t, ∑ e ∈ Finset.Icc 1 t,
    (ArithmeticFunction.moebius d : ℝ) * (ArithmeticFunction.moebius e : ℝ) / (Nat.lcm d e : ℝ)

end

end Work.ZeroDensity.Jutila
