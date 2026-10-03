/-
# `Submission.Work.FIArea6Hecke.heckeLSeries_zero_of_re_le_one`

**The `σ ≤ 1` half of *FI* (16.23)**: for a strict character `χ` mod `4d` and any `m : ℤ`, the Hecke
`L`-series `L(s,ψ) = ∑_n λ(n)n^{-s}` (`λ = heckeLam χ m`, `ψ(z) = χ(z)(z/|z|)^m`) vanishes for
`s.re ≤ 1`.

## Why this is the right statement

Mathlib's `LSeries f s = ∑' n, f n / n^s` is the *unconditional* `tsum`, i.e. it equals the
absolutely convergent value when the series converges and `0` otherwise
(`LSeries.eq_zero_of_not_LSeriesSummable`).  Hence

  `heckeLSeries χ m s = 0  ⟺  ¬ Summable (fun n => λ n / n^s)  ⟺  ∑_n ‖λ n‖ n^{-σ} = ∞`,  `σ = s.re`,

the last equivalence because summability of a complex series over `ℕ` is absolute summability.
So the content of the lemma is: **the abscissa of absolute convergence of the Hecke `L`-series is
`1`** — a genuine theorem, not a vacuity.

## The reduction performed here

`λ` is multiplicative, `λ n = 0` for even `n`, `λ q = 0` and `‖λ (q²)‖ = 1` for inert primes
`q ≡ 3 (4)`, while for a split prime `p ≡ 1 (4)` one has `λ p = ψ(𝔭) + ψ(𝔭̄)` with both terms of
modulus `1` unless `p ∣ 4d`.  Consequently the divergence `∑_n ‖λ n‖/n = ∞` is equivalent to the
divergence of the sum over the *split* primes,

  `∑_{p ≡ 1 (4)} ‖λ p‖ / p = ∞`

(the inert primes contribute the convergent `∑ 1/(q²-1)`, and for a split prime the whole local
block `∑_k ‖λ(p^k)‖/p^k` is finite — it is `≈ p^{-2}` exactly when `‖λ p‖ ≈ 0`).  The lemma below
performs the (purely formal) passage from that divergence to the vanishing of the `L`-series: it
needs no hypothesis on `χ` at all.

The remaining, *analytic*, statement — the divergence of `∑_{p ≡ 1 (4)} ‖λ p‖ / p` — is
`Work.FIArea6Hecke.heckeLam_prime_divergence` (proved in the sibling file).  Its content is the
non-vanishing of the Hecke `L`-function of the weight-`2m` Größencharakter
`δ(𝔭) = ψ(𝔭)/ψ(𝔭̄) = ψ(𝔭)²/ψ((p))` at `s = 1`: writing `‖λ p‖² = 2 + 2 Re δ(𝔭)` one has, with
`M(σ) = ∑_{p ≡ 1 (4)} p^{-σ} = ½ log(1/(σ-1)) + O(1)` (Mertens in AP mod `4`),

  `∑_{p ≡ 1 (4)} ‖λ p‖²/p^σ = 2 M(σ) + 2 Re ∑_{p ≡ 1 (4)} δ(𝔭)p^{-σ}
     = 2 M(σ) + log|L(σ,δ)| + O(1)`,

and the pointwise bound `‖λ p‖² ≥ 0` (`Re δ ≥ -1`, `|δ| = 1`) gives exactly
`log|L(σ,δ)| ≥ -M(σ) + O(1)`; the divergence therefore follows once `L(·,δ)` is analytic at
`s = 1` and non-zero there, which is Hecke's theorem (equivalently: Hecke's equidistribution of
the arguments of Gaussian primes / the prime number theorem in angular sectors of `ℚ(i)`).
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.Basic
import Submission.Work.FIArea6Hecke.heckeLam_prime_divergence

set_option autoImplicit false

namespace Work.FIArea6Hecke

open scoped BigOperators

/-- **The reduction.**  If the sum over the split primes of `‖λ p‖/p` diverges, then the Hecke
`L`-series of `(χ,m)` vanishes in `re s ≤ 1`.

Indeed, if the series converged at `s` then (by `Summable.indicator`) its restriction to the split
primes would be a summable nonnegative sequence, and for such a prime `p`

  `‖λ p‖ / p ≤ ‖λ p‖ / p^{s.re} = ‖λ p / p^s‖`

because `s.re ≤ 1` and `p ≥ 1`; contradiction. -/
lemma heckeLSeries_eq_zero_of_prime_divergence (chi : GaussianInt → ℂ) (m : ℤ)
    (hdiv : ¬ Summable (fun n : ℕ =>
      if n.Prime ∧ n % 4 = 1 then ‖Work.FIArea5.S16Hecke.heckeLam chi m n‖ / (n : ℝ) else 0))
    {s : ℂ} (hs : s.re ≤ 1) : Work.FIArea5.S16Hecke.heckeLSeries chi m s = 0 := by
  rw [Work.FIArea5.S16Hecke.heckeLSeries,
    LSeries_def₀ (Work.FIArea5.S16Hecke.heckeLam_zero chi m) s]
  refine tsum_eq_zero_of_not_summable ?_
  intro hsumm
  apply hdiv
  -- the norms of the terms of the series, restricted to the split primes
  have hind : Summable (fun n : ℕ =>
      ({n : ℕ | n.Prime ∧ n % 4 = 1} : Set ℕ).indicator
        (fun n => ‖Work.FIArea5.S16Hecke.heckeLam chi m n / ((n : ℂ) ^ s)‖) n) :=
    hsumm.norm.indicator {n : ℕ | n.Prime ∧ n % 4 = 1}
  have hnorm : Summable (fun n : ℕ =>
      if n.Prime ∧ n % 4 = 1 then
        ‖Work.FIArea5.S16Hecke.heckeLam chi m n / ((n : ℂ) ^ s)‖ else 0) :=
    hind.congr (fun n => by simp [Set.indicator_apply])
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hnorm
  · -- nonnegativity
    by_cases h : n.Prime ∧ n % 4 = 1
    · rw [if_pos h]
      exact div_nonneg (norm_nonneg _) (Nat.cast_nonneg n)
    · simp [h]
  · -- the termwise bound `‖λ n‖/n ≤ ‖λ n / n^s‖`
    by_cases h : n.Prime ∧ n % 4 = 1
    · have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h.1.pos
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_of_lt h.1.one_lt)
      have hle : ((n : ℝ) ^ s.re) ≤ (n : ℝ) := by
        simpa using Real.rpow_le_rpow_of_exponent_le h1 hs
      have hkey : ‖Work.FIArea5.S16Hecke.heckeLam chi m n / ((n : ℂ) ^ s)‖
          = ‖Work.FIArea5.S16Hecke.heckeLam chi m n‖ / ((n : ℝ) ^ s.re) := by
        rw [norm_div, Complex.norm_natCast_cpow_of_pos h.1.pos]
      simp only [h]
      rw [hkey]
      exact div_le_div_of_nonneg_left (norm_nonneg _) (Real.rpow_pos_of_pos hpos s.re) hle
    · simp [h]

end Work.FIArea6Hecke
