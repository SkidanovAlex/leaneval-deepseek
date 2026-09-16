import Mathlib
import Submission.ZetaWN
import Submission.PoleAsymptotic

open scoped BigOperators Topology SchwartzMap
open Filter

/-!
# ξ-truncation (P8 Lemma 4.1, step (iii)) — statement and decay input

The ξ-truncation of Lemma 4.1 isolates the pole contribution of the
per-coordinate integral.  With the Fourier representation (37)
(`Submission/ZFourier.lean`) the coordinate sum is
`∫∫ K(ξ,ξ′)·f(ξ)g(ξ′) dξ dξ′` where the ξ-dependent kernel `K` satisfies,
by the completed per-prime + product-tail + ζ_WN-ratio analysis
(`LocalFactorComparison`, `ProductTail`, `ZetaRatio`, `PoleAsymptotic`),
the pole asymptotic of P8 (41).  The truncation argument needs exactly three
inputs:

  (a) an explicit uniform modulus for the pole asymptotic over the cube
      `|ξ|, |ξ′| ≤ √(log x)` — the family hypothesis `UniformPoleAsymptotic`
      below (its *derivation* is the assembly of the commissioned commons
      lemmas L14 `riemannZeta_residue_uniform_bound`, L15
      `removedFactors_ratio_error`, L16 `primeFactors_log_over_prime_sum_le`
      with the pointwise `zetaWN_log_asymptotic_p8`: one-line substitution
      once all three are committed);
  (b) the crude bound `|K(ξ,ξ′)| ≤ C·log³x` for all real ξ, ξ′ (an
      independent sub-piece: `|K_p| ≤ 1 + 2/p^{1+1/log x} + 1/p^{1+2/log x}`
      over primes `p ∤ q`, compared with `ζ(1+1/log x)³ ≪ log³x` — needs a
      ζ(1+ε)-estimate campaign);
  (c) the rapid decay of the Schwartz transforms `f, g` — provided below:
      `schwartz_tail_decay` / `schwartz_tail_decay_normed` give
      `‖f ξ‖ ≤ C·T^{−k}` on `|ξ| ≥ T` for every `k`, which makes the
      integral outside the cube negligible (against the `log³x` crude bound
      by taking `k` large).

The final theorem of step (iii), once (a) and (b) are available, states:
for smooth compactly supported `F, G` with Schwartz transforms `f, g`, the
truncated double integral
`∫_{|ξ|,|ξ′| ≤ √log x} K(ξ,ξ′)·f(ξ)g(ξ′) − ∫_{cube} pole(ξ,ξ′)·f(ξ)g(ξ′)` is
`o(1)` (and the complement is negligible), with the pole integrand
`pole(ξ,ξ′) = B⁻¹·(N/φ(N))·(1+iξ)(1+iξ′)/(2+iξ+iξ′)` — whose integral is
`∫₀^∞ F′G′` by the final Fourier identity.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- **Family (uniform) pole asymptotic** — the hypothesis slot for the
ξ-truncation step.  For coprime moduli `W, N` (`q = WN`, `B(x) := φ(W)/W·log x`)
there is a vanishing error `ε(x) → 0` such that for every scale `x ≥ x₀` and
every Fourier variable `ξ` in the truncation cube `|ξ| ≤ √(log x)`,

    ‖ ζ_{WN}(1+(1+iξ)/log x)·(1+iξ)·N / (B(x)·φ(N)) − 1 ‖ ≤ ε(x) .

This is the uniform version of `zetaWN_log_asymptotic_p8`
(`Submission/PoleAsymptotic.lean`); it is obtained by composing the
quantitative residue bound (commons L14), the removed-Euler-factor estimate
(commons L15) and the prime-sum bound (commons L16). -/
noncomputable def UniformPoleAsymptotic (W N : ℕ) : Prop :=
  ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ,
    Tendsto ε atTop (𝓝 0) ∧
    ∀ x : ℕ, x₀ ≤ x → ∀ ξ : ℝ, |ξ| ≤ Real.sqrt (Real.log (x : ℝ)) →
      ‖zetaWN (W * N) (1 + logZ ξ x) * ((1 : ℂ) + ξ * Complex.I) * (N : ℂ) /
          ((((W.totient : ℂ) / (W : ℂ)) * (Real.log (x : ℝ) : ℂ)) * (N.totient : ℂ)) - 1‖ ≤
        ε x

/-- Rapid decay input (c): every Schwartz function `f : 𝓢(ℝ,ℂ)` satisfies a
pointwise polynomial decay `‖f x‖ ≤ C·|x|^{−k}` for `1 ≤ |x|` (from
`SchwartzMap.decay`). -/
theorem schwartz_pointwise_pow_decay (f : 𝓢(ℝ, ℂ)) (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ |x| → ‖f x‖ ≤ C / |x| ^ k := by
  rcases (SchwartzMap.decay f k 0) with ⟨C, hC0, hC⟩
  refine ⟨C, hC0, ?_⟩
  intro x hx
  have hxk : (0 : ℝ) < |x| ^ k := pow_pos (lt_of_lt_of_le zero_lt_one hx) k
  rw [le_div_iff₀ hxk]
  have h1 := hC x
  simpa [Real.norm_eq_abs, mul_comm, mul_left_comm, mul_assoc] using h1

/-- Rapid decay input (c), normalized at the cutoff: for `|x| ≥ T ≥ 1`,
`‖f x‖ ≤ C·T^{−k}`. -/
theorem schwartz_tail_decay_normed (f : 𝓢(ℝ, ℂ)) (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ x : ℝ, T ≤ |x| → ‖f x‖ ≤ C / T ^ k := by
  rcases (SchwartzMap.decay f k 0) with ⟨C, hC0, hC⟩
  refine ⟨C, hC0, ?_⟩
  intro T hT x hxT
  have hxk : (0 : ℝ) < T ^ k := pow_pos (lt_of_lt_of_le zero_lt_one hT) k
  rw [le_div_iff₀ hxk]
  have h1 := hC x
  have hle1 : T ^ k ≤ |x| ^ k := pow_le_pow_left₀ (by linarith : 0 ≤ T) hxT k
  have hle2 : ‖f x‖ * T ^ k ≤ ‖f x‖ * |x| ^ k :=
    mul_le_mul_of_nonneg_left hle1 (norm_nonneg (f x))
  have hmain : ‖f x‖ * |x| ^ k ≤ C := by
    simpa [Real.norm_eq_abs, mul_comm, mul_left_comm, mul_assoc] using h1
  exact hle2.trans hmain

end Commons.NumberTheory.MaynardSieve
