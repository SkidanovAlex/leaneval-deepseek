import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Submission.Commons.NumberTheory.Zeta.primeFactors_log_over_prime_sum_le

namespace Commons.NumberTheory.Zeta

open scoped BigOperators

private lemma cpow_neg_one_sub_neg_mul (p : ℕ) (hp0 : (p : ℂ) ≠ 0) (z : ℂ) :
    (p : ℂ) ^ (-(1 + z)) - (p : ℂ)⁻¹ = (p : ℂ)⁻¹ * ((p : ℂ) ^ (-z) - 1) := by
  have hcpow : (p : ℂ) ^ (-(1 + z)) = (p : ℂ)⁻¹ * (p : ℂ) ^ (-z) := by
    calc
      (p : ℂ) ^ (-(1 + z)) = (p : ℂ) ^ ((-1 : ℂ) + (-z)) := by congr 1; ring
      _ = (p : ℂ) ^ (-1 : ℂ) * (p : ℂ) ^ (-z) := by
        rw [Complex.cpow_add (-1 : ℂ) (-z) hp0]
      _ = (p : ℂ)⁻¹ * (p : ℂ) ^ (-z) := by rw [Complex.cpow_neg_one]
  rw [hcpow]
  ring

private lemma denom_norm_eq (p : ℕ) (hp2 : 2 ≤ p) :
    ‖(1 : ℂ) - (p : ℂ)⁻¹‖ = 1 - (p : ℝ)⁻¹ := by
  have hcast : (1 : ℂ) - (p : ℂ)⁻¹ = ((1 : ℝ) - (p : ℝ)⁻¹ : ℝ) := by
    norm_num [Complex.ofReal_inv]
  rw [hcast]
  rw [Complex.norm_of_nonneg]
  have hpge1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hle : (p : ℝ)⁻¹ ≤ 1 := by
    rw [← one_div]
    simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hpge1)
  linarith

private lemma denom_norm_ge (p : ℕ) (hp2 : 2 ≤ p) : (1 / 2 : ℝ) ≤ ‖(1 : ℂ) - (p : ℂ)⁻¹‖ := by
  rw [denom_norm_eq p hp2]
  have hp2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hle : (p : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
    rw [← one_div]
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < (2 : ℝ)) hp2r
  linarith

/-- For a prime power base `p ≥ 2` with `‖z‖ log p ≤ 1`:
`‖p^{-(1+z)} − p^{-1}‖ ≤ 2‖z‖ (log p)/p`. -/
private lemma per_prime_diff (p : ℕ) (hp2 : 2 ≤ p) (z : ℂ)
    (hz : ‖z‖ * Real.log (p : ℝ) ≤ 1) :
    ‖(p : ℂ) ^ (-(1 + z)) - (p : ℂ)⁻¹‖ ≤ 2 * ‖z‖ * Real.log (p : ℝ) / (p : ℝ) := by
  have hp0n : p ≠ 0 := by omega
  have hp0c : (p : ℂ) ≠ 0 := by exact_mod_cast hp0n
  have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
  rw [cpow_neg_one_sub_neg_mul p hp0c z]
  rw [norm_mul]
  have hnormInv : ‖(p : ℂ)⁻¹‖ = (p : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  rw [hnormInv]
  have hlogc : Complex.log (p : ℂ) = (Real.log (p : ℝ) : ℂ) := by rw [Complex.natCast_log]
  have hpow : (p : ℂ) ^ (-z) = Complex.exp ((Real.log (p : ℝ) : ℂ) * (-z)) := by
    rw [Complex.cpow_def_of_ne_zero hp0c, hlogc]
  have hxnorm : ‖(Real.log (p : ℝ) : ℂ) * (-z)‖ = Real.log (p : ℝ) * ‖z‖ := by
    rw [norm_mul, Complex.norm_of_nonneg hlogp, norm_neg]
  have hxle : ‖(Real.log (p : ℝ) : ℂ) * (-z)‖ ≤ 1 := by
    rw [hxnorm, mul_comm]
    exact hz
  have hb1 : ‖(p : ℂ) ^ (-z) - 1‖ ≤ 2 * (Real.log (p : ℝ) * ‖z‖) := by
    rw [hpow]
    calc
      ‖Complex.exp ((Real.log (p : ℝ) : ℂ) * (-z)) - 1‖ ≤
          2 * ‖(Real.log (p : ℝ) : ℂ) * (-z)‖ := by
        exact Complex.norm_exp_sub_one_le hxle
      _ = 2 * (Real.log (p : ℝ) * ‖z‖) := by rw [hxnorm]
  have hp2r : 0 < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  calc
    (p : ℝ)⁻¹ * ‖(p : ℂ) ^ (-z) - 1‖ ≤ (p : ℝ)⁻¹ * (2 * (Real.log (p : ℝ) * ‖z‖)) := by
      exact mul_le_mul_of_nonneg_left hb1 (inv_nonneg.mpr hp2r.le)
    _ = 2 * ‖z‖ * Real.log (p : ℝ) / (p : ℝ) := by
      field_simp [hp2r.ne']

/-- Per-prime relative removed-factor error: with `|1 − p^{-1}| ≥ 1/2`,
`‖(1 − p^{-(1+z)})/(1 − p^{-1}) − 1‖ ≤ 4‖z‖(log p)/p`. -/
private lemma factor_ratio_bound (p : ℕ) (hp2 : 2 ≤ p) (z : ℂ)
    (hz : ‖z‖ * Real.log (p : ℝ) ≤ 1) :
    ‖(1 - (p : ℂ) ^ (-(1 + z))) / (1 - (p : ℂ)⁻¹) - 1‖ ≤
      4 * ‖z‖ * Real.log (p : ℝ) / (p : ℝ) := by
  let d : ℝ := 2 * ‖z‖ * Real.log (p : ℝ) / (p : ℝ)
  have hnum := per_prime_diff p hp2 z hz
  have hB : (1 / 2 : ℝ) ≤ ‖(1 : ℂ) - (p : ℂ)⁻¹‖ := denom_norm_ge p hp2
  have hb_ne : (1 : ℂ) - (p : ℂ)⁻¹ ≠ 0 := by
    intro h
    have : ‖(1 : ℂ) - (p : ℂ)⁻¹‖ = 0 := by rw [h]; simp
    linarith [hB, this]
  have hsplit : (1 - (p : ℂ) ^ (-(1 + z))) / (1 - (p : ℂ)⁻¹) - 1 =
      ((p : ℂ)⁻¹ - (p : ℂ) ^ (-(1 + z))) / (1 - (p : ℂ)⁻¹) := by
    field_simp [hb_ne]
    ring
  have hnorm : ‖(1 - (p : ℂ) ^ (-(1 + z))) / (1 - (p : ℂ)⁻¹) - 1‖ =
      ‖(p : ℂ) ^ (-(1 + z)) - (p : ℂ)⁻¹‖ / ‖(1 : ℂ) - (p : ℂ)⁻¹‖ := by
    rw [hsplit, norm_div]
    have hnumneg : (p : ℂ)⁻¹ - (p : ℂ) ^ (-(1 + z)) = -((p : ℂ) ^ (-(1 + z)) - (p : ℂ)⁻¹) := by ring
    rw [hnumneg, norm_neg]
  have hd0 : 0 ≤ d := by
    dsimp [d]
    positivity
  rw [hnorm]
  have hmain : ‖(p : ℂ) ^ (-(1 + z)) - (p : ℂ)⁻¹‖ / ‖(1 : ℂ) - (p : ℂ)⁻¹‖ ≤
      d / (1 / 2 : ℝ) := by
    exact div_le_div₀ hd0 hnum (by norm_num) hB
  calc
    ‖(p : ℂ) ^ (-(1 + z)) - (p : ℂ)⁻¹‖ / ‖(1 : ℂ) - (p : ℂ)⁻¹‖ ≤ d / (1 / 2 : ℝ) := hmain
    _ = 4 * ‖z‖ * Real.log (p : ℝ) / (p : ℝ) := by
      dsimp [d]
      field_simp
      ring

/-- Relative error of the removed Euler factors of the modified zeta
`ζ_q(1+z) = ζ(1+z)·∏_{p|q}(1−p^{−(1+z)})` at `z → 0`: comparing the factors
with their values at `s = 1`, `∏_{p|q}(1−p^{−1}) = φ(q)/q`.  For a prime
`p ≥ 2` dividing `q`, `‖p^{−(1+z)} − p^{−1}‖ ≤ 2‖z‖(log p)/p` (via
`cpow_def_of_ne_zero` + `Complex.norm_exp_sub_one_le`), so each relative
factor satisfies `‖(1−p^{−(1+z)})/(1−p^{−1}) − 1‖ ≤ 4‖z‖(log p)/p`
(`|1−p^{−1}| ≥ 1/2`); multiplying the `(1+u_p)` factors and using
`∏(1+|u_p|) ≤ exp(Σ|u_p|)` gives the bound below.  This is the
removed-factor input to the *uniform* pole asymptotic of `ζ_q` at the points
`1 + (1+iξ)/log x` (Polymath8a, "Variants of the Selberg sieve", (41)):
used with `q = WN` and `‖z‖ = (1+|ξ|)/log x`. -/
theorem removedFactors_ratio_error (q : ℕ) (hq : q ≠ 0) (z : ℂ)
    (hz : ∀ p ∈ q.primeFactors, ‖z‖ * Real.log (p : ℝ) ≤ 1) :
    ‖(∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-(1 + z)))) /
        (∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹)) - 1‖ ≤
      Real.exp (∑ p ∈ q.primeFactors, 4 * ‖z‖ * Real.log (p : ℝ) / (p : ℝ)) - 1 := by
  classical
  let S : Finset ℕ := q.primeFactors
  let a : ℕ → ℂ := fun p => 1 - (p : ℂ) ^ (-(1 + z))
  let b : ℕ → ℂ := fun p => 1 - (p : ℂ)⁻¹
  let u : ℕ → ℂ := fun p => a p / b p - 1
  have huf : ∀ p, a p / b p = 1 + u p := by
    intro p
    dsimp [u]
    ring
  have hprod : (∏ p ∈ S, a p) / (∏ p ∈ S, b p) = ∏ p ∈ S, (1 + u p) := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    exact huf p
  have hper : ∀ p ∈ S, ‖u p‖ ≤ 4 * ‖z‖ * Real.log (p : ℝ) / (p : ℝ) := by
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors (by simpa [S] using hp)
    have hp2 : 2 ≤ p := hpprime.two_le
    exact factor_ratio_bound p hp2 z (hz p (by simpa [S] using hp))
  have hstep1 : ‖(∏ p ∈ S, a p) / (∏ p ∈ S, b p) - 1‖ ≤
      Real.exp (∑ p ∈ S, ‖u p‖) - 1 := by
    rw [hprod]
    exact S.norm_prod_one_add_sub_one_le u
  have hsum : (∑ p ∈ S, ‖u p‖) ≤ ∑ p ∈ S, 4 * ‖z‖ * Real.log (p : ℝ) / (p : ℝ) := by
    exact Finset.sum_le_sum hper
  have hexp : Real.exp (∑ p ∈ S, ‖u p‖) ≤
      Real.exp (∑ p ∈ S, 4 * ‖z‖ * Real.log (p : ℝ) / (p : ℝ)) := by
    exact Real.exp_le_exp.mpr hsum
  calc
    ‖(∏ p ∈ S, a p) / (∏ p ∈ S, b p) - 1‖ ≤
        Real.exp (∑ p ∈ S, ‖u p‖) - 1 := hstep1
    _ ≤ Real.exp (∑ p ∈ S, 4 * ‖z‖ * Real.log (p : ℝ) / (p : ℝ)) - 1 := by
      exact sub_le_sub_right hexp 1

end Commons.NumberTheory.Zeta