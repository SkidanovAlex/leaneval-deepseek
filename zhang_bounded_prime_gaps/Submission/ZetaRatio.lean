import Mathlib
import Submission.ZetaWN
import Submission.LocalFactorComparison

open scoped BigOperators Topology
open Filter

/-!
# P8 Lemma 4.1 (ii): the ζ_WN-ratio identification of the per-coordinate factors

With the per-prime comparison (P8 (40), `Submission.LocalFactorComparison`) and
the `1 + o(1)` product tail (`Submission.ProductTail`) in place, the remaining
identification of Lemma 4.1(ii) is: the Euler product over the primes
`p ∤ q` (`q = WN`) of the per-coordinate ratio factors

    ρ_p := (1−p^{−1−a})(1−p^{−1−b}) / (1−p^{−1−a−b})        (Re a, Re b > 0)

equals the modified-zeta ratio

    ∏_{p∤q} ρ_p  =  ζ_q(1+a+b) / (ζ_q(1+a) · ζ_q(1+b)),      ζ_q = ζ_WN

(`zetaWN`, defined meromorphically in `Submission.ZetaWN`, equal to the Euler
product `∏_{p∤q}(1−p⁻ˢ)⁻¹` for `Re s > 1`).  Concretely, as a limit over
finite prime ranges `p < n` with `p ∤ q` (the style of
`zetaWN_eulerProduct`):

    `eulerRatioZetaWN q hq ha hb` :
      lim_n ∏_{p<n, p∤q} ρ_p = ζ_q(1+a+b) / (ζ_q(1+a)·ζ_q(1+b)).

This is the exact object into which the per-coordinate divisor sums
`Z(F,G)` factor once the Fourier representation (P8 (37)) is substituted; the
multiplication over the `k` coordinates is a finite product of these limits
(`Fintype`/`prod_comm`), handled when the consumer statement is written.

Contents (all kernel-verified, no `sorry`): `zetaWN_ne_zero_of_one_le_re`
(non-vanishing of `ζ_q` on `Re s ≥ 1`, needed to divide by `ζ_q(1+a)`,
`ζ_q(1+b)`), `eulerProduct_inv_zetaWN` (the inverted Euler product
`∏_{p∤q}(1−p⁻ˢ) → ζ_q(s)⁻¹`), and the main `eulerRatioZetaWN`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- `1 − p⁻ˢ ≠ 0` already for `1 ≤ s.re` (`‖p⁻ˢ‖ ≤ 1/2` for `p ≥ 2`). -/
lemma one_sub_cpow_ne_zero_of_one_le_re {p : ℕ} {s : ℂ} (hp2 : 2 ≤ p)
    (hs : 1 ≤ s.re) :
    (1 - (p : ℂ) ^ (-s)) ≠ 0 := by
  intro hz
  have hEq : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp hz).symm
  have hn := norm_cpow_neg_le_inv (p := p) hp2 (s := s) hs
  have h12 : ‖(p : ℂ) ^ (-s)‖ ≤ (1 / 2 : ℝ) := by
    have hinv : (p : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
      rw [one_div]
      exact (inv_le_inv₀ (by positivity : 0 < (p : ℝ)) (by norm_num)).mpr
        (by exact_mod_cast hp2)
    exact hn.trans hinv
  rw [hEq] at h12
  norm_num at h12

/-- `ζ_q(s) ≠ 0` for `1 ≤ s.re` (Riemann zeta is non-zero on `Re s ≥ 1` and
the finitely many removed `p | q` Euler factors are non-zero). -/
theorem zetaWN_ne_zero_of_one_le_re (q : ℕ) {s : ℂ} (hs : 1 ≤ s.re) :
    zetaWN q s ≠ 0 := by
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs
  have hfac : (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun p hp =>
      one_sub_cpow_ne_zero_of_one_le_re
        (Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hp)) hs)
  simpa [zetaWN] using mul_ne_zero hζ hfac

/-- The inverted Euler product: `∏_{p∤q}(1 − p⁻ˢ) → ζ_q(s)⁻¹` for `Re s > 1`
(inverted from `zetaWN_eulerProduct`). -/
theorem eulerProduct_inv_zetaWN (q : ℕ) (hq : q ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun n : ℕ => ∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q),
        (1 - (p : ℂ) ^ (-s)))
      atTop (𝓝 (zetaWN q s)⁻¹) := by
  have hmain : Tendsto (fun n : ℕ => ∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q),
        (1 - (p : ℂ) ^ (-s))⁻¹) atTop (𝓝 (zetaWN q s)) :=
    zetaWN_eulerProduct q hq (s := s) hs
  have hz : zetaWN q s ≠ 0 := zetaWN_ne_zero_of_one_le_re q (le_of_lt hs)
  have hinv := hmain.inv₀ hz
  simpa [Finset.prod_inv_distrib] using hinv

/-- **The ζ_WN-ratio identification (per coordinate pair `(a,b)`).**
For `q ≠ 0` and `Re a, Re b > 0`,

    lim_n  ∏_{p < n, p ∤ q} (1−p^{−1−a})(1−p^{−1−b})/(1−p^{−1−a−b})
        = ζ_q(1+a+b) / (ζ_q(1+a) · ζ_q(1+b)) .
-/
theorem eulerRatioZetaWN (q : ℕ) (hq : q ≠ 0) {a b : ℂ} (ha : 0 < a.re)
    (hb : 0 < b.re) :
    Tendsto (fun n : ℕ => ∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q),
        (1 - (p : ℂ) ^ (-(1 + a))) * (1 - (p : ℂ) ^ (-(1 + b))) *
          (1 - (p : ℂ) ^ (-(1 + a + b)))⁻¹)
      atTop (𝓝 (zetaWN q (1 + a + b) / (zetaWN q (1 + a) * zetaWN q (1 + b)))) := by
  classical
  let S : ℕ → Finset ℕ := fun n => (n.primesBelow).filter (fun p => ¬ p ∣ q)
  have hs1 : 1 < (1 + a).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith
  have hs2 : 1 < (1 + b).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith
  have hs3 : 1 < (1 + a + b).re := by
    rw [Complex.add_re, Complex.add_re, Complex.one_re]
    linarith
  let u : ℕ → ℂ := fun p => (1 - (p : ℂ) ^ (-(1 + a)))
  let v : ℕ → ℂ := fun p => (1 - (p : ℂ) ^ (-(1 + b)))
  let w : ℕ → ℂ := fun p => (1 - (p : ℂ) ^ (-(1 + a + b)))⁻¹
  have hU : Tendsto (fun n => ∏ p ∈ S n, u p) atTop
      (𝓝 (zetaWN q (1 + a))⁻¹) := by
    dsimp [S, u]
    exact eulerProduct_inv_zetaWN q hq (s := 1 + a) hs1
  have hV : Tendsto (fun n => ∏ p ∈ S n, v p) atTop
      (𝓝 (zetaWN q (1 + b))⁻¹) := by
    dsimp [S, v]
    exact eulerProduct_inv_zetaWN q hq (s := 1 + b) hs2
  have hW : Tendsto (fun n => ∏ p ∈ S n, w p) atTop
      (𝓝 (zetaWN q (1 + a + b))) := by
    dsimp [S, w]
    exact zetaWN_eulerProduct q hq (s := 1 + a + b) hs3
  have hUVW : Tendsto (fun n => (∏ p ∈ S n, u p) * (∏ p ∈ S n, v p) *
        (∏ p ∈ S n, w p)) atTop
      (𝓝 ((zetaWN q (1 + a))⁻¹ * (zetaWN q (1 + b))⁻¹ * zetaWN q (1 + a + b))) := by
    exact (hU.mul hV).mul hW
  have hpoint : (fun n : ℕ => ∏ p ∈ S n, u p * v p * w p) =
      fun n : ℕ => (∏ p ∈ S n, u p) * (∏ p ∈ S n, v p) * ∏ p ∈ S n, w p := by
    funext n
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hmain : Tendsto (fun n : ℕ => ∏ p ∈ S n, u p * v p * w p) atTop
      (𝓝 ((zetaWN q (1 + a))⁻¹ * (zetaWN q (1 + b))⁻¹ * zetaWN q (1 + a + b))) := by
    simpa [hpoint] using hUVW
  have hz1 : zetaWN q (1 + a) ≠ 0 := zetaWN_ne_zero_of_one_le_re q (by
    rw [Complex.add_re, Complex.one_re]; linarith)
  have hz2 : zetaWN q (1 + b) ≠ 0 := zetaWN_ne_zero_of_one_le_re q (by
    rw [Complex.add_re, Complex.one_re]; linarith)
  have hval : (zetaWN q (1 + a))⁻¹ * (zetaWN q (1 + b))⁻¹ * zetaWN q (1 + a + b) =
      zetaWN q (1 + a + b) / (zetaWN q (1 + a) * zetaWN q (1 + b)) := by
    field_simp [hz1, hz2]
  -- reindex back to the direct per-prime product of the ratio factors
  have hU2 : (fun n : ℕ => ∏ p ∈ S n, u p * v p * w p) =
      fun n : ℕ => ∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q),
        (1 - (p : ℂ) ^ (-(1 + a))) * (1 - (p : ℂ) ^ (-(1 + b))) *
          (1 - (p : ℂ) ^ (-(1 + a + b)))⁻¹ := by
    funext n
    simp [S, u, v, w]
  simpa [hU2, hval] using hmain

end Commons.NumberTheory.MaynardSieve
