import Mathlib
import Submission.ProductTail
import Submission.LocalFactorComparison

open scoped BigOperators Topology
open Filter

set_option linter.unusedVariables false

/-!
# Tail of the kernel Euler product (P8 Lemma 4.1 (40): `K_p = (1+O(p⁻²))R_p`)

Polymath8a, Lemma 4.1, compares the per-prime kernel factor `K_p` of (39) with
its ratio form `R_p = (1−p^{−1−a})(1−p^{−1−b})/(1−p^{−1−a−b})`:

    K_p = (1 + O(p⁻²))·R_p                                    (40)

(`Submission.LocalFactorComparison` proves `‖K_p/R_p − 1‖ ≤ 48/p²`), and
concludes, using `∏_{p > w}(1 + O(p⁻²)) = 1 + o(1)`, that the full Euler
product over the primes `p ∤ WN` (all of which exceed `w` in the application,
since `W = ∏_{p ≤ w} p` divides `q = WN`) differs from the ratio product by a
factor `1 + o(1)` as `w → ∞`.

This module proves that statement in the uniform finite form needed by the
truncation argument:

  * `tailProduct_norm_sub_one_le` — the generic complex tail estimate: for
    distinct naturals `p > w ≥ 1` and `‖z_p‖ ≤ C/p²`,
    `‖∏_{p∈S}(1+z_p) − 1‖ ≤ exp(C/w) − 1`;
  * `locK_div_locR_tail` — its instantiation at `z_p = K_p/R_p − 1` (with
    `C = 48` from (40)): `‖∏_{p∈S} K_p/R_p − 1‖ ≤ exp(48/w) − 1` for
    `S ⊆ {p : w < p}` and `Re a, Re b ≥ 0`;
  * `locK_prod_div_locR_prod_tail` — the same statement for the quotient of
    the two products, i.e. `∏_{p∈S} K_p = (1 + O(1/w))·∏_{p∈S} R_p`.

The companion statement identifying `∏_{p ∤ q} R_p` with the `ζ_WN`-ratio is
`eulerRatioZetaWN` (`Submission.ZetaRatio`); combining the two gives P8 (41).
-/

namespace Commons.NumberTheory.MaynardSieve

/-- **Generic complex Euler-product tail.**  For a finite set `S` of naturals
all exceeding `w ≥ 1`, and complex weights with `‖z_p‖ ≤ C/p²`,

    ‖∏_{p∈S} (1 + z_p) − 1‖ ≤ exp(C/w) − 1 .

(`Finset.norm_prod_one_add_sub_one_le` for the product estimate, and the
telescoping `∑_{p∈S} 1/p² ≤ 1/w` of `Submission.ProductTail` for the exponent.) -/
theorem tailProduct_norm_sub_one_le {C : ℝ} (hC : 0 ≤ C) {w : ℕ} (hw : 1 ≤ w)
    {S : Finset ℕ} (hS : ∀ p ∈ S, w < p) {z : ℕ → ℂ}
    (hz : ∀ p ∈ S, ‖z p‖ ≤ C / (p : ℝ) ^ 2) :
    ‖∏ p ∈ S, (1 + z p) - 1‖ ≤ Real.exp (C / (w : ℝ)) - 1 := by
  refine (Finset.norm_prod_one_add_sub_one_le S z).trans ?_
  have hsum : ∑ p ∈ S, ‖z p‖ ≤ C / (w : ℝ) := by
    have h2 : ∀ p ∈ S, C / (p : ℝ) ^ 2 = C * ((p : ℝ) ^ 2)⁻¹ := by
      intro p _
      rw [div_eq_mul_inv]
    calc
      ∑ p ∈ S, ‖z p‖ ≤ ∑ p ∈ S, C / (p : ℝ) ^ 2 := Finset.sum_le_sum hz
      _ = C * ∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹ := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl h2
      _ ≤ C * (w : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_left (sum_inv_sq_le_inv hw hS) hC
      _ = C / (w : ℝ) := by rw [div_eq_mul_inv]
  exact sub_le_sub_right (Real.exp_le_exp.mpr hsum) 1

/-- **P8 (40) integrated over the tail primes.**  For `Re a, Re b ≥ 0` and a
finite set `S` of naturals all exceeding `w ≥ 1`:

    ‖∏_{p∈S} K_p/R_p − 1‖ ≤ exp(48/w) − 1 . -/
theorem locK_div_locR_tail {a b : ℂ} (ha : 0 ≤ a.re) (hb : 0 ≤ b.re) {w : ℕ}
    (hw : 1 ≤ w) {S : Finset ℕ} (hS : ∀ p ∈ S, w < p) :
    ‖∏ p ∈ S, (locK p a b / locR p a b) - 1‖ ≤ Real.exp (48 / (w : ℝ)) - 1 := by
  have hprod : (∏ p ∈ S, (1 + (locK p a b / locR p a b - 1))) =
      ∏ p ∈ S, (locK p a b / locR p a b) := by
    refine Finset.prod_congr rfl (fun p _ => ?_)
    ring
  rw [← hprod]
  refine tailProduct_norm_sub_one_le (C := 48) (by norm_num) hw hS (fun p hp => ?_)
  have hp2 : 2 ≤ p := by have := hS p hp; omega
  exact locK_div_locR_sub_one_bound a b hp2 ha hb

/-- **P8 (40), product form.**  `∏_{p∈S} K_p = (1 + O(1/w))·∏_{p∈S} R_p` as a
norm bound on the quotient. -/
theorem locK_prod_div_locR_prod_tail {a b : ℂ} (ha : 0 ≤ a.re) (hb : 0 ≤ b.re)
    {w : ℕ} (hw : 1 ≤ w) {S : Finset ℕ} (hS : ∀ p ∈ S, w < p) :
    ‖(∏ p ∈ S, locK p a b) / (∏ p ∈ S, locR p a b) - 1‖ ≤
      Real.exp (48 / (w : ℝ)) - 1 := by
  rw [← Finset.prod_div_distrib]
  exact locK_div_locR_tail ha hb hw hS

end Commons.NumberTheory.MaynardSieve
