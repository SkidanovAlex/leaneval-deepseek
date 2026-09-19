import Mathlib
import Submission.Commons.Analysis.Complex.norm_ratio_sub_one_le

open scoped BigOperators

namespace Commons.NumberTheory.Zeta

/-- For a natural `p ≥ 2` and a complex exponent `s` with `1 ≤ Re s`, the power
`p^{-s}` has norm at most `1/p`.  (`‖(p:ℂ)^{-s}‖ = p^{-Re s} ≤ p^{-1}`.) -/
private lemma norm_cpow_neg_le_inv (p : ℕ) (hp2 : 2 ≤ p) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖(p : ℂ) ^ (-s)‖ ≤ (p : ℝ)⁻¹ := by
  have hp0 : 0 < p := by omega
  have hle := Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos (n := p) hp0
      (w := -s) (z := (-1 : ℂ)) ?_
  · rwa [Complex.cpow_neg_one, norm_inv, Complex.norm_natCast] at hle
  · simp only [Complex.neg_re, Complex.one_re]
    linarith

/-- **P8 Lemma 4.1 (40), `k` coordinates, uniform form.**

For any number `k` of coordinates there is a constant `C > 0` such that for every
integer `p ≥ 2` and every pair of `k`-tuples `a, b : Fin k → ℂ` with non-negative
real parts,

    ‖ (1 + ∑_j (-p^{-(1+a_j)} - p^{-(1+b_j)} + p^{-(1+a_j+b_j)}))
        / ∏_j ((1-p^{-(1+a_j)})(1-p^{-(1+b_j)})/(1-p^{-(1+a_j+b_j)})) - 1 ‖
      ≤ C / p².

The numerator is the first-order expansion of the product `∏_j K_{p,j}` of the
per-prime local factors `K_{p,j} = 1 - p^{-(1+a_j)} - p^{-(1+b_j)} +
p^{-(1+a_j+b_j)}`, while the denominator is the corresponding ratio product
`∏_j R_{p,j}`; both `p^{-(1+a_j)}`, `p^{-(1+b_j)}`, `p^{-(1+a_j+b_j)}` are `O(1/p)`,
so the relative error is `O(p⁻²)` uniformly in `a, b` (with `Re ≥ 0`). -/
theorem exists_norm_coordK_div_prod_locR_sub_one_le (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ), 2 ≤ p → ∀ (a b : Fin k → ℂ),
      (∀ j, 0 ≤ (a j).re) → (∀ j, 0 ≤ (b j).re) →
      ‖(1 + ∑ j : Fin k, (-((p : ℂ) ^ (-(1 + a j))) - ((p : ℂ) ^ (-(1 + b j))) +
            ((p : ℂ) ^ (-(1 + a j + b j))))) /
          (∏ j : Fin k, (((1 : ℂ) - (p : ℂ) ^ (-(1 + a j))) * ((1 : ℂ) - (p : ℂ) ^ (-(1 + b j))) /
            ((1 : ℂ) - (p : ℂ) ^ (-(1 + a j + b j))))) - 1‖ ≤ C / (p : ℝ) ^ 2 := by
  obtain ⟨C, hCpos, hC⟩ := Commons.Analysis.Complex.norm_ratio_sub_one_le k
  refine ⟨C, hCpos, fun p hp2 a b ha hb => ?_⟩
  have hp2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hρpos : 0 < (p : ℝ)⁻¹ := by positivity
  have hρle : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [one_div]
    exact (inv_le_inv₀ (by positivity : (0 : ℝ) < (p : ℝ)) (by norm_num : (0 : ℝ) < (2 : ℝ))).mpr hp2r
  have hx : ∀ j : Fin k, ‖(p : ℂ) ^ (-(1 + a j))‖ ≤ (p : ℝ)⁻¹ :=
    fun j => norm_cpow_neg_le_inv p hp2 (s := 1 + a j)
      (by rw [Complex.add_re, Complex.one_re]; linarith [ha j])
  have hy : ∀ j : Fin k, ‖(p : ℂ) ^ (-(1 + b j))‖ ≤ (p : ℝ)⁻¹ :=
    fun j => norm_cpow_neg_le_inv p hp2 (s := 1 + b j)
      (by rw [Complex.add_re, Complex.one_re]; linarith [hb j])
  have hz : ∀ j : Fin k, ‖(p : ℂ) ^ (-(1 + a j + b j))‖ ≤ (p : ℝ)⁻¹ :=
    fun j => norm_cpow_neg_le_inv p hp2 (s := 1 + a j + b j)
      (by rw [Complex.add_re, Complex.add_re, Complex.one_re]; linarith [ha j, hb j])
  have hmain := hC (p : ℝ)⁻¹ hρpos hρle
    (fun j : Fin k => (p : ℂ) ^ (-(1 + a j)))
    (fun j : Fin k => (p : ℂ) ^ (-(1 + b j)))
    (fun j : Fin k => (p : ℂ) ^ (-(1 + a j + b j))) hx hy hz
  simpa [div_eq_mul_inv, inv_pow] using hmain

end Commons.NumberTheory.Zeta
