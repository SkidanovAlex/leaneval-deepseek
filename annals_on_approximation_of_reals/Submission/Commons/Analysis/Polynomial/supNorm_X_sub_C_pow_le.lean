import Mathlib.Analysis.Polynomial.Norm

open Polynomial
open scoped BigOperators

namespace Commons.Analysis.Polynomial

/-- For every coefficient index `k`, the coefficient of `(X - C a)^m` at `k` has norm bounded
by `(2 * (1 + |a|))^m`. -/
lemma coeff_norm_X_sub_C_pow_le (m : ℕ) (a : ℝ) (k : ℕ) :
    ‖(((Polynomial.X - Polynomial.C a) ^ m : Polynomial ℝ).coeff k)‖ ≤
      (2 : ℝ) ^ m * (1 + |a|) ^ m := by
  have hXC : (Polynomial.X - Polynomial.C a : Polynomial ℝ) =
      Polynomial.X + Polynomial.C (-a) := by
    rw [sub_eq_add_neg]
    congr 1
    exact (map_neg (Polynomial.C : ℝ →+* Polynomial ℝ) a).symm
  calc
    ‖(((Polynomial.X - Polynomial.C a) ^ m : Polynomial ℝ).coeff k)‖
        = ‖(((-a) ^ (m - k) : ℝ) * (m.choose k : ℝ))‖ := by
            rw [hXC, Polynomial.coeff_X_add_C_pow]
    _ = |a| ^ (m - k) * (m.choose k : ℝ) := by
            rw [norm_mul, norm_pow]
            congr 1
            · rw [norm_neg, Real.norm_eq_abs]
            · rw [Real.norm_eq_abs, abs_of_nonneg]
              exact Nat.cast_nonneg (m.choose k)
    _ = (m.choose k : ℝ) * |a| ^ (m - k) := by ring
    _ ≤ (m.choose k : ℝ) * (1 + |a|) ^ m := by
            refine mul_le_mul_of_nonneg_left ?h2 (Nat.cast_nonneg (m.choose k))
            have hbase : |a| ≤ 1 + |a| := by linarith [abs_nonneg a]
            have hb0 : 0 ≤ |a| := abs_nonneg a
            have h1 : 1 ≤ 1 + |a| := by linarith
            exact (pow_le_pow_left₀ hb0 hbase (m - k)).trans
              (pow_le_pow_right₀ h1 (Nat.sub_le m k))
    _ ≤ (2 : ℝ) ^ m * (1 + |a|) ^ m := by
            refine mul_le_mul_of_nonneg_right ?hch ?hpos
            · exact_mod_cast Nat.choose_le_two_pow m k
            · exact pow_nonneg (by linarith [abs_nonneg a]) m

/-- Coefficient sup-norm of `(X - C a)^m` is bounded by `(2 * (1 + |a|))^m`. -/
theorem supNorm_X_sub_C_pow_le (m : ℕ) (a : ℝ) :
    (((Polynomial.X - Polynomial.C a) ^ m : Polynomial ℝ).supNorm) ≤
      (2 : ℝ) ^ m * (1 + |a|) ^ m := by
  obtain ⟨i, hi⟩ := Polynomial.exists_eq_supNorm
    ((Polynomial.X - Polynomial.C a) ^ m : Polynomial ℝ)
  calc
    (((Polynomial.X - Polynomial.C a) ^ m : Polynomial ℝ).supNorm)
        = ‖(((Polynomial.X - Polynomial.C a) ^ m : Polynomial ℝ).coeff i)‖ := hi
    _ ≤ (2 : ℝ) ^ m * (1 + |a|) ^ m := coeff_norm_X_sub_C_pow_le m a i

end Commons.Analysis.Polynomial