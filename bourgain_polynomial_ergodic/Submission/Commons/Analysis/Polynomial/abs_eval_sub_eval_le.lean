import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Ring.GeomSum

namespace Commons.Analysis.Polynomial

open Finset

/-- For `x, y ∈ [0, X]` with `X ≥ 1` and `i ≤ d`, the difference of `i`-th powers is bounded by
`d * X ^ (d - 1) * |x - y|`. -/
lemma abs_pow_sub_pow_le {x y X : ℝ} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hxX : x ≤ X) (hyX : y ≤ X)
    (hX : 1 ≤ X) {d i : ℕ} (hi : i ≤ d) :
    |x ^ i - y ^ i| ≤ (d : ℝ) * X ^ (d - 1) * |x - y| := by
  have hX0 : 0 ≤ X := le_trans zero_le_one hX
  have hxabs : |x| ≤ X := abs_le.mpr ⟨by linarith, hxX⟩
  have hyabs : |y| ≤ X := abs_le.mpr ⟨by linarith, hyX⟩
  have hfac : x ^ i - y ^ i = (x - y) * ∑ j ∈ range i, x ^ j * y ^ (i - 1 - j) :=
    ((Commute.all x y).mul_geom_sum₂ i).symm
  rw [hfac, abs_mul]
  have hsum : |∑ j ∈ range i, x ^ j * y ^ (i - 1 - j)| ≤ (i : ℝ) * X ^ (i - 1) := by
    calc |∑ j ∈ range i, x ^ j * y ^ (i - 1 - j)|
        ≤ ∑ j ∈ range i, |x ^ j * y ^ (i - 1 - j)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j ∈ range i, |x| ^ j * |y| ^ (i - 1 - j) := by simp [abs_mul, abs_pow]
      _ ≤ ∑ j ∈ range i, X ^ (i - 1) := by
            apply Finset.sum_le_sum
            intro j hj
            have hjle : j ≤ i - 1 := by
              have := Finset.mem_range.mp hj; omega
            have h1 : |x| ^ j ≤ X ^ j := pow_le_pow_left₀ (abs_nonneg x) hxabs j
            have h2 : |y| ^ (i - 1 - j) ≤ X ^ (i - 1 - j) :=
              pow_le_pow_left₀ (abs_nonneg y) hyabs _
            calc |x| ^ j * |y| ^ (i - 1 - j) ≤ X ^ j * X ^ (i - 1 - j) :=
                    mul_le_mul h1 h2 (pow_nonneg (abs_nonneg y) _) (pow_nonneg hX0 _)
              _ = X ^ (i - 1) := by
                    rw [← pow_add, Nat.add_sub_cancel' hjle]
      _ = (i : ℝ) * X ^ (i - 1) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hmono : (i : ℝ) * X ^ (i - 1) ≤ (d : ℝ) * X ^ (d - 1) :=
    mul_le_mul (Nat.cast_le.mpr hi) (pow_le_pow_right₀ hX (Nat.sub_le_sub_right hi 1))
      (pow_nonneg hX0 _) (Nat.cast_nonneg d)
  calc |x - y| * |∑ j ∈ range i, x ^ j * y ^ (i - 1 - j)|
      ≤ |x - y| * ((i : ℝ) * X ^ (i - 1)) := mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ ≤ |x - y| * ((d : ℝ) * X ^ (d - 1)) := mul_le_mul_of_nonneg_left hmono (abs_nonneg _)
    _ = (d : ℝ) * X ^ (d - 1) * |x - y| := by ring

theorem abs_eval_sub_eval_le (Q : Polynomial ℝ) (d : ℕ) (hd : 1 ≤ d) (hdeg : Q.natDegree ≤ d)
    {X x y : ℝ} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hxX : x ≤ X) (hyX : y ≤ X) (hX : 1 ≤ X) :
    |Q.eval x - Q.eval y|
      ≤ (∑ i ∈ Finset.range (d + 1), |Q.coeff i|) * (d : ℝ) * X ^ (d - 1) * |x - y| := by
  have hd1 : Q.natDegree < d + 1 := Nat.lt_succ_of_le hdeg
  have hx : Q.eval x = ∑ i ∈ Finset.range (d + 1), Q.coeff i * x ^ i :=
    Polynomial.eval_eq_sum_range' hd1 x
  have hy : Q.eval y = ∑ i ∈ Finset.range (d + 1), Q.coeff i * y ^ i :=
    Polynomial.eval_eq_sum_range' hd1 y
  have hdiff : Q.eval x - Q.eval y = ∑ i ∈ Finset.range (d + 1), Q.coeff i * (x ^ i - y ^ i) := by
    rw [hx, hy, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  calc |Q.eval x - Q.eval y|
      = |∑ i ∈ Finset.range (d + 1), Q.coeff i * (x ^ i - y ^ i)| := by rw [hdiff]
    _ ≤ ∑ i ∈ Finset.range (d + 1), |Q.coeff i * (x ^ i - y ^ i)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range (d + 1), |Q.coeff i| * |x ^ i - y ^ i| := by simp [abs_mul]
    _ ≤ ∑ i ∈ Finset.range (d + 1), |Q.coeff i| * ((d : ℝ) * X ^ (d - 1) * |x - y|) := by
          apply Finset.sum_le_sum
          intro i hi
          apply mul_le_mul_of_nonneg_left
            (abs_pow_sub_pow_le hx0 hy0 hxX hyX hX
              (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
          exact abs_nonneg _
    _ = (∑ i ∈ Finset.range (d + 1), |Q.coeff i|) * ((d : ℝ) * X ^ (d - 1) * |x - y|) := by
          rw [Finset.sum_mul]
    _ = (∑ i ∈ Finset.range (d + 1), |Q.coeff i|) * (d : ℝ) * X ^ (d - 1) * |x - y| := by ring

end Commons.Analysis.Polynomial