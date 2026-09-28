import Mathlib
import Submission.Work.HP.dyadic_summation

namespace Work.HP

/-- Geometric decay: for `r ≥ 2` the terms `(1/2)^{j (r-1)}` decay at least like `(1/2)^j`,
so their sum is at most `2`. -/
theorem geom_half_sum (r : ℕ) (hr : 2 ≤ r) (n : ℕ) :
    ∑ j ∈ Finset.range n, ((1 : ℝ) / 2) ^ (j * (r - 1)) ≤ 2 := by
  have hx : ((1 : ℝ) / 2) ^ (r - 1) ≤ 1 / 2 := by
    have h2 : (2 : ℝ) ≤ 2 ^ (r - 1) := by
      simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 1 ≤ r - 1)
    rw [div_pow, one_pow]
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) h2
  have hcongr : ∑ j ∈ Finset.range n, ((1 : ℝ) / 2) ^ (j * (r - 1))
      = ∑ j ∈ Finset.range n, (((1 : ℝ) / 2) ^ (r - 1)) ^ j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.mul_comm j (r - 1), pow_mul]
  rw [hcongr]
  have hx1 : ((1 : ℝ) / 2) ^ (r - 1) ≠ 1 := by linarith
  rw [geom_sum_eq hx1 n]
  have hxn : 0 ≤ (((1 : ℝ) / 2) ^ (r - 1)) ^ n := by positivity
  have hden : (0 : ℝ) < 1 - ((1 : ℝ) / 2) ^ (r - 1) := by linarith
  have heq : ((((1 : ℝ) / 2) ^ (r - 1)) ^ n - 1) / (((1 : ℝ) / 2) ^ (r - 1) - 1)
      = (1 - (((1 : ℝ) / 2) ^ (r - 1)) ^ n) / (1 - ((1 : ℝ) / 2) ^ (r - 1)) := by
    rw [div_eq_div_iff (by linarith : ((1 : ℝ) / 2) ^ (r - 1) - 1 ≠ 0)
        (by linarith : (1 : ℝ) - ((1 : ℝ) / 2) ^ (r - 1) ≠ 0)]
    ring
  rw [heq, div_le_iff₀ hden]
  nlinarith [hxn, hx]

/-- Collapsing the dyadic weight of one shell into a single power of `2` times a decaying
geometric factor. -/
theorem dyadic_pow_algebra (r L j : ℕ) (hr : 1 ≤ r) :
    (2 : ℝ) ^ (j + 2) / (2 : ℝ) ^ L * ((2 : ℝ) ^ (L + 1) / (2 : ℝ) ^ j) ^ r
      = (2 : ℝ) ^ (L * (r - 1) + r + 2) * ((1 : ℝ) / 2) ^ (j * (r - 1)) := by
  have hpow : ((2 : ℝ) ^ (L + 1) / (2 : ℝ) ^ j) ^ r
      = (2 : ℝ) ^ (r * (L + 1)) / (2 : ℝ) ^ (r * j) := by
    rw [div_pow]
    congr 1
    · rw [← pow_mul, Nat.mul_comm (L + 1) r]
    · rw [← pow_mul, Nat.mul_comm j r]
  rw [hpow, div_mul_div_comm]
  have hn : (2 : ℝ) ^ (j + 2) * (2 : ℝ) ^ (r * (L + 1))
      = (2 : ℝ) ^ (L * (r - 1) + r + 2) * (2 : ℝ) ^ (j + L) := by
    rw [← pow_add, ← pow_add]
    congr 1
    have h1 : r * (L + 1) = L * (r - 1) + (r + L) := by
      have hL : L * (r - 1) + L = L * r := by
        rw [← Nat.mul_succ]
        congr 1
        omega
      have hcomm : r * L = L * r := Nat.mul_comm r L
      rw [Nat.mul_add, Nat.mul_one]
      omega
    rw [h1]
    omega
  have hd : (2 : ℝ) ^ L * (2 : ℝ) ^ (r * j)
      = (2 : ℝ) ^ (j * (r - 1)) * (2 : ℝ) ^ (j + L) := by
    rw [← pow_add, ← pow_add]
    congr 1
    have h2 : j * (r - 1) + j = j * r := by
      rw [← Nat.mul_succ]
      congr 1
      omega
    have hcomm : r * j = j * r := Nat.mul_comm r j
    omega
  rw [hn, hd, mul_div_mul_right _ _ (by positivity : (2 : ℝ) ^ (j + L) ≠ 0)]
  rw [div_pow, one_pow, one_div, div_eq_mul_inv]

/-- Final dyadic comparison: `2^{L(r-1)+r+2} · 2 ≤ 2^{2r+2} A^{r-1}` whenever `2^L ≤ 2A`. -/
theorem final_arith (r : ℕ) (hr : 2 ≤ r) {A : ℝ} {L : ℕ}
    (h2L : (2 : ℝ) ^ L ≤ 2 * A) :
    (2 : ℝ) ^ (L * (r - 1) + r + 2) * 2 ≤ (2 : ℝ) ^ (2 * r + 2) * A ^ (r - 1) := by
  have hL : (2 : ℝ) ^ (L * (r - 1) + r + 2) * 2
      = (2 : ℝ) ^ (r + 3) * ((2 : ℝ) ^ L) ^ (r - 1) := by
    calc (2 : ℝ) ^ (L * (r - 1) + r + 2) * 2
        = (2 : ℝ) ^ (L * (r - 1)) * (2 : ℝ) ^ (r + 2) * 2 := by
            rw [show L * (r - 1) + r + 2 = L * (r - 1) + (r + 2) by ring, pow_add]
      _ = (2 : ℝ) ^ (L * (r - 1)) * ((2 : ℝ) ^ (r + 2) * 2) := by ring
      _ = (2 : ℝ) ^ (L * (r - 1)) * (2 : ℝ) ^ (r + 3) := by
            rw [show (2 : ℝ) ^ (r + 3) = (2 : ℝ) ^ (r + 2) * 2 by
                  rw [show r + 3 = r + 2 + 1 by omega, pow_succ]]
      _ = (2 : ℝ) ^ (r + 3) * ((2 : ℝ) ^ L) ^ (r - 1) := by
            rw [pow_mul]; ring
  have hR : (2 : ℝ) ^ (2 * r + 2) * A ^ (r - 1)
      = (2 : ℝ) ^ (r + 3) * (2 * A) ^ (r - 1) := by
    rw [mul_pow]
    rw [show (2 : ℝ) ^ (2 * r + 2) = (2 : ℝ) ^ (r + 3) * (2 : ℝ) ^ (r - 1) by
          rw [← pow_add]; congr 1; omega]
    ring
  rw [hL, hR]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2L (r - 1)) (by positivity)

theorem dyadic_ball_weight_sum (r : ℕ) (hr : 2 ≤ r) :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 1 ≤ A →
      (∑ j ∈ Finset.range (dyIdx A + 1), ((2 : ℝ) ^ (j + 1) / A) * (A / (2 : ℝ) ^ j + 1) ^ r)
        ≤ K * A ^ (r - 1) := by
  refine ⟨(2 : ℝ) ^ (2 * r + 2), by positivity, ?_⟩
  intro A hA
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hAle : A ≤ (2 : ℝ) ^ (dyIdx A) := le_pow_dyIdx A
  have h2L : (2 : ℝ) ^ (dyIdx A) ≤ 2 * A := pow_dyIdx_le hA
  have hpt : ∀ j ∈ Finset.range (dyIdx A + 1),
      ((2 : ℝ) ^ (j + 1) / A) * (A / (2 : ℝ) ^ j + 1) ^ r
        ≤ (2 : ℝ) ^ (dyIdx A * (r - 1) + r + 2) * ((1 : ℝ) / 2) ^ (j * (r - 1)) := by
    intro j hj
    have hjL : j ≤ dyIdx A := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have h2jpos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    have h2Lpos : (0 : ℝ) < (2 : ℝ) ^ (dyIdx A) := by positivity
    have I1 : (2 : ℝ) ^ (j + 1) / A ≤ (2 : ℝ) ^ (j + 2) / (2 : ℝ) ^ (dyIdx A) := by
      rw [div_le_div_iff₀ hA0 h2Lpos]
      have h2 : (2 : ℝ) ^ (j + 2) = (2 : ℝ) ^ (j + 1) * 2 := by rw [pow_succ]
      rw [h2, mul_assoc]
      exact mul_le_mul_of_nonneg_left h2L (by positivity)
    have hAj : A + (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (dyIdx A + 1) := by
      have h1 : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (dyIdx A) := pow_le_pow_right₀ (by norm_num) hjL
      calc A + (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (dyIdx A) + (2 : ℝ) ^ (dyIdx A) := add_le_add hAle h1
        _ = (2 : ℝ) ^ (dyIdx A + 1) := by rw [pow_succ]; ring
    have I2b : A / (2 : ℝ) ^ j + 1 ≤ (2 : ℝ) ^ (dyIdx A + 1) / (2 : ℝ) ^ j := by
      rw [← div_self (ne_of_gt h2jpos), ← add_div]
      exact div_le_div_of_nonneg_right hAj h2jpos.le
    have I2 : (A / (2 : ℝ) ^ j + 1) ^ r
        ≤ ((2 : ℝ) ^ (dyIdx A + 1) / (2 : ℝ) ^ j) ^ r :=
      pow_le_pow_left₀ (by positivity) I2b r
    calc ((2 : ℝ) ^ (j + 1) / A) * (A / (2 : ℝ) ^ j + 1) ^ r
        ≤ ((2 : ℝ) ^ (j + 2) / (2 : ℝ) ^ (dyIdx A))
            * ((2 : ℝ) ^ (dyIdx A + 1) / (2 : ℝ) ^ j) ^ r :=
          mul_le_mul I1 I2 (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (dyIdx A * (r - 1) + r + 2) * ((1 : ℝ) / 2) ^ (j * (r - 1)) :=
          dyadic_pow_algebra r (dyIdx A) j (by omega)
  calc ∑ j ∈ Finset.range (dyIdx A + 1), ((2 : ℝ) ^ (j + 1) / A) * (A / (2 : ℝ) ^ j + 1) ^ r
      ≤ ∑ j ∈ Finset.range (dyIdx A + 1),
          (2 : ℝ) ^ (dyIdx A * (r - 1) + r + 2) * ((1 : ℝ) / 2) ^ (j * (r - 1)) :=
        Finset.sum_le_sum hpt
    _ = (2 : ℝ) ^ (dyIdx A * (r - 1) + r + 2)
          * ∑ j ∈ Finset.range (dyIdx A + 1), ((1 : ℝ) / 2) ^ (j * (r - 1)) := by
        rw [Finset.mul_sum]
    _ ≤ (2 : ℝ) ^ (dyIdx A * (r - 1) + r + 2) * 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact geom_half_sum r hr (dyIdx A + 1)
    _ ≤ (2 : ℝ) ^ (2 * r + 2) * A ^ (r - 1) := final_arith r hr h2L

end Work.HP
