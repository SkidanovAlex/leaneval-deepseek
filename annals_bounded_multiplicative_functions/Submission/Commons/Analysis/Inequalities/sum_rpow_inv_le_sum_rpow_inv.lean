import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Inequalities

open scoped NNReal ENNReal BigOperators

/-- For `r ≥ 1`, the `r`-th power of a finite sum of extended nonnegative reals dominates the
sum of the `r`-th powers: `∑ i ∈ s, a_i ^ r ≤ (∑ i ∈ s, a_i) ^ r`. -/
theorem finset_sum_rpow_le_of_one_le {ι : Type*} (s : Finset ι) (a : ι → ℝ≥0∞) {r : ℝ}
    (hr : 1 ≤ r) : ∑ i ∈ s, (a i) ^ r ≤ (∑ i ∈ s, a i) ^ r := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rcases eq_or_ne (∑ i ∈ s, a i) ⊤ with hstop | hSne
  · rw [hstop, ENNReal.top_rpow_of_pos hr0]
    exact le_top
  rcases eq_or_ne (∑ i ∈ s, a i) 0 with hS0 | hSne0
  · have ha : ∀ i ∈ s, a i = 0 := fun i hi => by
      have h := Finset.single_le_sum (f := a) (fun j _ => zero_le) hi
      rw [hS0] at h
      exact le_bot_iff.mp h
    rw [hS0, ENNReal.zero_rpow_of_pos hr0]
    exact le_of_eq (Finset.sum_eq_zero fun i hi => by
      rw [ha i hi, ENNReal.zero_rpow_of_pos hr0])
  · calc ∑ i ∈ s, (a i) ^ r
        ≤ ∑ i ∈ s, a i * (∑ j ∈ s, a j) ^ (r - 1) := by
          apply Finset.sum_le_sum
          intro i hi
          have hai_le : a i ≤ ∑ j ∈ s, a j :=
            Finset.single_le_sum (f := a) (fun j _ => zero_le) hi
          have hai_top : a i ≠ ⊤ := ne_top_of_le_ne_top hSne hai_le
          rcases eq_or_ne (a i) 0 with hai0 | hai0
          · rw [hai0, ENNReal.zero_rpow_of_pos hr0, zero_mul]
          · have hpow : a i ^ r = a i * a i ^ (r - 1) := by
              conv_lhs => rw [show r = 1 + (r - 1) by ring]
              rw [ENNReal.rpow_add 1 (r - 1) hai0 hai_top, ENNReal.rpow_one]
            rw [hpow]
            exact mul_le_mul_right (ENNReal.rpow_le_rpow hai_le (by linarith)) (a i)
      _ = (∑ i ∈ s, a i) * (∑ j ∈ s, a j) ^ (r - 1) := by rw [Finset.sum_mul]
      _ = (∑ i ∈ s, a i) ^ r := by
          nth_rw 1 [← ENNReal.rpow_one (∑ i ∈ s, a i)]
          rw [← ENNReal.rpow_add 1 (r - 1) hSne0 hSne,
            show (1 : ℝ) + (r - 1) = r by ring]

/-- **The embedding `ℓ^p ↪ ℓ^q` for `p ≤ q`**, in `ℝ≥0∞` form: for `0 < p ≤ q` and a finite
family `x : ι → ℝ≥0∞`, `(Σ x_i^q)^(1/q) ≤ (Σ x_i^p)^(1/p)`. -/
theorem sum_rpow_inv_le_sum_rpow_inv {ι : Type*} (s : Finset ι) (x : ι → ℝ≥0∞)
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    (∑ i ∈ s, (x i) ^ q) ^ (1 / q) ≤ (∑ i ∈ s, (x i) ^ p) ^ (1 / p) := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hpne : p ≠ 0 := ne_of_gt hp
  have hpmul : p * (q / p) = q := by
    rw [mul_comm, div_mul_cancel₀ q hpne]
  have hpow : ∀ i, (x i) ^ q = ((x i) ^ p) ^ (q / p) := fun i => by
    rw [← ENNReal.rpow_mul, hpmul]
  have h1 : ∑ i ∈ s, (x i) ^ q ≤ (∑ i ∈ s, (x i) ^ p) ^ (q / p) := by
    simp_rw [hpow]
    refine finset_sum_rpow_le_of_one_le s (fun i => (x i) ^ p) ?_
    rw [le_div_iff₀ hp]
    simpa using hpq
  calc (∑ i ∈ s, (x i) ^ q) ^ (1 / q)
      ≤ ((∑ i ∈ s, (x i) ^ p) ^ (q / p)) ^ (1 / q) :=
        ENNReal.rpow_le_rpow h1 (by positivity)
    _ = (∑ i ∈ s, (x i) ^ p) ^ ((q / p) * (1 / q)) := (ENNReal.rpow_mul _ _ _).symm
    _ = (∑ i ∈ s, (x i) ^ p) ^ (1 / p) := by
        congr 1
        field_simp

end Commons.Analysis.Inequalities