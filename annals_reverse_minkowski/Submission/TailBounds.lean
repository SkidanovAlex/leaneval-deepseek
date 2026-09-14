import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Real
open scoped BigOperators Topology
set_option autoImplicit false

namespace Submission

/-- For c > 0, the Gaussian tail over positive integers is bounded by a geometric series. -/
lemma gauss_tail_le_geom (c : ℝ) (hc : 0 < c) :
    (∑' k : ℕ, Real.exp (-c * ((k : ℝ) + 1) ^ 2)) ≤
      Real.exp (-c) / (1 - Real.exp (-c)) := by
  have hexp0 : 0 < Real.exp (-c) := Real.exp_pos _
  have hexp1 : Real.exp (-c) < 1 := (Real.exp_lt_one_iff.mpr (by linarith))
  let r : ℝ := Real.exp (-c)
  have hr0 : 0 ≤ r := hexp0.le
  have hr1 : r < 1 := hexp1
  have hsumm_r : Summable (fun n : ℕ => r ^ (n + 1)) := by
    simpa [pow_succ, mul_comm] using (summable_geometric_of_lt_one hr0 hr1).mul_left r
  have hterm : ∀ k : ℕ, Real.exp (-c * ((k : ℝ) + 1) ^ 2) ≤ r ^ (k + 1) := by
    intro k
    dsimp [r]
    rw [← Real.exp_nat_mul]
    rw [Real.exp_le_exp]
    norm_num
    have hk : ((k : ℝ) + 1) ^ 2 ≥ (k : ℝ) + 1 := by
      calc
        ((k : ℝ) + 1) ^ 2 = (k : ℝ) ^ 2 + 2 * (k : ℝ) + 1 := by ring
        _ ≥ (k : ℝ) + 1 := by nlinarith [sq_nonneg (k : ℝ)]
    nlinarith
  have hleft : Summable (fun k : ℕ => Real.exp (-c * ((k : ℝ) + 1) ^ 2)) := by
    refine Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) (fun k => hterm k) hsumm_r
  calc
    (∑' k : ℕ, Real.exp (-c * ((k : ℝ) + 1) ^ 2)) ≤ ∑' k : ℕ, r ^ (k + 1) := by
      exact Summable.tsum_le_tsum hterm hleft hsumm_r
    _ = r / (1 - r) := by
      calc
        (∑' n : ℕ, r ^ (n + 1)) = r * (∑' n : ℕ, r ^ n) := by
          rw [← tsum_mul_left]
          apply tsum_congr
          intro n
          ring
        _ = r * (1 - r)⁻¹ := by rw [tsum_geometric_of_lt_one hr0 hr1]
        _ = r / (1 - r) := by field_simp [sub_ne_zero.mpr hr1.ne']

/-- crude but often-useful bound: Gaussian tail ≤ 2 exp(-c) when exp(-c) ≤ 1/2 -/
lemma gauss_tail_le_two_exp_neg (c : ℝ) (hc1 : Real.exp (-c) ≤ 1 / 2) :
    (∑' k : ℕ, Real.exp (-c * ((k : ℝ) + 1) ^ 2)) ≤ 2 * Real.exp (-c) := by
  have hc : 0 < c := by
    by_contra hc'
    have hle : 1 ≤ Real.exp (-c) := by
      have : Real.exp (-c) ≥ Real.exp 0 := Real.exp_monotone (by linarith)
      simpa using this
    linarith
  have hden : (1 - Real.exp (-c))⁻¹ ≤ 2 := by
    have hpos : 0 < 1 - Real.exp (-c) := by linarith
    rw [← one_div]
    rw [div_le_iff₀ hpos]
    nlinarith
  calc
    (∑' k : ℕ, Real.exp (-c * ((k : ℝ) + 1) ^ 2)) ≤ Real.exp (-c) / (1 - Real.exp (-c)) := gauss_tail_le_geom c hc
    _ = Real.exp (-c) * (1 - Real.exp (-c))⁻¹ := by rfl
    _ ≤ Real.exp (-c) * 2 := by nlinarith [mul_le_mul_of_nonneg_left hden (Real.exp_pos (-c)).le]
    _ = 2 * Real.exp (-c) := by ring


/-- exp(-1200) is tiny: ≤ 1/8. -/
lemma exp_neg_1200_le : Real.exp (-1200) ≤ 1 / 8 := by
  have hge1 : (1201 : ℝ) ≤ Real.exp 1200 := by
    have := Real.add_one_le_exp (x := (1200 : ℝ))
    norm_num at this ⊢
    exact this
  have hge8 : (8 : ℝ) ≤ Real.exp 1200 := by linarith
  have hpos : 0 < Real.exp 1200 := Real.exp_pos _
  rw [Real.exp_neg]
  have h := (inv_le_inv₀ hpos (by norm_num : 0 < (8 : ℝ))).mpr hge8
  norm_num at h ⊢
  exact h

/-- If c ≥ 1200 then exp(-c) ≤ 1/8 ≤ 1/2 -/
lemma exp_neg_le_of_ge (c : ℝ) (hc : 1200 ≤ c) : Real.exp (-c) ≤ 1 / 2 := by
  have hmono : Real.exp (-c) ≤ Real.exp (-1200) := by
    exact Real.exp_monotone (by linarith)
  have hle : Real.exp (-1200) ≤ 1 / 2 := by linarith [exp_neg_1200_le]
  linarith

/-- Gaussian tail with c ≥ 1200 is ≤ 1/4 -/
lemma gauss_tail_le_quarter_of_ge (c : ℝ) (hc : 1200 ≤ c) :
    (∑' k : ℕ, Real.exp (-c * ((k : ℝ) + 1) ^ 2)) ≤ 1 / 4 := by
  have hcpos : 0 < c := by linarith
  have h1 : Real.exp (-c) ≤ 1 / 2 := exp_neg_le_of_ge c hc
  have h2 : (∑' k : ℕ, Real.exp (-c * ((k : ℝ) + 1) ^ 2)) ≤ 2 * Real.exp (-c) :=
    gauss_tail_le_two_exp_neg c h1
  have h3 : Real.exp (-c) ≤ 1 / 8 := by
    have hmono : Real.exp (-c) ≤ Real.exp (-1200) := Real.exp_monotone (by linarith)
    linarith [exp_neg_1200_le, hmono]
  linarith

end Submission
