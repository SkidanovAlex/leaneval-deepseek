import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Uniform block-sum bound (VK chain)

This file proves `Work.BMF.VKChain.block_sum_uniform`: the quantity

`(1 + L / log 2) * exp (-(c * ((L / c) ^ (6/7)) ^ 3 / (L^2 * log (c ^ (6/7) * L ^ (1/7) + 2))))`

is bounded above uniformly in `L ≥ 1`, for every fixed `c = cvk` with `0 < c ≤ 1`.

The mathematical content is that the exponent of the exponential grows like
`L ^ (3/7) / 2`, which beats the linear prefactor `1 + L / log 2`; hence the whole
expression stays bounded (indeed it is at most `200`).
-/

namespace Work.BMF.VKChain

/-- For `y > 0`, `exp (-y) ≤ 6 / y^3`. This is the elementary Taylor bound
`1 + y + y^2/2 + y^3/6 ≤ exp y`. -/
lemma exp_neg_le_cube (y : ℝ) (hy : 0 < y) : Real.exp (-y) ≤ 6 / y^3 := by
  have hsum : (∑ i ∈ Finset.range 4, y^i/(i.factorial:ℝ)) = 1 + y + y^2/2 + y^3/6 := by
    norm_num [Finset.sum_range_succ]
  have h := Real.sum_le_exp_of_nonneg (le_of_lt hy) 4
  rw [hsum] at h
  have hy3 : y^3/6 ≤ Real.exp y := by nlinarith [sq_nonneg y, hy]
  rw [Real.exp_neg, inv_eq_one_div]
  have hpos : 0 < y^3/6 := by positivity
  calc (1:ℝ)/Real.exp y ≤ 1/(y^3/6) := one_div_le_one_div_of_le hpos hy3
    _ = 6/y^3 := by ring

/-- Lower bound for the numerator: for `0 < c ≤ 1` and `L ≥ 1`,
`L^(18/7) ≤ c * ((L/c)^(6/7))^3`. -/
lemma num_lower_rpow (L cvk : ℝ) (hcvk0 : 0 < cvk) (hcvk1 : cvk ≤ 1) (hL : 1 ≤ L) :
    L ^ (18 / 7 : ℝ) ≤ cvk * ((L / cvk) ^ (6 / 7 : ℝ)) ^ 3 := by
  have hLpos : 0 < L := by linarith
  have hx : 0 < L/cvk := by positivity
  have hx0 : 0 ≤ L/cvk := le_of_lt hx
  have hstep : ((L / cvk) ^ (6 / 7 : ℝ)) ^ 3 = (L / cvk) ^ (18 / 7 : ℝ) := by
    calc ((L / cvk) ^ (6 / 7 : ℝ)) ^ 3
        = ((L / cvk) ^ (6 / 7 : ℝ)) ^ (3 : ℝ) := (Real.rpow_natCast _ 3).symm
      _ = (L / cvk) ^ ((6 / 7 : ℝ) * 3) := (Real.rpow_mul hx0 (6 / 7 : ℝ) 3).symm
      _ = (L / cvk) ^ (18 / 7 : ℝ) := by norm_num
  have hLc : L = cvk * (L/cvk) := by field_simp
  have h1 : (L/cvk) * (L/cvk)^(11/7:ℝ) = (L/cvk)^(18/7:ℝ) := by
    calc (L/cvk) * (L/cvk)^(11/7:ℝ) = (L/cvk)^(1:ℝ) * (L/cvk)^(11/7:ℝ) := by rw [Real.rpow_one]
      _ = (L/cvk)^(1 + 11/7:ℝ) := (Real.rpow_add hx 1 (11/7:ℝ)).symm
      _ = (L/cvk)^(18/7:ℝ) := by norm_num
  have key : cvk * (L/cvk)^(18/7:ℝ) = L * (L/cvk)^(11/7:ℝ) := by
    calc cvk * (L/cvk)^(18/7:ℝ) = cvk * ((L/cvk) * (L/cvk)^(11/7:ℝ)) := by rw [h1]
      _ = cvk * (L/cvk) * (L/cvk)^(11/7:ℝ) := by ring
      _ = L * (L/cvk)^(11/7:ℝ) := by rw [← hLc]
  have hge : L * L^(11/7:ℝ) ≤ L * (L/cvk)^(11/7:ℝ) := by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hLpos)
    apply Real.rpow_le_rpow (le_of_lt hLpos) _ (by norm_num : (0:ℝ) ≤ 11/7)
    rw [le_div_iff₀ hcvk0]
    have : L * cvk ≤ L * 1 := mul_le_mul_of_nonneg_left hcvk1 (le_of_lt hLpos)
    linarith
  have hLL : L * L^(11/7:ℝ) = L^(18/7:ℝ) := by
    calc L * L^(11/7:ℝ) = L^(1:ℝ) * L^(11/7:ℝ) := by rw [Real.rpow_one]
      _ = L^(1 + 11/7:ℝ) := (Real.rpow_add hLpos 1 (11/7:ℝ)).symm
      _ = L^(18/7:ℝ) := by norm_num
  calc L^(18/7:ℝ) = L * L^(11/7:ℝ) := hLL.symm
    _ ≤ L * (L/cvk)^(11/7:ℝ) := hge
    _ = cvk * (L/cvk)^(18/7:ℝ) := key.symm
    _ = cvk * ((L/cvk)^(6/7:ℝ))^3 := by rw [hstep]

/-- Upper bound for the denominator: for `0 < c ≤ 1` and `L ≥ 1`,
`L^2 * log (c^(6/7) * L^(1/7) + 2) ≤ 2 * L^(15/7)`. -/
lemma den_upper_rpow (L cvk : ℝ) (hcvk0 : 0 < cvk) (hcvk1 : cvk ≤ 1) (hL : 1 ≤ L) :
    L ^ 2 * Real.log (cvk ^ (6 / 7 : ℝ) * L ^ (1 / 7 : ℝ) + 2) ≤ 2 * L ^ (15 / 7 : ℝ) := by
  have hLpos : 0 < L := by linarith
  have hL17pos : 0 < L^(1/7:ℝ) := Real.rpow_pos_of_pos hLpos _
  have ha1 : cvk^(6/7:ℝ) ≤ 1 := Real.rpow_le_one (le_of_lt hcvk0) hcvk1 (by norm_num)
  have ha2 : cvk^(6/7:ℝ) * L^(1/7:ℝ) ≤ L^(1/7:ℝ) := by
    simpa using mul_le_mul_of_nonneg_right ha1 (le_of_lt hL17pos)
  have ha3 : cvk^(6/7:ℝ) * L^(1/7:ℝ) + 2 ≤ L^(1/7:ℝ) + 2 := by linarith
  have hpos : 0 < cvk^(6/7:ℝ) * L^(1/7:ℝ) + 2 := by positivity
  have hlog : Real.log (cvk^(6/7:ℝ) * L^(1/7:ℝ) + 2) ≤ 2 * L^(1/7:ℝ) := by
    have h1 : Real.log (cvk^(6/7:ℝ) * L^(1/7:ℝ) + 2) ≤ Real.log (L^(1/7:ℝ) + 2) :=
      Real.log_le_log hpos ha3
    have h2 : Real.log (L^(1/7:ℝ) + 2) ≤ L^(1/7:ℝ) + 1 := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < L^(1/7:ℝ) + 2)
      linarith
    have h3 : L^(1/7:ℝ) + 1 ≤ 2 * L^(1/7:ℝ) := by
      have := Real.one_le_rpow hL (by norm_num : (0:ℝ) ≤ 1/7)
      linarith
    linarith
  have h2 : L^2 * Real.log (cvk^(6/7:ℝ) * L^(1/7:ℝ) + 2) ≤ L^2 * (2 * L^(1/7:ℝ)) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have h3 : L^2 * (2 * L^(1/7:ℝ)) = 2 * L^(15/7:ℝ) := by
    rw [show L^2 = L^(2:ℝ) from (Real.rpow_natCast L 2).symm]
    calc L^(2:ℝ) * (2 * L^(1/7:ℝ)) = 2 * (L^(2:ℝ) * L^(1/7:ℝ)) := by ring
      _ = 2 * L^(2 + 1/7:ℝ) := by rw [Real.rpow_add hLpos 2 (1/7:ℝ)]
      _ = 2 * L^(15/7:ℝ) := by norm_num
  rw [h3] at h2
  exact h2

/-- Tail bound: for `L ≥ 1`,
`(1 + L / log 2) * exp (-(L^(3/7) / 2)) ≤ 200`. -/
lemma exp_tail_bound_aux (L : ℝ) (hL : 1 ≤ L) :
    (1 + L / Real.log 2) * Real.exp (-(L ^ (3 / 7 : ℝ) / 2)) ≤ 200 := by
  have hLpos : 0 < L := by linarith
  have hLpowpos : 0 < L^(9/7:ℝ) := Real.rpow_pos_of_pos hLpos _
  have hypos : 0 < L^(3/7:ℝ)/2 := by
    have : 0 < L^(3/7:ℝ) := Real.rpow_pos_of_pos hLpos _
    linarith
  have hexp := exp_neg_le_cube (L^(3/7:ℝ)/2) hypos
  have hL37 : (L^(3/7:ℝ))^3 = L^(9/7:ℝ) := by
    calc (L^(3/7:ℝ))^3 = (L^(3/7:ℝ))^(3:ℝ) := (Real.rpow_natCast _ 3).symm
      _ = L^((3/7:ℝ)*3) := (Real.rpow_mul (le_of_lt hLpos) (3/7:ℝ) 3).symm
      _ = L^(9/7:ℝ) := by norm_num
  have hy3 : (L^(3/7:ℝ)/2)^3 = L^(9/7:ℝ)/8 := by
    rw [div_pow, hL37]; norm_num
  have hexp2 : Real.exp (-(L^(3/7:ℝ)/2)) ≤ 48/L^(9/7:ℝ) := by
    rw [hy3] at hexp
    have hc : 6/(L^(9/7:ℝ)/8) = 48/L^(9/7:ℝ) := by
      field_simp
      ring
    rw [hc] at hexp
    exact hexp
  have hlog2pos : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hLpow : L ≤ L^(9/7:ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (1:ℝ) ≤ 9/7)
    rwa [Real.rpow_one] at this
  have h1 : (1 + L/Real.log 2) ≤ (1 + 2*L) := by
    have h2 : (1:ℝ) ≤ 2*Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hmul : L * 1 ≤ L * (2*Real.log 2) := mul_le_mul_of_nonneg_left h2 (le_of_lt hLpos)
    have : L/Real.log 2 ≤ 2*L := by
      rw [div_le_iff₀ hlog2pos]
      nlinarith [hmul]
    linarith
  have h3 : (1 + 2*L) * (48/L^(9/7:ℝ)) ≤ 200 := by
    have heq : (1 + 2*L) * (48/L^(9/7:ℝ)) = 48*(1+2*L)/L^(9/7:ℝ) := by ring
    rw [heq, div_le_iff₀ hLpowpos]
    have ha : 48*(1+2*L) ≤ 200*L := by nlinarith [hL]
    have hb : 200*L ≤ 200*L^(9/7:ℝ) := by nlinarith [hLpow]
    linarith
  calc (1 + L / Real.log 2) * Real.exp (-(L ^ (3 / 7 : ℝ) / 2))
      ≤ (1 + L / Real.log 2) * (48/L^(9/7:ℝ)) := by
        apply mul_le_mul_of_nonneg_left hexp2 (by positivity)
    _ ≤ (1 + 2*L) * (48/L^(9/7:ℝ)) := by
        apply mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ 200 := h3

theorem block_sum_uniform (cvk : ℝ) (hcvk0 : 0 < cvk) (hcvk1 : cvk ≤ 1) :
    ∃ A : ℝ, 0 < A ∧ ∀ L : ℝ, 1 ≤ L →
      (1 + L / Real.log 2) * Real.exp (-(cvk * ((L / cvk) ^ (6 / 7 : ℝ)) ^ 3 /
        (L ^ 2 * Real.log (cvk ^ (6 / 7 : ℝ) * L ^ (1 / 7 : ℝ) + 2)))) ≤ A := by
  refine ⟨200, by norm_num, ?_⟩
  intro L hL
  have hLpos : 0 < L := by linarith
  have hN : L^(18/7:ℝ) ≤ cvk * ((L/cvk)^(6/7:ℝ))^3 := num_lower_rpow L cvk hcvk0 hcvk1 hL
  have hDle : L^2 * Real.log (cvk^(6/7:ℝ)*L^(1/7:ℝ)+2) ≤ 2*L^(15/7:ℝ) :=
    den_upper_rpow L cvk hcvk0 hcvk1 hL
  have hDpos : 0 < L^2 * Real.log (cvk^(6/7:ℝ)*L^(1/7:ℝ)+2) := by
    have harg : 1 < cvk^(6/7:ℝ)*L^(1/7:ℝ) + 2 := by
      have h2 : 0 < L^(1/7:ℝ) := Real.rpow_pos_of_pos hLpos _
      have h3 : 0 < cvk^(6/7:ℝ) := Real.rpow_pos_of_pos hcvk0 _
      nlinarith [mul_pos h3 h2]
    have hlog : 0 < Real.log (cvk^(6/7:ℝ)*L^(1/7:ℝ)+2) := Real.log_pos harg
    exact mul_pos (by positivity) hlog
  have hratio : L^(18/7:ℝ)/(2*L^(15/7:ℝ)) ≤
      (cvk * ((L/cvk)^(6/7:ℝ))^3)/(L^2 * Real.log (cvk^(6/7:ℝ)*L^(1/7:ℝ)+2)) :=
    div_le_div₀ (by positivity) hN hDpos hDle
  have hND : L^(18/7:ℝ)/(2*L^(15/7:ℝ)) = L^(3/7:ℝ)/2 := by
    have hsplit : L^(3/7:ℝ) * L^(15/7:ℝ) = L^(18/7:ℝ) := by
      rw [← Real.rpow_add hLpos (3/7) (15/7)]; norm_num
    have hx : L^(15/7:ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hLpos _)
    rw [← hsplit]
    field_simp
  have hE : L^(3/7:ℝ)/2 ≤
      (cvk * ((L/cvk)^(6/7:ℝ))^3)/(L^2 * Real.log (cvk^(6/7:ℝ)*L^(1/7:ℝ)+2)) := by
    rw [← hND]; exact hratio
  have hexp : Real.exp (-(cvk * ((L/cvk)^(6/7:ℝ))^3 /
        (L^2 * Real.log (cvk^(6/7:ℝ)*L^(1/7:ℝ)+2)))) ≤ Real.exp (-(L^(3/7:ℝ)/2)) := by
    apply Real.exp_le_exp.mpr
    linarith [hE]
  calc (1 + L / Real.log 2) * Real.exp (-(cvk * ((L / cvk) ^ (6 / 7 : ℝ)) ^ 3 /
        (L ^ 2 * Real.log (cvk ^ (6 / 7 : ℝ) * L ^ (1 / 7 : ℝ) + 2))))
      ≤ (1 + L / Real.log 2) * Real.exp (-(L^(3/7:ℝ)/2)) := by
        apply mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ 200 := exp_tail_bound_aux L hL

end Work.BMF.VKChain
