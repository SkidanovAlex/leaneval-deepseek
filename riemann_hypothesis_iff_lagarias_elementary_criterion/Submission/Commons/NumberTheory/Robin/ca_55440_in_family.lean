import Mathlib
import Submission.Commons.NumberTheory.Robin.caMu_ge_iff_caF
import Submission.Commons.Analysis.Real.log_one_add_lower

open scoped BigOperators

namespace Commons.NumberTheory.Robin

noncomputable section

/-! Certified log bounds (rational), used with ε := 1/30. -/

private lemma log2_lo : (1 / 2 : ℝ) < Real.log 2 := by
  have h := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith

private lemma log2_hi : Real.log 2 < (7 / 10 : ℝ) := by
  have h := Real.log_two_lt_d9
  norm_num at h ⊢
  linarith

private lemma log3_lo : (1 : ℝ) < Real.log 3 := by
  have he : Real.exp 1 < 3 := Real.exp_one_lt_three
  have h := Real.log_lt_log (Real.exp_pos 1) he
  simpa using h

private lemma log3_hi : Real.log 3 < (11 / 10 : ℝ) := by
  have h := Real.log_three_lt_d9
  norm_num at h ⊢
  linarith

private lemma log5_lo : (1 : ℝ) < Real.log 5 := by
  have h4 : Real.log 4 < Real.log 5 := Real.log_lt_log (by norm_num) (by norm_num : (4 : ℝ) < (5 : ℝ))
  have h4' : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num]
    rw [Real.log_pow]
    norm_num
  have h2 : (1 : ℝ) < 2 * Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  calc
    (1 : ℝ) < 2 * Real.log 2 := h2
    _ = Real.log 4 := h4'.symm
    _ < Real.log 5 := h4

private lemma log5_hi : Real.log 5 < (5 / 3 : ℝ) := by
  have h := Real.log_five_lt_d9
  norm_num at h ⊢
  linarith

private lemma log7_hi : Real.log (7 : ℝ) < (21 / 10 : ℝ) := by
  have h1 : Real.log (7 : ℝ) ≤ Real.log (8 : ℝ) := Real.log_le_log (by norm_num) (by norm_num : (7 : ℝ) ≤ (8 : ℝ))
  have h8 : Real.log (8 : ℝ) = 3 * Real.log (2 : ℝ) := by
    rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num]
    rw [Real.log_pow]
    norm_num
  have h1' : Real.log (7 : ℝ) ≤ 3 * Real.log (2 : ℝ) := by
    rw [h8] at h1
    exact h1
  calc
    Real.log (7 : ℝ) ≤ 3 * Real.log (2 : ℝ) := h1'
    _ < 21 / 10 := by
      have h := Real.log_two_lt_d9
      norm_num at h ⊢
      linarith

private lemma log10_eq : Real.log (10 : ℝ) = Real.log (2 : ℝ) + Real.log (5 : ℝ) := by
  rw [show (10 : ℝ) = (2 * 5 : ℝ) by norm_num]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0)]

private lemma log11_lo : (3 / 2 : ℝ) < Real.log (11 : ℝ) := by
  have h11 : Real.log (10 : ℝ) < Real.log (11 : ℝ) := Real.log_lt_log (by norm_num) (by norm_num : (10 : ℝ) < (11 : ℝ))
  calc
    (3 / 2 : ℝ) = 1 / 2 + 1 := by norm_num
    _ < Real.log 2 + Real.log 5 := by
      have h2 := log2_lo
      have h5 := log5_lo
      linarith
    _ = Real.log 10 := log10_eq.symm
    _ < Real.log 11 := h11

private lemma log11_hi : Real.log (11 : ℝ) < (37 / 15 : ℝ) := by
  have hsplit : Real.log (11 : ℝ) = Real.log (2 : ℝ) + Real.log (5 : ℝ) + Real.log (11 / 10 : ℝ) := by
    rw [show (11 : ℝ) = (10 : ℝ) * (11 / 10 : ℝ) by norm_num]
    rw [Real.log_mul (by norm_num : (10 : ℝ) ≠ 0) (by norm_num : (11 / 10 : ℝ) ≠ 0)]
    rw [show (10 : ℝ) = (2 * 5 : ℝ) by norm_num]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0)]
    ring_nf
  have h1110 : Real.log (11 / 10 : ℝ) < 1 / 10 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : 0 < (11 / 10 : ℝ)) (by norm_num : (11 / 10 : ℝ) ≠ 1)
    linarith
  rw [hsplit]
  have h2 := log2_hi
  have h5 := log5_hi
  linarith

private lemma log13_lo : (30 / 13 : ℝ) < Real.log (13 : ℝ) := by
  have hsplit : Real.log (13 : ℝ) = 2 * Real.log (3 : ℝ) + Real.log (13 / 9 : ℝ) := by
    rw [show (13 : ℝ) = (9 : ℝ) * (13 / 9 : ℝ) by norm_num]
    rw [Real.log_mul (by norm_num : (9 : ℝ) ≠ 0) (by norm_num : (13 / 9 : ℝ) ≠ 0)]
    rw [show (9 : ℝ) = (3 : ℝ) ^ (2 : ℕ) by norm_num]
    rw [Real.log_pow]
    ring_nf
  have h3 : (2 : ℝ) < 2 * Real.log 3 := by
    have h := log3_lo
    linarith
  have hq : (28 / 81 : ℝ) ≤ Real.log (13 / 9 : ℝ) := by
    have h := Commons.Analysis.Real.log_one_add_lower (u₀ := (4 / 9 : ℝ)) (u := (4 / 9 : ℝ))
      (by norm_num) (by norm_num) (le_rfl)
    have hfrac : (13 / 9 : ℝ) = 1 + (4 / 9 : ℝ) := by norm_num
    rw [← hfrac] at h
    have hquad : (28 / 81 : ℝ) ≤ (4 / 9 : ℝ) - (4 / 9 : ℝ) ^ 2 / 2 := by norm_num
    exact le_trans hquad h
  rw [hsplit]
  have h4 : (2 : ℝ) + 28 / 81 ≤ 2 * Real.log 3 + Real.log (13 / 9) := by linarith
  have hnum : (30 / 13 : ℝ) < 2 + 28 / 81 := by norm_num
  linarith

private lemma log1p_lt (x : ℝ) (hx : 0 < x) : Real.log (1 + x) < x := by
  have h := Real.log_lt_sub_one_of_pos (by positivity : 0 < 1 + x) (by nlinarith : 1 + x ≠ 1)
  linarith

private lemma log1p_quad_ge (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    x - x ^ 2 / 2 ≤ Real.log (1 + x) := by
  exact Commons.Analysis.Real.log_one_add_lower (u₀ := x) (u := x) hx1 hx0 le_rfl

/-! `F(p,1) < 1/(p·log p) ≤ 1/(13·log 13) < 1/30` for p ≥ 13 (closed form). -/

private lemma caF1_lt_one_div (p : ℕ) (hp : 2 ≤ p) :
    Real.log (((p : ℝ) ^ (1 + 1) - 1) / (((p : ℝ) ^ (1 + 1)) - (p : ℝ))) / Real.log (p : ℝ)
      < 1 / ((p : ℝ) * Real.log (p : ℝ)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hp1r : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1r
  have hpm1 : (p : ℝ) - 1 ≠ 0 := by
    have hne : (p : ℝ) ≠ 1 := by exact_mod_cast (by omega : p ≠ 1)
    exact sub_ne_zero.mpr hne
  have hmain : ((p : ℝ) * (p : ℝ) - 1) / ((p : ℝ) * (p : ℝ) - (p : ℝ)) = 1 + 1 / (p : ℝ) := by
    have hnum : (p : ℝ) * (p : ℝ) - 1 = ((p : ℝ) + 1) * ((p : ℝ) - 1) := by ring
    have hden : (p : ℝ) * (p : ℝ) - (p : ℝ) = (p : ℝ) * ((p : ℝ) - 1) := by ring
    rw [hnum, hden]
    field_simp [hp0, hpm1]
  have hq : (((p : ℝ) ^ (1 + 1) - 1) / (((p : ℝ) ^ (1 + 1)) - (p : ℝ))) = 1 + 1 / (p : ℝ) := by
    rw [show (p : ℝ) ^ (1 + 1) = (p : ℝ) * (p : ℝ) by rw [pow_two]]
    exact hmain
  rw [hq]
  have hloglt : Real.log (1 + 1 / (p : ℝ)) < 1 / (p : ℝ) := by
    have h := log1p_lt (1 / (p : ℝ)) (by positivity)
    simpa using h
  have hden : 1 / ((p : ℝ) * Real.log (p : ℝ)) = (1 / (p : ℝ)) / Real.log (p : ℝ) := by
    field_simp [ne_of_gt (by exact_mod_cast (by omega : 0 < p) : (0 : ℝ) < (p : ℝ)), hlogp.ne']
  rw [hden]
  rw [div_lt_div_iff₀ hlogp hlogp]
  have hmul : Real.log (1 + 1 / (p : ℝ)) * Real.log (p : ℝ) < (1 / (p : ℝ)) * Real.log (p : ℝ) :=
    mul_lt_mul_of_pos_right hloglt hlogp
  nlinarith

private lemma one_div_p_log_le (p : ℕ) (hp : 13 ≤ p) :
    (1 / ((p : ℝ) * Real.log (p : ℝ))) ≤ 1 / ((13 : ℝ) * Real.log (13 : ℝ)) := by
  have hpR : (13 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < p))
  have hlog13 : 0 < Real.log (13 : ℝ) := Real.log_pos (by norm_num)
  have hlogge : Real.log (13 : ℝ) ≤ Real.log (p : ℝ) := Real.log_le_log (by norm_num) hpR
  have hpos13 : (0 : ℝ) < 13 := by norm_num
  have hmulge : (13 : ℝ) * Real.log (13 : ℝ) ≤ (p : ℝ) * Real.log (p : ℝ) := by
    have h1 : (13 : ℝ) * Real.log (p : ℝ) ≤ (p : ℝ) * Real.log (p : ℝ) :=
      mul_le_mul_of_nonneg_right hpR (le_of_lt hlogp)
    have h2 : (13 : ℝ) * Real.log (13 : ℝ) ≤ (13 : ℝ) * Real.log (p : ℝ) :=
      mul_le_mul_of_nonneg_left hlogge (by norm_num)
    exact le_trans h2 h1
  have hden_pos : 0 < (13 : ℝ) * Real.log (13 : ℝ) := mul_pos hpos13 hlog13
  exact one_div_le_one_div_of_le hden_pos hmulge

private lemma c11 (p : ℕ) (hp : 13 ≤ p) :
    Real.log (((p : ℝ) ^ (1 + 1) - 1) / (((p : ℝ) ^ (1 + 1)) - (p : ℝ))) / Real.log (p : ℝ) < (1 / 30 : ℝ) := by
  have h1 := caF1_lt_one_div p (by omega : 2 ≤ p)
  have h2 := one_div_p_log_le p hp
  have h3 : 1 / ((13 : ℝ) * Real.log (13 : ℝ)) < 1 / 30 := by
    have hpos : (0 : ℝ) < (13 : ℝ) * Real.log 13 :=
      mul_pos (by norm_num) (Real.log_pos (by norm_num : (1 : ℝ) < (13 : ℝ)))
    have h13' : (30 / 13 : ℝ) < Real.log 13 := log13_lo
    have hmul : (30 : ℝ) < (13 : ℝ) * Real.log 13 := by
      have hm := mul_lt_mul_of_pos_right h13' (by norm_num : (0 : ℝ) < 13)
      norm_num at hm
      nlinarith
    exact (div_lt_div_iff₀ hpos (by norm_num : (0 : ℝ) < 30)).mpr (by simpa using hmul)
  exact lt_trans (lt_of_lt_of_le h1 h2) h3

/-! Certified inequalities ε = 1/30 ≤ F(p,k) and F(p,k) < ε for p ∈ {2,3,5,7,11}. -/

private lemma c1 : (1 / 30 : ℝ) ≤
    Real.log (((2 : ℝ) ^ (4 + 1) - 1) / (((2 : ℝ) ^ (4 + 1)) - (2 : ℝ))) / Real.log (2 : ℝ) := by
  have hQ : (((2 : ℝ) ^ (4 + 1) - 1) / (((2 : ℝ) ^ (4 + 1)) - (2 : ℝ))) = (31 / 30 : ℝ) := by norm_num
  rw [hQ]
  have hq : (59 / 1800 : ℝ) ≤ Real.log (31 / 30 : ℝ) := by
    have hquad := log1p_quad_ge (1 / 30 : ℝ) (by norm_num) (by norm_num)
    have hf : (31 / 30 : ℝ) = 1 + (1 / 30 : ℝ) := by norm_num
    rw [← hf] at hquad
    have hquad2 : (59 / 1800 : ℝ) ≤ (1 / 30 : ℝ) - (1 / 30 : ℝ) ^ 2 / 2 := by norm_num
    exact le_trans hquad2 hquad
  have hmain : Real.log (2 : ℝ) ≤ 30 * Real.log (31 / 30 : ℝ) := by
    have h1 : Real.log (2 : ℝ) ≤ 7 / 10 := log2_hi.le
    have h2 : (7 / 10 : ℝ) ≤ 59 / 60 := by norm_num
    have h3 : (59 / 60 : ℝ) ≤ 30 * Real.log (31 / 30 : ℝ) := by
      calc
        (59 / 60 : ℝ) = 30 * (59 / 1800) := by norm_num
        _ ≤ 30 * Real.log (31 / 30 : ℝ) := mul_le_mul_of_nonneg_left hq (by norm_num)
    exact le_trans (le_trans h1 h2) h3
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num : (1 : ℝ) < (2 : ℝ))
  rw [le_div_iff₀ hlog2]
  nlinarith

private lemma c2 : Real.log (((2 : ℝ) ^ (5 + 1) - 1) / (((2 : ℝ) ^ (5 + 1)) - (2 : ℝ))) / Real.log (2 : ℝ)
    < (1 / 30 : ℝ) := by
  have hQ : (((2 : ℝ) ^ (5 + 1) - 1) / (((2 : ℝ) ^ (5 + 1)) - (2 : ℝ))) = (63 / 62 : ℝ) := by norm_num
  rw [hQ]
  have h1 : Real.log (63 / 62 : ℝ) < 1 / 62 := by
    have h := log1p_lt (1 / 62 : ℝ) (by norm_num)
    have hf : (63 / 62 : ℝ) = 1 + (1 / 62 : ℝ) := by norm_num
    rwa [hf]
  have h2 : 30 * Real.log (63 / 62 : ℝ) < 30 * (1 / 62 : ℝ) :=
    mul_lt_mul_of_pos_left h1 (by norm_num : (0 : ℝ) < 30)
  have h3 : (30 * (1 / 62 : ℝ) : ℝ) < 1 / 2 := by norm_num
  have hlt : 30 * Real.log (63 / 62 : ℝ) < Real.log (2 : ℝ) :=
    lt_trans (lt_trans h2 h3) log2_lo
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num : (1 : ℝ) < (2 : ℝ))
  rw [div_lt_iff₀ hlog2]
  nlinarith

private lemma c3 : (1 / 30 : ℝ) ≤
    Real.log (((3 : ℝ) ^ (2 + 1) - 1) / (((3 : ℝ) ^ (2 + 1)) - (3 : ℝ))) / Real.log (3 : ℝ) := by
  have hQ : (((3 : ℝ) ^ (2 + 1) - 1) / (((3 : ℝ) ^ (2 + 1)) - (3 : ℝ))) = (13 / 12 : ℝ) := by norm_num
  rw [hQ]
  have hq : (23 / 288 : ℝ) ≤ Real.log (13 / 12 : ℝ) := by
    have hquad := log1p_quad_ge (1 / 12 : ℝ) (by norm_num) (by norm_num)
    have hf : (13 / 12 : ℝ) = 1 + (1 / 12 : ℝ) := by norm_num
    rw [← hf] at hquad
    have hquad2 : (23 / 288 : ℝ) ≤ (1 / 12 : ℝ) - (1 / 12 : ℝ) ^ 2 / 2 := by norm_num
    exact le_trans hquad2 hquad
  have hmain : Real.log (3 : ℝ) ≤ 30 * Real.log (13 / 12 : ℝ) := by
    have h1 : Real.log (3 : ℝ) ≤ 11 / 10 := log3_hi.le
    have h2 : (11 / 10 : ℝ) ≤ 115 / 48 := by norm_num
    have h3 : (115 / 48 : ℝ) ≤ 30 * Real.log (13 / 12 : ℝ) := by
      calc
        (115 / 48 : ℝ) = 30 * (23 / 288) := by norm_num
        _ ≤ 30 * Real.log (13 / 12 : ℝ) := mul_le_mul_of_nonneg_left hq (by norm_num)
    exact le_trans (le_trans h1 h2) h3
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num : (1 : ℝ) < (3 : ℝ))
  rw [le_div_iff₀ hlog3]
  nlinarith

private lemma c4 : Real.log (((3 : ℝ) ^ (3 + 1) - 1) / (((3 : ℝ) ^ (3 + 1)) - (3 : ℝ))) / Real.log (3 : ℝ)
    < (1 / 30 : ℝ) := by
  have hQ : (((3 : ℝ) ^ (3 + 1) - 1) / (((3 : ℝ) ^ (3 + 1)) - (3 : ℝ))) = (40 / 39 : ℝ) := by norm_num
  rw [hQ]
  have h1 : Real.log (40 / 39 : ℝ) < 1 / 39 := by
    have h := log1p_lt (1 / 39 : ℝ) (by norm_num)
    have hf : (40 / 39 : ℝ) = 1 + (1 / 39 : ℝ) := by norm_num
    rwa [hf]
  have h2 : 30 * Real.log (40 / 39 : ℝ) < 30 * (1 / 39 : ℝ) :=
    mul_lt_mul_of_pos_left h1 (by norm_num : (0 : ℝ) < 30)
  have h3 : (30 * (1 / 39 : ℝ) : ℝ) < 1 := by norm_num
  have hlt : 30 * Real.log (40 / 39 : ℝ) < Real.log (3 : ℝ) :=
    lt_trans (lt_trans h2 h3) log3_lo
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num : (1 : ℝ) < (3 : ℝ))
  rw [div_lt_iff₀ hlog3]
  nlinarith

private lemma c5 : (1 / 30 : ℝ) ≤
    Real.log (((5 : ℝ) ^ (1 + 1) - 1) / (((5 : ℝ) ^ (1 + 1)) - (5 : ℝ))) / Real.log (5 : ℝ) := by
  have hQ : (((5 : ℝ) ^ (1 + 1) - 1) / (((5 : ℝ) ^ (1 + 1)) - (5 : ℝ))) = (6 / 5 : ℝ) := by norm_num
  rw [hQ]
  have hq : (9 / 50 : ℝ) ≤ Real.log (6 / 5 : ℝ) := by
    have hquad := log1p_quad_ge (1 / 5 : ℝ) (by norm_num) (by norm_num)
    have hf : (6 / 5 : ℝ) = 1 + (1 / 5 : ℝ) := by norm_num
    rw [← hf] at hquad
    have hquad2 : (9 / 50 : ℝ) ≤ (1 / 5 : ℝ) - (1 / 5 : ℝ) ^ 2 / 2 := by norm_num
    exact le_trans hquad2 hquad
  have hmain : Real.log (5 : ℝ) ≤ 30 * Real.log (6 / 5 : ℝ) := by
    have h1 : Real.log (5 : ℝ) ≤ 5 / 3 := log5_hi.le
    have h2 : (5 / 3 : ℝ) ≤ 27 / 5 := by norm_num
    have h3 : (27 / 5 : ℝ) ≤ 30 * Real.log (6 / 5 : ℝ) := by
      calc
        (27 / 5 : ℝ) = 30 * (9 / 50) := by norm_num
        _ ≤ 30 * Real.log (6 / 5 : ℝ) := mul_le_mul_of_nonneg_left hq (by norm_num)
    exact le_trans (le_trans h1 h2) h3
  have hlog5 : 0 < Real.log (5 : ℝ) := Real.log_pos (by norm_num : (1 : ℝ) < (5 : ℝ))
  rw [le_div_iff₀ hlog5]
  nlinarith

private lemma c6 : Real.log (((5 : ℝ) ^ (2 + 1) - 1) / (((5 : ℝ) ^ (2 + 1)) - (5 : ℝ))) / Real.log (5 : ℝ)
    < (1 / 30 : ℝ) := by
  have hQ : (((5 : ℝ) ^ (2 + 1) - 1) / (((5 : ℝ) ^ (2 + 1)) - (5 : ℝ))) = (31 / 30 : ℝ) := by norm_num
  rw [hQ]
  have h1 : Real.log (31 / 30 : ℝ) < 1 / 30 := by
    have h := log1p_lt (1 / 30 : ℝ) (by norm_num)
    have hf : (31 / 30 : ℝ) = 1 + (1 / 30 : ℝ) := by norm_num
    rwa [hf]
  have h2 : 30 * Real.log (31 / 30 : ℝ) < 30 * (1 / 30 : ℝ) :=
    mul_lt_mul_of_pos_left h1 (by norm_num : (0 : ℝ) < 30)
  have hlt : 30 * Real.log (31 / 30 : ℝ) < Real.log (5 : ℝ) := by
    calc
      30 * Real.log (31 / 30 : ℝ) < 30 * (1 / 30 : ℝ) := h2
      _ = 1 := by norm_num
      _ < Real.log 5 := log5_lo
  have hlog5 : 0 < Real.log (5 : ℝ) := Real.log_pos (by norm_num : (1 : ℝ) < (5 : ℝ))
  rw [div_lt_iff₀ hlog5]
  nlinarith

private lemma c7 : (1 / 30 : ℝ) ≤
    Real.log (((7 : ℝ) ^ (1 + 1) - 1) / (((7 : ℝ) ^ (1 + 1)) - (7 : ℝ))) / Real.log (7 : ℝ) := by
  have hQ : (((7 : ℝ) ^ (1 + 1) - 1) / (((7 : ℝ) ^ (1 + 1)) - (7 : ℝ))) = (8 / 7 : ℝ) := by norm_num
  rw [hQ]
  have hq : (13 / 98 : ℝ) ≤ Real.log (8 / 7 : ℝ) := by
    have hquad := log1p_quad_ge (1 / 7 : ℝ) (by norm_num) (by norm_num)
    have hf : (8 / 7 : ℝ) = 1 + (1 / 7 : ℝ) := by norm_num
    rw [← hf] at hquad
    have hquad2 : (13 / 98 : ℝ) ≤ (1 / 7 : ℝ) - (1 / 7 : ℝ) ^ 2 / 2 := by norm_num
    exact le_trans hquad2 hquad
  have hmain : Real.log (7 : ℝ) ≤ 30 * Real.log (8 / 7 : ℝ) := by
    have h1 : Real.log (7 : ℝ) ≤ 21 / 10 := log7_hi.le
    have h2 : (21 / 10 : ℝ) ≤ 195 / 49 := by norm_num
    have h3 : (195 / 49 : ℝ) ≤ 30 * Real.log (8 / 7 : ℝ) := by
      calc
        (195 / 49 : ℝ) = 30 * (13 / 98) := by norm_num
        _ ≤ 30 * Real.log (8 / 7 : ℝ) := mul_le_mul_of_nonneg_left hq (by norm_num)
    exact le_trans (le_trans h1 h2) h3
  have hlog7 : 0 < Real.log (7 : ℝ) := Real.log_pos (by norm_num : (1 : ℝ) < (7 : ℝ))
  rw [le_div_iff₀ hlog7]
  nlinarith

private lemma c8 : Real.log (((7 : ℝ) ^ (2 + 1) - 1) / (((7 : ℝ) ^ (2 + 1)) - (7 : ℝ))) / Real.log (7 : ℝ)
    < (1 / 30 : ℝ) := by
  have hQ : (((7 : ℝ) ^ (2 + 1) - 1) / (((7 : ℝ) ^ (2 + 1)) - (7 : ℝ))) = (57 / 56 : ℝ) := by norm_num
  rw [hQ]
  have h1 : Real.log (57 / 56 : ℝ) < 1 / 56 := by
    have h := log1p_lt (1 / 56 : ℝ) (by norm_num)
    have hf : (57 / 56 : ℝ) = 1 + (1 / 56 : ℝ) := by norm_num
    rwa [hf]
  have h2 : 30 * Real.log (57 / 56 : ℝ) < 30 * (1 / 56 : ℝ) :=
    mul_lt_mul_of_pos_left h1 (by norm_num : (0 : ℝ) < 30)
  have h3 : (30 * (1 / 56 : ℝ) : ℝ) = 15 / 28 := by norm_num
  have h4 : (15 / 28 : ℝ) < Real.log (7 : ℝ) := by
    have h4a : Real.log (4 : ℝ) < Real.log (7 : ℝ) := Real.log_lt_log (by norm_num) (by norm_num : (4 : ℝ) < (7 : ℝ))
    have h4b : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num]
      rw [Real.log_pow]
      norm_num
    have hbig : (1 : ℝ) < Real.log (4 : ℝ) := by
      have h2lo := log2_lo
      rw [h4b]
      linarith
    calc
      (15 / 28 : ℝ) < 1 := by norm_num
      _ < Real.log 4 := hbig
      _ < Real.log 7 := h4a
  have hlt : 30 * Real.log (57 / 56 : ℝ) < Real.log (7 : ℝ) := by
    calc
      30 * Real.log (57 / 56 : ℝ) < 30 * (1 / 56 : ℝ) := h2
      _ = 15 / 28 := h3
      _ < Real.log 7 := h4
  have hlog7 : 0 < Real.log (7 : ℝ) := Real.log_pos (by norm_num : (1 : ℝ) < (7 : ℝ))
  rw [div_lt_iff₀ hlog7]
  nlinarith

private lemma c9 : (1 / 30 : ℝ) ≤
    Real.log (((11 : ℝ) ^ (1 + 1) - 1) / (((11 : ℝ) ^ (1 + 1)) - (11 : ℝ))) / Real.log (11 : ℝ) := by
  have hQ : (((11 : ℝ) ^ (1 + 1) - 1) / (((11 : ℝ) ^ (1 + 1)) - (11 : ℝ))) = (12 / 11 : ℝ) := by norm_num
  rw [hQ]
  have hq : (21 / 242 : ℝ) ≤ Real.log (12 / 11 : ℝ) := by
    have hquad := log1p_quad_ge (1 / 11 : ℝ) (by norm_num) (by norm_num)
    have hf : (12 / 11 : ℝ) = 1 + (1 / 11 : ℝ) := by norm_num
    rw [← hf] at hquad
    have hquad2 : (21 / 242 : ℝ) ≤ (1 / 11 : ℝ) - (1 / 11 : ℝ) ^ 2 / 2 := by norm_num
    exact le_trans hquad2 hquad
  have hmain : Real.log (11 : ℝ) ≤ 30 * Real.log (12 / 11 : ℝ) := by
    have h1 : Real.log (11 : ℝ) ≤ 37 / 15 := log11_hi.le
    have h2 : (37 / 15 : ℝ) ≤ 315 / 121 := by norm_num
    have h3 : (315 / 121 : ℝ) ≤ 30 * Real.log (12 / 11 : ℝ) := by
      calc
        (315 / 121 : ℝ) = 30 * (21 / 242) := by norm_num
        _ ≤ 30 * Real.log (12 / 11 : ℝ) := mul_le_mul_of_nonneg_left hq (by norm_num)
    exact le_trans (le_trans h1 h2) h3
  have hlog11 : 0 < Real.log (11 : ℝ) := Real.log_pos (by norm_num : (1 : ℝ) < (11 : ℝ))
  rw [le_div_iff₀ hlog11]
  nlinarith

private lemma c10 : Real.log (((11 : ℝ) ^ (2 + 1) - 1) / (((11 : ℝ) ^ (2 + 1)) - (11 : ℝ))) / Real.log (11 : ℝ)
    < (1 / 30 : ℝ) := by
  have hQ : (((11 : ℝ) ^ (2 + 1) - 1) / (((11 : ℝ) ^ (2 + 1)) - (11 : ℝ))) = (133 / 132 : ℝ) := by norm_num
  rw [hQ]
  have h1 : Real.log (133 / 132 : ℝ) < 1 / 132 := by
    have h := log1p_lt (1 / 132 : ℝ) (by norm_num)
    have hf : (133 / 132 : ℝ) = 1 + (1 / 132 : ℝ) := by norm_num
    rwa [hf]
  have h2 : 30 * Real.log (133 / 132 : ℝ) < 30 * (1 / 132 : ℝ) :=
    mul_lt_mul_of_pos_left h1 (by norm_num : (0 : ℝ) < 30)
  have h3 : (30 * (1 / 132 : ℝ) : ℝ) = 5 / 22 := by norm_num
  have hlt : 30 * Real.log (133 / 132 : ℝ) < Real.log (11 : ℝ) := by
    calc
      30 * Real.log (133 / 132 : ℝ) < 30 * (1 / 132 : ℝ) := h2
      _ = 5 / 22 := h3
      _ < 3 / 2 := by norm_num
      _ < Real.log 11 := log11_lo
  have hlog11 : 0 < Real.log (11 : ℝ) := Real.log_pos (by norm_num : (1 : ℝ) < (11 : ℝ))
  rw [div_lt_iff₀ hlog11]
  nlinarith

/-! Exponent determination via `caMu_ge_iff_caF`. -/

private abbrev mu (p : ℕ) (ε : ℝ) : ℝ :=
  Real.log (((p : ℝ) ^ (1 + ε) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)

private abbrev expo (p : ℕ) (ε : ℝ) : ℕ := Nat.floor (mu p ε)

private abbrev term (p : ℕ) (ε : ℝ) : ℕ := p ^ (expo p ε)

private lemma expo2 : expo 2 (1/30) = 4 := by
  unfold expo
  have hge : (4 : ℕ) ≤ Nat.floor (mu 2 (1/30)) :=
    (Nat.le_floor_iff' (by norm_num : (4 : ℕ) ≠ 0)).mpr (by
      simpa [mu] using (caMu_ge_iff_caF (p := 2) (ε := (1/30 : ℝ)) (k := 4) (by norm_num) (by norm_num) (by norm_num)).mpr c1)
  have hlt : Nat.floor (mu 2 (1/30)) < 5 := by
    refine (Nat.floor_lt' (by norm_num : (5 : ℕ) ≠ 0)).mpr ?_
    have hnot : ¬ (↑(5 : ℕ) : ℝ) ≤ mu 2 (1/30) := by
      intro h5
      have h := (caMu_ge_iff_caF (p := 2) (ε := (1/30 : ℝ)) (k := 5) (by norm_num) (by norm_num) (by norm_num)).mp h5
      exact (not_le_of_gt c2) h
    exact lt_of_not_ge hnot
  omega

private lemma expo3 : expo 3 (1/30) = 2 := by
  unfold expo
  have hge : (2 : ℕ) ≤ Nat.floor (mu 3 (1/30)) :=
    (Nat.le_floor_iff' (by norm_num : (2 : ℕ) ≠ 0)).mpr (by
      simpa [mu] using (caMu_ge_iff_caF (p := 3) (ε := (1/30 : ℝ)) (k := 2) (by norm_num) (by norm_num) (by norm_num)).mpr c3)
  have hlt : Nat.floor (mu 3 (1/30)) < 3 := by
    refine (Nat.floor_lt' (by norm_num : (3 : ℕ) ≠ 0)).mpr ?_
    have hnot : ¬ (↑(3 : ℕ) : ℝ) ≤ mu 3 (1/30) := by
      intro h3
      have h := (caMu_ge_iff_caF (p := 3) (ε := (1/30 : ℝ)) (k := 3) (by norm_num) (by norm_num) (by norm_num)).mp h3
      exact (not_le_of_gt c4) h
    exact lt_of_not_ge hnot
  omega

private lemma expo5 : expo 5 (1/30) = 1 := by
  unfold expo
  have hge : (1 : ℕ) ≤ Nat.floor (mu 5 (1/30)) :=
    (Nat.le_floor_iff' (by norm_num : (1 : ℕ) ≠ 0)).mpr (by
      simpa [mu] using (caMu_ge_iff_caF (p := 5) (ε := (1/30 : ℝ)) (k := 1) (by norm_num) (by norm_num) (by norm_num)).mpr c5)
  have hlt : Nat.floor (mu 5 (1/30)) < 2 := by
    refine (Nat.floor_lt' (by norm_num : (2 : ℕ) ≠ 0)).mpr ?_
    have hnot : ¬ (↑(2 : ℕ) : ℝ) ≤ mu 5 (1/30) := by
      intro h2
      have h := (caMu_ge_iff_caF (p := 5) (ε := (1/30 : ℝ)) (k := 2) (by norm_num) (by norm_num) (by norm_num)).mp h2
      exact (not_le_of_gt c6) h
    exact lt_of_not_ge hnot
  omega

private lemma expo7 : expo 7 (1/30) = 1 := by
  unfold expo
  have hge : (1 : ℕ) ≤ Nat.floor (mu 7 (1/30)) :=
    (Nat.le_floor_iff' (by norm_num : (1 : ℕ) ≠ 0)).mpr (by
      simpa [mu] using (caMu_ge_iff_caF (p := 7) (ε := (1/30 : ℝ)) (k := 1) (by norm_num) (by norm_num) (by norm_num)).mpr c7)
  have hlt : Nat.floor (mu 7 (1/30)) < 2 := by
    refine (Nat.floor_lt' (by norm_num : (2 : ℕ) ≠ 0)).mpr ?_
    have hnot : ¬ (↑(2 : ℕ) : ℝ) ≤ mu 7 (1/30) := by
      intro h2
      have h := (caMu_ge_iff_caF (p := 7) (ε := (1/30 : ℝ)) (k := 2) (by norm_num) (by norm_num) (by norm_num)).mp h2
      exact (not_le_of_gt c8) h
    exact lt_of_not_ge hnot
  omega

private lemma expo11 : expo 11 (1/30) = 1 := by
  unfold expo
  have hge : (1 : ℕ) ≤ Nat.floor (mu 11 (1/30)) :=
    (Nat.le_floor_iff' (by norm_num : (1 : ℕ) ≠ 0)).mpr (by
      simpa [mu] using (caMu_ge_iff_caF (p := 11) (ε := (1/30 : ℝ)) (k := 1) (by norm_num) (by norm_num) (by norm_num)).mpr c9)
  have hlt : Nat.floor (mu 11 (1/30)) < 2 := by
    refine (Nat.floor_lt' (by norm_num : (2 : ℕ) ≠ 0)).mpr ?_
    have hnot : ¬ (↑(2 : ℕ) : ℝ) ≤ mu 11 (1/30) := by
      intro h2
      have h := (caMu_ge_iff_caF (p := 11) (ε := (1/30 : ℝ)) (k := 2) (by norm_num) (by norm_num) (by norm_num)).mp h2
      exact (not_le_of_gt c10) h
    exact lt_of_not_ge hnot
  omega

private lemma expo_ge13 (p : ℕ) (hp13 : 13 ≤ p) : expo p (1/30) = 0 := by
  have hlt_mu : mu p (1/30) < (↑(1 : ℕ) : ℝ) := by
    have hnot : ¬ (↑(1 : ℕ) : ℝ) ≤ mu p (1/30) := by
      intro h1
      have h := (caMu_ge_iff_caF (p := p) (ε := (1/30 : ℝ)) (k := 1) (by omega : 2 ≤ p) (by norm_num) (by norm_num)).mp h1
      exact (not_le_of_gt (c11 p hp13)) h
    exact lt_of_not_ge hnot
  unfold expo
  have hfl : Nat.floor (mu p (1/30)) < 1 := (Nat.floor_lt' (by norm_num : (1 : ℕ) ≠ 0)).mpr hlt_mu
  omega

private lemma bound_13 : 13 ≤ Nat.ceil (Real.exp 60) + 2 := by
  have h1 : (61 : ℝ) ≤ Real.exp 60 := by
    have h := Real.add_one_le_exp (60 : ℝ)
    norm_num at h
    exact h
  have hc : Nat.ceil (61 : ℝ) ≤ Nat.ceil (Real.exp 60) := Nat.ceil_le_ceil h1
  have hc61 : Nat.ceil (61 : ℝ) = 61 := by simp
  have hbig : (61 : ℕ) ≤ Nat.ceil (Real.exp 60) := by simpa [hc61] using hc
  omega

private lemma small_filter_eq (B : ℕ) (hB : 13 ≤ B) :
    ((Finset.range B).filter Nat.Prime).filter (fun p : ℕ => p < 13) = ({2, 3, 5, 7, 11} : Finset ℕ) := by
  ext p
  simp
  constructor
  · intro h
    rcases h with ⟨⟨hpB, hpr⟩, hlt⟩
    have hprlt : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
      have hp2 : 2 ≤ p := hpr.two_le
      interval_cases p <;> norm_num at hpr
      all_goals norm_num
    simpa using hprlt
  · intro h
    have hmem : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by simpa using h
    rcases hmem with rfl | rfl | rfl | rfl | rfl
    all_goals
      constructor
      · constructor
        · omega
        · norm_num
      · norm_num

private lemma prod_eq_55440 (B : ℕ) (hB : 13 ≤ B) :
    (Finset.prod ((Finset.range B).filter Nat.Prime) (fun p : ℕ => term p (1/30))) = 55440 := by
  let P : Finset ℕ := (Finset.range B).filter Nat.Prime
  rw [← Finset.prod_filter_mul_prod_filter_not P (fun p : ℕ => p < 13) (fun p : ℕ => term p (1/30))]
  have hbig : (∏ p ∈ P.filter (fun p : ℕ => ¬ p < 13), term p (1/30)) = 1 := by
    apply Finset.prod_eq_one
    intro p hp
    have hng : ¬ p < 13 := (Finset.mem_filter.mp hp).2
    have hp13 : 13 ≤ p := by omega
    change p ^ (expo p (1/30)) = 1
    rw [expo_ge13 p hp13]
    simp
  have hsmall : (∏ p ∈ P.filter (fun p : ℕ => p < 13), term p (1/30)) = 55440 := by
    have hset : P.filter (fun p : ℕ => p < 13) = ({2, 3, 5, 7, 11} : Finset ℕ) := by
      simpa [P] using (small_filter_eq B hB)
    rw [hset]
    rw [show (Finset.prod ({2, 3, 5, 7, 11} : Finset ℕ) (fun p => term p (1/30))) =
        term 2 (1/30) * term 3 (1/30) * term 5 (1/30) * term 7 (1/30) * term 11 (1/30) by
      simp [Finset.prod_insert, Finset.prod_singleton]
      ac_rfl]
    simp only [term]
    rw [expo2, expo3, expo5, expo7, expo11]
    norm_num
  rw [hbig, hsmall]
  norm_num

/-- `55440` lies in the CA family: ε = 1/30 makes the product over primes
`p < e^{60} + 2` of `p^{⌊μ(p,ε)⌋}` equal `2^4·3^2·5·7·11 = 55440`. -/
theorem ca_55440_in_family :
    ∃ ε : ℝ, 0 < ε ∧
      Finset.prod ((Finset.range (if 0 < ε then Nat.ceil (Real.exp (2 / ε)) + 2 else 3)).filter Nat.Prime)
        (fun p : ℕ => p ^ Nat.floor
          (Real.log (((p : ℝ) ^ (1 + ε) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ))) = 55440 := by
  refine ⟨(1 / 30 : ℝ), by norm_num, ?_⟩
  rw [if_pos (by norm_num : (0 : ℝ) < 1 / 30)]
  have h60 : (2 / (1 / 30 : ℝ)) = 60 := by norm_num
  rw [h60]
  change (Finset.prod ((Finset.range (Nat.ceil (Real.exp 60) + 2)).filter Nat.Prime)
      (fun p : ℕ => term p (1 / 30))) = 55440
  exact prod_eq_55440 (Nat.ceil (Real.exp 60) + 2) bound_13

end
end Commons.NumberTheory.Robin
