import Mathlib
import Submission.Work.BW.DefsMult

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Auxiliary facts for `Work.BW.split_conditions`. -/

namespace Work.BW

open Finset

/-! ## Part 1: `halfSplit` arithmetic -/

theorem halfSplit_zero (r : ℕ) (x : ℝ) : halfSplit r x 0 = ⌊x / 2⌋₊ := by
  simp [halfSplit]

theorem halfSplit_ne_zero {r m : ℕ} (hm : m ≠ 0) (x : ℝ) :
    halfSplit r x m = ⌊x / (2 * r)⌋₊ := by
  simp [halfSplit, hm]

theorem halfSplit_eq_succ (r m : ℕ) (x : ℝ) :
    halfSplit r x (m + 1) = ⌊x / (2 * r)⌋₊ := halfSplit_ne_zero (Nat.succ_ne_zero m) x

theorem halfSplit_anti {r : ℕ} {x : ℝ} (hx : 0 ≤ x) (m : ℕ) :
    halfSplit r x (m + 1) ≤ halfSplit r x m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    rw [halfSplit_zero, halfSplit_eq_succ]
    refine Nat.floor_le_floor ?_
    rcases Nat.eq_zero_or_pos r with hr | hr
    · simp only [hr, Nat.cast_zero, mul_zero, div_zero]
      exact div_nonneg hx (by norm_num)
    · have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      refine div_le_div_of_nonneg_left hx (by norm_num) ?_
      linarith
  · rw [halfSplit_eq_succ, halfSplit_ne_zero (Nat.pos_iff_ne_zero.mp h) x]

theorem halfSplit_sum_le {r : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    ((∑ m ∈ Finset.range (r + 1), halfSplit r x m : ℕ) : ℝ) ≤ x := by
  rw [Finset.sum_range_succ']
  rw [Nat.cast_add]
  have h0 : ((halfSplit r x 0 : ℕ) : ℝ) ≤ x / 2 := by
    rw [halfSplit_zero]; exact Nat.floor_le (by linarith)
  have hrest : ((∑ k ∈ Finset.range r, halfSplit r x (k + 1) : ℕ) : ℝ) ≤ x / 2 := by
    rw [Nat.cast_sum]
    have hc : ∀ k ∈ Finset.range r,
        ((halfSplit r x (k + 1) : ℕ) : ℝ) ≤ x / (2 * r) := by
      intro k _
      rw [halfSplit_eq_succ]
      exact Nat.floor_le (by positivity)
    calc (∑ k ∈ Finset.range r, ((halfSplit r x (k + 1) : ℕ) : ℝ))
        ≤ ∑ _k ∈ Finset.range r, x / (2 * r) := Finset.sum_le_sum hc
      _ = (r : ℝ) * (x / (2 * r)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ x / 2 := by
            rcases Nat.eq_zero_or_pos r with hrr | hrr
            · rw [hrr]; simp only [Nat.cast_zero, mul_zero, div_zero]
              exact div_nonneg hx (by norm_num)
            · have hrne : (r:ℝ) ≠ 0 := by
                have : (0:ℝ) < r := by exact_mod_cast hrr
                positivity
              have heq : (r:ℝ) * (x / (2*r)) = x/2 := by field_simp
              exact le_of_eq heq
  linarith

/-! ## Part 2: basics on `pxi`, `pI`, logs -/

theorem two_rd_ge_four {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) : (4 : ℝ) ≤ 2 * r * d := by
  have h1 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have h2 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  nlinarith

theorem two_rd_pos {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) : (0 : ℝ) < 2 * r * d := by
  linarith [two_rd_ge_four hr hd]

theorem log_2rd_ge {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) :
    4 / 3 ≤ Real.log (2 * r * d) := by
  have h4 : (0 : ℝ) < 4 := by norm_num
  have h1 : Real.log 4 ≤ Real.log (2 * r * d) := by
    apply Real.log_le_log h4 (two_rd_ge_four hr hd)
  have h2 : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
  have h3 : Real.log 4 = 2 * Real.log 2 := by
    rw [h2, Real.log_pow]; norm_num
  have h5 : (4 : ℝ) / 3 ≤ 2 * Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  linarith

theorem log_2rd_pos {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) :
    0 < Real.log (2 * r * d) := by
  linarith [log_2rd_ge hr hd]

theorem pxi_pos {r : ℕ} (hr : 2 ≤ r) : 0 < pxi r := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hr)
  have h2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have : (0.536 : ℝ) / r < 1 := by
    rw [div_lt_one hr']; linarith
  simp only [pxi]
  linarith

theorem pxi_le_one (r : ℕ) : pxi r ≤ 1 := by
  rcases Nat.eq_zero_or_pos r with h | h
  · simp [pxi, h]
  · have hr' : (0 : ℝ) < r := by exact_mod_cast h
    have : 0 ≤ (0.536 : ℝ) / r := by positivity
    simp only [pxi]; linarith

theorem pxi_ge {r : ℕ} (hr : 2 ≤ r) : (0.7 : ℝ) ≤ pxi r := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hr)
  have h2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hle : (0.536 : ℝ) / r ≤ 0.268 := by
    rw [div_le_iff₀ hr']
    linarith
  simp only [pxi]
  linarith

theorem pI_low {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) :
    50 * Real.log (2 * r * d) - 1 ≤ (pI r d : ℝ) := by
  have h := Nat.lt_floor_add_one (50 * Real.log (2 * r * d))
  simp only [pI]
  linarith

/-! ## Part 3: `2 ^ pI` and `Theta` lower bounds -/

theorem one05_pow50_ge_e2 : Real.exp 2 ≤ (1.05 : ℝ) ^ (50:ℕ) := by
  have hnat : (11 : ℝ) ≤ (1.05 : ℝ) ^ (50:ℕ) := by
    have hb : (1.05 : ℝ) = (105:ℝ)/100 := by norm_num
    rw [hb]; norm_num
  have he2 : Real.exp 2 < 11 := by
    have h1 : Real.exp 1 < 3 := Real.exp_one_lt_three
    have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
      rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]; ring
    rw [h2]; nlinarith [Real.exp_pos 1]
  linarith

theorem pow_two_pI_ge {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) :
    (2 * r * d) ^ (34 : ℕ) / 2 ≤ (2 : ℝ) ^ pI r d := by
  have hpos := two_rd_pos hr hd
  have hLpos : 0 < Real.log (2 * r * d) := log_2rd_pos hr hd
  have hL : (0:ℝ) ≤ Real.log (2 * r * d) := le_of_lt hLpos
  -- (2rd)^34 = exp(34 * L)
  have e1 : (2 * r * d) ^ (34 : ℕ) = Real.exp (34 * Real.log (2 * r * d)) := by
    rw [show (34:ℝ) * Real.log (2 * r * d)
          = ((34:ℕ):ℝ) * Real.log (2 * r * d) by norm_num]
    rw [Real.exp_nat_mul, Real.exp_log hpos]
  -- 2^(50L) = exp(50 L log 2)
  have e2 : (2:ℝ) ^ (50 * Real.log (2 * r * d))
      = Real.exp (50 * Real.log (2 * r * d) * Real.log 2) := by
    rw [Real.rpow_def_of_pos (show (0:ℝ) < 2 by norm_num)]
    ring_nf
  have h34 : (34:ℝ) ≤ 50 * Real.log 2 := by
    have := Real.log_two_gt_d9; nlinarith
  have hle1 : (2 * r * d) ^ (34 : ℕ) ≤ (2:ℝ) ^ (50 * Real.log (2 * r * d)) := by
    rw [e1, e2]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hL (by linarith : (0:ℝ) ≤ (50:ℝ) * Real.log 2 - 34)]
  -- hsplit
  have hsplit : (2:ℝ) ^ (50 * Real.log (2 * r * d))
      = (2:ℝ) ^ (50 * Real.log (2 * r * d) - 1) * 2 := by
    have h := Real.rpow_add (show (0:ℝ) < 2 by norm_num)
      (50 * Real.log (2 * r * d) - 1) 1
    rw [show 50 * Real.log (2 * r * d) - 1 + 1 = 50 * Real.log (2 * r * d) by ring] at h
    rw [h]; norm_num
  have hmono : (2:ℝ) ^ (50 * Real.log (2 * r * d) - 1) ≤ (2:ℝ) ^ pI r d := by
    have hlow := pI_low hr hd
    have h := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 2 by norm_num) hlow
    rwa [Real.rpow_natCast] at h
  calc (2 * r * d) ^ (34 : ℕ) / 2
      ≤ (2:ℝ) ^ (50 * Real.log (2 * r * d)) / 2 :=
        div_le_div_of_nonneg_right hle1 (by norm_num)
    _ = (2:ℝ) ^ (50 * Real.log (2 * r * d) - 1) := by rw [hsplit]; ring
    _ ≤ (2:ℝ) ^ pI r d := hmono

theorem inv_one_sub_sub_one {a : ℝ} (ha : a ≠ 1) : (1-a)⁻¹ - 1 = a * (1-a)⁻¹ := by
  field_simp; ring

theorem theta_ge {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) :
    (2 * r * d) ^ (2 : ℕ) / 2 ≤ (2 : ℝ) ^ pI r d * (pxi r) ^ (r * pI r d) := by
  have hpos := two_rd_pos hr hd
  have hxi := pxi_pos hr
  have hrw : (2 : ℝ) ^ pI r d * (pxi r) ^ (r * pI r d)
      = (2 * (pxi r) ^ r) ^ pI r d := by
    rw [mul_pow, ← pow_mul]
  rw [hrw]
  -- 2 * xi^r >= 1.05
  have h105 : (1.05 : ℝ) ≤ 2 * (pxi r) ^ r := by
    rcases lt_or_ge r 21 with h | h
    · interval_cases r <;> norm_num [pxi]
    · have h21 : (21 : ℝ) ≤ r := by exact_mod_cast h
      have hr' : (0 : ℝ) < r := by linarith
      have hy : (0.536 : ℝ) / r < 1 := by rw [div_lt_one hr']; linarith
      have hpos1 : (0:ℝ) < 1 - 0.536 / r := by linarith
      have ha : (0.536:ℝ)/r ≤ 0.536/21 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) h21
      have ha1 : ((0.536:ℝ)/r) ≠ 1 := ne_of_lt hy
      have hA : -Real.log (1 - (0.536:ℝ)/r) ≤ (0.536:ℝ)/r * (1-(0.536:ℝ)/r)⁻¹ := by
        have h1 : -Real.log (1 - (0.536:ℝ)/r) = Real.log ((1 - (0.536:ℝ)/r)⁻¹) := by
          rw [Real.log_inv]
        rw [h1]
        have h2 : Real.log ((1 - (0.536:ℝ)/r)⁻¹) ≤ (1 - (0.536:ℝ)/r)⁻¹ - 1 :=
          Real.log_le_sub_one_of_pos (inv_pos.mpr hpos1)
        have h3 := inv_one_sub_sub_one ha1
        linarith
      have hkey : (r:ℝ) * (-Real.log (pxi r)) ≤ 0.64 := by
        have hxir : pxi r = 1 - 0.536 / r := rfl
        rw [hxir]
        have hmul : (r:ℝ) * (-Real.log (1 - (0.536:ℝ)/r))
            ≤ (r:ℝ) * ((0.536:ℝ)/r * (1-(0.536:ℝ)/r)⁻¹) :=
          mul_le_mul_of_nonneg_left hA (le_of_lt hr')
        have hsimp : (r:ℝ) * ((0.536:ℝ)/r * (1-(0.536:ℝ)/r)⁻¹)
            = 0.536 * (1-(0.536:ℝ)/r)⁻¹ := by
          field_simp
        have hlast : 0.536 * (1-(0.536:ℝ)/r)⁻¹ ≤ 0.64 := by
          rw [inv_eq_one_div, ← div_eq_mul_one_div]
          rw [div_le_iff₀ hpos1]
          nlinarith [ha]
        linarith
      have hlog2 : (0.69 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      have hlog105 : Real.log (1.05:ℝ) ≤ 0.05 := by
        have h1 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1.05 by norm_num)
        linarith
      have hlt : (0:ℝ) < 2 * (pxi r)^r := by
        have := pxi_pos hr
        positivity
      have hpos105 : (0:ℝ) < 1.05 := by norm_num
      have hloggoalle : Real.log (1.05:ℝ) ≤ Real.log (2 * (pxi r)^r) := by
        rw [Real.log_mul (by norm_num) (ne_of_gt (pow_pos (pxi_pos hr) r)), Real.log_pow]
        nlinarith
      exact (Real.log_le_log_iff hpos105 hlt).mp hloggoalle
  have h105I : (1.05 : ℝ) ^ (pI r d) ≤ (2 * (pxi r) ^ r) ^ (pI r d) :=
    pow_le_pow_left₀ (by norm_num) h105 _
  have hLpos : 0 < Real.log (2 * r * d) := log_2rd_pos hr hd
  have hL : (0:ℝ) ≤ Real.log (2 * r * d) := le_of_lt hLpos
  -- 1.05^I ≥ (2rd)^2/2
  have hmono : (1.05 : ℝ) ^ (50 * Real.log (2 * r * d) - 1) ≤ (1.05 : ℝ) ^ pI r d := by
    have hlow := pI_low hr hd
    have h := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 1.05 by norm_num) hlow
    rwa [Real.rpow_natCast] at h
  have hb : Real.exp 2 ≤ (1.05:ℝ)^(50:ℕ) := one05_pow50_ge_e2
  have hb' : Real.exp 2 ≤ (1.05:ℝ)^(((50:ℕ)):ℝ) := by
    rw [Real.rpow_natCast]; exact hb
  have hmono2 : (Real.exp 2) ^ Real.log (2 * r * d)
      ≤ ((1.05:ℝ)^(((50:ℕ)):ℝ)) ^ Real.log (2 * r * d) :=
    Real.rpow_le_rpow (le_of_lt (Real.exp_pos 2)) hb' hL
  have hmul : ((1.05:ℝ)^(((50:ℕ)):ℝ)) ^ Real.log (2 * r * d)
      = (1.05:ℝ) ^ ((((50:ℕ)):ℝ) * Real.log (2 * r * d)) :=
    (Real.rpow_mul (show (0:ℝ) ≤ 1.05 by norm_num) (((50:ℕ)):ℝ)
      (Real.log (2 * r * d))).symm
  have hcast : (((50:ℕ)):ℝ) = (50:ℝ) := by norm_num
  have hexp2 : (Real.exp 2) ^ Real.log (2 * r * d) = (2 * r * d) ^ (2 : ℕ) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos 2), Real.log_exp]
    rw [show (2:ℝ) * Real.log (2 * r * d)
          = Real.log (2 * r * d) + Real.log (2 * r * d) by ring]
    rw [Real.exp_add, Real.exp_log hpos]
    ring
  have hsplit : (1.05:ℝ) ^ (50 * Real.log (2 * r * d))
      = (1.05:ℝ) ^ (50 * Real.log (2 * r * d) - 1) * 1.05 := by
    have h := Real.rpow_add (show (0:ℝ) < 1.05 by norm_num)
      (50 * Real.log (2 * r * d) - 1) 1
    rw [show 50 * Real.log (2 * r * d) - 1 + 1 = 50 * Real.log (2 * r * d) by ring] at h
    rw [h]; norm_num
  have hstep : (2 * r * d) ^ (2:ℕ) ≤ (1.05:ℝ) ^ pI r d * 1.05 := by
    calc (2 * r * d) ^ (2:ℕ) = (Real.exp 2) ^ Real.log (2 * r * d) := hexp2.symm
      _ ≤ ((1.05:ℝ)^(((50:ℕ)):ℝ)) ^ Real.log (2 * r * d) := hmono2
      _ = (1.05:ℝ) ^ ((((50:ℕ)):ℝ) * Real.log (2 * r * d)) := hmul
      _ = (1.05:ℝ) ^ (50 * Real.log (2 * r * d)) := by rw [hcast]
      _ = (1.05:ℝ) ^ (50 * Real.log (2 * r * d) - 1) * 1.05 := hsplit
      _ ≤ (1.05:ℝ) ^ pI r d * 1.05 :=
            mul_le_mul_of_nonneg_right hmono (by norm_num)
  have hpos105 : (0:ℝ) < (1.05:ℝ) ^ pI r d := by positivity
  calc (2 * r * d) ^ (2 : ℕ) / 2
      ≤ (1.05:ℝ) ^ pI r d := by nlinarith
    _ ≤ (2 * (pxi r) ^ r) ^ pI r d := h105I

/-! ## Part 4: `pD`, `pD0`, `pDj`, `pT`, `calS`, `calT`, `calD` facts -/

theorem prod_le_prod_of_nonneg {ι : Type*} [DecidableEq ι] {s : Finset ι} {f g : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have h1 : f a ≤ g a := h a (Finset.mem_insert_self a s)
      have h2 : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i :=
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
           (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have h3 : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
      have h4 : 0 ≤ ∏ i ∈ s, f i :=
        Finset.prod_nonneg (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      exact mul_le_mul h1 h2 h4 (le_trans h3 h1)

theorem prod_sigma_ge {r d : ℕ} (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1/(d:ℝ) ≤ σ j) : ((d:ℝ)^r)⁻¹ ≤ ∏ j, σ j := by
  have h1 : ∏ _j : Fin r, ((1:ℝ)/(d:ℝ)) ≤ ∏ j : Fin r, σ j :=
    prod_le_prod_of_nonneg (fun j _ => by positivity) (fun j _ => hσ j)
  have h2 : (∏ _j : Fin r, ((1:ℝ)/(d:ℝ))) = ((d:ℝ)^r)⁻¹ := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [one_div, inv_pow]
  rwa [h2] at h1

theorem pD_pos {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1/(d:ℝ) ≤ σ j) : 0 < pD r d σ := by
  have hL := log_2rd_pos hr hd
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hσpos : ∀ j, 0 < σ j := by
    intro j
    have h1 : (0:ℝ) < 1/(d:ℝ) := by positivity
    linarith [hσ j]
  have hr0 : (0:ℝ) < r := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0<2) hr)
  have hprod : 0 < ∏ j, σ j := Finset.prod_pos (fun j _ => hσpos j)
  rw [pD]
  positivity

theorem pD_low {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1/(d:ℝ) ≤ σ j) :
    2 * (r:ℝ)^r * (32:ℝ)^(r+1) * (d:ℝ) * Real.log (2*r*d) ≤ pD r d σ := by
  have hL := log_2rd_pos hr hd
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hr0 : (0:ℝ) < r := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0<2) hr)
  have hprod := prod_sigma_ge hd σ hσ
  have hDmin : 2 * (r:ℝ)^r * (32:ℝ)^(r+1) * (d:ℝ) * Real.log (2*r*d)
      = 2 * (r:ℝ)^r * (32*(d:ℝ))^(r+1) * Real.log (2*r*d) * ((d:ℝ)^r)⁻¹ := by
    rw [mul_pow, pow_succ]
    field_simp
    ring
  rw [pD, hDmin]
  have h2 : 0 ≤ 2 * (r:ℝ)^r * (32*(d:ℝ))^(r+1) * Real.log (2*r*d) := by positivity
  exact mul_le_mul_of_nonneg_left hprod h2

theorem pD_ge_one {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1/(d:ℝ) ≤ σ j) : 1 ≤ pD r d σ := by
  have h := pD_low hr hd σ hσ
  have hr1 : (2:ℝ) ≤ r := by exact_mod_cast hr
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hr0 : (0:ℝ) < r := by linarith
  have hL : (4:ℝ)/3 ≤ Real.log (2*r*d) := log_2rd_ge hr hd
  have h32 : (1:ℝ) ≤ (32:ℝ)^(r+1) := one_le_pow₀ (by norm_num)
  have hrr : (4:ℝ) ≤ (r:ℝ)^r := by
    have h1 : (2:ℝ)^(2:ℕ) ≤ (r:ℝ)^(2:ℕ) := pow_le_pow_left₀ (by norm_num) hr1 2
    have h2 : (r:ℝ)^(2:ℕ) ≤ (r:ℝ)^r := pow_le_pow_right₀ (by linarith) hr
    calc (4:ℝ) = (2:ℝ)^(2:ℕ) := by norm_num
      _ ≤ (r:ℝ)^(2:ℕ) := h1
      _ ≤ (r:ℝ)^r := h2
  have hprod : (1:ℝ) ≤ 2 * (r:ℝ)^r * (32:ℝ)^(r+1) * (d:ℝ) * Real.log (2*r*d) := by
    have h1 : (1:ℝ) ≤ (r:ℝ)^r := by linarith [hrr]
    have h2 : (1:ℝ) ≤ (32:ℝ)^(r+1) := h32
    have h3 : (1:ℝ) ≤ (d:ℝ) := hd1
    have h4 : (1:ℝ) ≤ Real.log (2*r*d) := by linarith [hL]
    have h5 : (1:ℝ) ≤ 2 := by norm_num
    have hA : (1:ℝ) ≤ 2 * (r:ℝ)^r := by
      have := mul_le_mul h5 h1 (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ 2)
      simpa using this
    have hB : (1:ℝ) ≤ 2 * (r:ℝ)^r * (32:ℝ)^(r+1) := by
      have hnn : (0:ℝ) ≤ 2 * (r:ℝ)^r := by linarith [hA]
      have := mul_le_mul hA h2 (by norm_num : (0:ℝ) ≤ 1) hnn
      simpa using this
    have hC : (1:ℝ) ≤ 2 * (r:ℝ)^r * (32:ℝ)^(r+1) * (d:ℝ) := by
      have hnn : (0:ℝ) ≤ 2 * (r:ℝ)^r * (32:ℝ)^(r+1) := by linarith [hB]
      have := mul_le_mul hB h3 (by norm_num : (0:ℝ) ≤ 1) hnn
      simpa using this
    have hnn : (0:ℝ) ≤ 2 * (r:ℝ)^r * (32:ℝ)^(r+1) * (d:ℝ) := by linarith [hC]
    have := mul_le_mul hC h4 (by norm_num : (0:ℝ) ≤ 1) hnn
    simpa using this
  linarith [h, hprod]

theorem pD0_le {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1/(d:ℝ) ≤ σ j) :
    (pD0 r d σ : ℝ) ≤ (r:ℝ) * pD r d σ / (2 * Real.log (2*r*d)) := by
  apply Nat.floor_le
  have hL := log_2rd_pos hr hd
  have hD := pD_pos hr hd σ hσ
  positivity

theorem pD0_ge (r d : ℕ) (σ : Fin r → ℝ) :
    (r:ℝ) * pD r d σ / (2 * Real.log (2*r*d)) ≤ (pD0 r d σ : ℝ) + 1 := by
  have h := Nat.lt_floor_add_one ((r:ℝ) * pD r d σ / (2 * Real.log (2*r*d)))
  simp only [pD0]
  linarith

theorem pDj_le {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1/(d:ℝ) ≤ σ j) (j : Fin r) :
    (pDj r d σ j : ℝ) ≤ pD r d σ / ((r:ℝ) * (d:ℝ) * σ j) := by
  apply Nat.floor_le
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hσj : 0 < σ j := by
    have h1 : (0:ℝ) < 1/(d:ℝ) := by positivity
    linarith [hσ j]
  have hr0 : (0:ℝ) < r := by
    have : (0:ℝ) < r := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0<2) hr)
    exact this
  have hD : 0 ≤ pD r d σ := le_of_lt (pD_pos hr hd σ hσ)
  have hrd : 0 < (r:ℝ) * (d:ℝ) := mul_pos hr0 hd0
  exact div_nonneg hD (le_of_lt (mul_pos hrd hσj))

theorem pDj_le_r {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1/(d:ℝ) ≤ σ j) (j : Fin r) :
    (pDj r d σ j : ℝ) ≤ pD r d σ / (r:ℝ) := by
  have hD := pD_pos hr hd σ hσ
  have h1 := pDj_le hr hd σ hσ j
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hσj : 1 ≤ (d:ℝ) * σ j := by
    have h2 := hσ j
    rw [div_le_iff₀ hd0] at h2
    linarith
  have hrpos : 0 < (r:ℝ) := by
    have : (0:ℝ) < r := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0<2) hr)
    exact this
  have hden : (r:ℝ) ≤ (r:ℝ) * (d:ℝ) * σ j := by nlinarith
  calc (pDj r d σ j : ℝ) ≤ pD r d σ / ((r:ℝ) * (d:ℝ) * σ j) := h1
    _ ≤ pD r d σ / (r:ℝ) :=
        div_le_div_of_nonneg_left (le_of_lt hD) hrpos hden

theorem pT_ge {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1/(d:ℝ) ≤ σ j) : 11 * (r:ℝ) * pD r d σ ≤ (pT r d σ : ℝ) := by
  have hD1 := pD_ge_one hr hd σ hσ
  have hr2 : (2:ℝ) ≤ r := by exact_mod_cast hr
  have h := Nat.lt_floor_add_one ((11.75:ℝ) * r * pD r d σ)
  have h2 : (11:ℝ) * r * pD r d σ ≤ (11.75:ℝ) * r * pD r d σ - 1 := by nlinarith
  simp only [pT]
  linarith [h]

theorem calS_eq (r d h : ℕ) :
    calS r d h = 2 * (pxi r) ^ (-((r * pI r d : ℕ) : ℤ)) * (pS r d h : ℝ) := rfl

theorem calS_div_two (r d h : ℕ) :
    calS r d h / 2 = (pxi r) ^ (-((r * pI r d : ℕ) : ℤ)) * (pS r d h : ℝ) := by
  rw [calS_eq]; ring

theorem calS_div_two_r {r d h : ℕ} (hr : r ≠ 0) :
    calS r d h / (2*(r:ℝ)) = (pxi r) ^ (-((r * pI r d : ℕ) : ℤ)) * (16*(d:ℝ)*(h:ℝ)) := by
  have hr0 : (0:ℝ) < r := by
    have : (0:ℕ) < r := Nat.pos_of_ne_zero hr
    exact_mod_cast this
  have hS : (pS r d h : ℝ) = 16 * (r:ℝ) * (d:ℝ) * (h:ℝ) := by
    simp only [pS]; push_cast; ring
  rw [calS_eq, hS]
  field_simp

theorem calT_eq (r d : ℕ) (σ : Fin r → ℝ) :
    calT r d σ = pxi r * (pxi r) ^ (r * pI r d) * (pT r d σ : ℝ) := rfl

theorem calT_div_two (r d : ℕ) (σ : Fin r → ℝ) :
    calT r d σ / 2 = pxi r * (pxi r) ^ (r * pI r d) * (pT r d σ : ℝ) / 2 := by
  rw [calT_eq]

theorem calT_div_two_r (r d : ℕ) (σ : Fin r → ℝ) :
    calT r d σ / (2*(r:ℝ)) = pxi r * (pxi r) ^ (r * pI r d) * (pT r d σ : ℝ) / (2*(r:ℝ)) := by
  rw [calT_eq]

theorem calD_zero (r d h : ℕ) (σ : Fin r → ℝ) :
    calD r d h σ 0 = (h:ℝ) * ((pD0 r d σ : ℝ) + 1) := by
  simp [calD]

theorem calD_succ (r d h : ℕ) (σ : Fin r → ℝ) (j : Fin r) :
    calD r d h σ j.succ = (pDj r d σ j : ℝ) / (2:ℝ)^(pI r d) := by
  simp [calD]

theorem calD_nonneg (r d h : ℕ) (σ : Fin r → ℝ) (i : Fin (r+1)) :
    0 ≤ calD r d h σ i := by
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, rfl⟩
  · rw [h, calD_zero]; positivity
  · rw [calD_succ]; positivity

theorem calD_succ_le_M {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (h : ℕ) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1/(d:ℝ) ≤ σ j) (j : Fin r) :
    calD r d h σ j.succ ≤ pD r d σ / ((r:ℝ) * (2:ℝ)^(pI r d)) := by
  rw [calD_succ]
  have h1 := pDj_le_r hr hd σ hσ j
  have h2 : (0:ℝ) < (2:ℝ)^(pI r d) := by positivity
  have hr0 : (0:ℝ) < r := by
    have : (0:ℝ) < r := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0<2) hr)
    exact this
  rw [div_le_iff₀ h2]
  have heq : pD r d σ / ((r:ℝ) * (2:ℝ)^(pI r d)) * (2:ℝ)^(pI r d) = pD r d σ / (r:ℝ) := by
    field_simp
  rw [heq]
  exact h1

theorem two_log_le_sq_mul_pow {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) :
    2 * Real.log (2*r*d) ≤ (r:ℝ)^2 * (2:ℝ)^(pI r d) := by
  have hpos := two_rd_pos hr hd
  have hLpos := log_2rd_pos hr hd
  have hr2 : (2:ℝ) ≤ r := by exact_mod_cast hr
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hrnn : (0:ℝ) ≤ r := by linarith
  have hI := pow_two_pI_ge hr hd
  have hLle : Real.log (2*r*d) ≤ 2*r*d := by
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  have h8 : 8*(d:ℝ) ≤ (r:ℝ) * (2*r*d)^34 := by
    rw [mul_pow]
    have h32 : (2:ℝ)^34 ≤ (2*r)^34 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 34
    have hd34 : (d:ℝ) ≤ d^34 := by
      calc (d:ℝ) = d^1 := by ring
        _ ≤ d^34 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h1 : (8:ℝ) ≤ (r:ℝ) * (2:ℝ)^34 := by
      have h2 : (1:ℝ) ≤ (2:ℝ)^34 := one_le_pow₀ (by norm_num)
      nlinarith [hr2, h2]
    have s1 : 8*(d:ℝ) ≤ ((r:ℝ) * (2:ℝ)^34) * (d:ℝ)^34 :=
      mul_le_mul h1 hd34 (by linarith) (by positivity)
    have s2 : ((r:ℝ) * (2:ℝ)^34) * (d:ℝ)^34 ≤ ((r:ℝ) * (2*r)^34) * (d:ℝ)^34 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h32 hrnn) (by positivity)
    calc 8*(d:ℝ) ≤ ((r:ℝ) * (2:ℝ)^34) * (d:ℝ)^34 := s1
      _ ≤ ((r:ℝ) * (2*r)^34) * (d:ℝ)^34 := s2
      _ = (r:ℝ) * ((2*r)^34 * (d:ℝ)^34) := by ring
  have h4 : 4*(r:ℝ)*(d:ℝ) ≤ (r:ℝ)^2 * (2*r*d)^34 / 2 := by
    have hmul : (r:ℝ) * (8*(d:ℝ)) ≤ (r:ℝ) * ((r:ℝ) * (2*r*d)^34) :=
      mul_le_mul_of_nonneg_left h8 hrnn
    linarith [hmul]
  have h2 : 2 * Real.log (2*r*d) ≤ 4*(r:ℝ)*(d:ℝ) := by linarith
  have h5 : (r:ℝ)^2 * (2*r*d)^34 / 2 ≤ (r:ℝ)^2 * (2:ℝ)^(pI r d) := by
    have h6 : (2*r*d)^34/2 ≤ (2:ℝ)^(pI r d) := hI
    calc (r:ℝ)^2 * (2*r*d)^34 / 2 = (r:ℝ)^2 * ((2*r*d)^34/2) := by ring
      _ ≤ (r:ℝ)^2 * (2:ℝ)^(pI r d) := mul_le_mul_of_nonneg_left h6 (sq_nonneg _)
  linarith

theorem M_le_calD_zero {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (h : ℕ) (hh : 1 ≤ h)
    (σ : Fin r → ℝ) (hσ : ∀ j, 1/(d:ℝ) ≤ σ j) :
    pD r d σ / ((r:ℝ) * (2:ℝ)^(pI r d)) ≤ calD r d h σ 0 := by
  rw [calD_zero]
  have hD0 := pD0_ge r d σ
  have hkey := two_log_le_sq_mul_pow hr hd
  have hr2 : (2:ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0:ℝ) < r := by linarith
  have hLpos : 0 < Real.log (2*r*d) := log_2rd_pos hr hd
  have hDnn : 0 ≤ pD r d σ := le_of_lt (pD_pos hr hd σ hσ)
  have h2I : (0:ℝ) < (2:ℝ)^(pI r d) := by positivity
  have hcomp : pD r d σ / ((r:ℝ) * (2:ℝ)^(pI r d))
      ≤ (r:ℝ) * pD r d σ / (2 * Real.log (2*r*d)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h2 := mul_le_mul_of_nonneg_left hkey hDnn
    have heq : pD r d σ * ((r:ℝ)^2 * (2:ℝ)^(pI r d))
        = ((r:ℝ) * pD r d σ) * ((r:ℝ) * (2:ℝ)^(pI r d)) := by ring
    rwa [heq] at h2
  have h1 : (1:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have h3 : (0:ℝ) ≤ (pD0 r d σ : ℝ) := Nat.cast_nonneg _
  nlinarith [hcomp, hD0, h1, h3]

theorem choose_lower (Tq k : ℕ) :
    (((Tq + 1 : ℕ) : ℝ)) ^ k / ((k.factorial : ℕ) : ℝ) ≤ ((Tq + k).choose k : ℝ) := by
  have h := Nat.pow_sub_le_descFactorial (Tq + k) k
  have hsimp : Tq + k + 1 - k = Tq + 1 := by omega
  rw [hsimp, Nat.descFactorial_eq_factorial_mul_choose] at h
  have hR : ((Tq : ℝ) + 1)^k ≤ ((k.factorial : ℕ) : ℝ) * ((Tq + k).choose k : ℝ) := by
    exact_mod_cast h
  have hk : (0:ℝ) < ((k.factorial : ℕ) : ℝ) := by exact_mod_cast k.factorial_pos
  rw [Nat.cast_add, Nat.cast_one, div_le_iff₀ hk]
  calc ((Tq : ℝ) + 1)^k ≤ ((k.factorial : ℕ) : ℝ) * ((Tq + k).choose k : ℝ) := hR
    _ = ((Tq + k).choose k : ℝ) * ((k.factorial : ℕ) : ℝ) := by ring

theorem prod_pow_one_le {r : ℕ} {f : Fin (r+1) → ℝ} {e : Fin (r+1) → ℕ} {M : ℝ} {m : ℕ}
    (he : ∀ i, e i ≤ 1) (hsum : ∑ i, e i = m + 1)
    (hM : 0 ≤ M) (hf0 : M ≤ f 0) (hfn : 0 ≤ f 0)
    (hfj0 : ∀ j : Fin r, 0 ≤ f j.succ) (hfj : ∀ j : Fin r, f j.succ ≤ M) :
    ∏ i, f i ^ e i ≤ f 0 * M ^ m := by
  have h1 : ∏ j : Fin r, f j.succ ^ e j.succ ≤ ∏ j : Fin r, M ^ e j.succ := by
    apply prod_le_prod_of_nonneg
    · intro j _
      exact pow_nonneg (hfj0 j) _
    · intro j _
      exact pow_le_pow_left₀ (hfj0 j) (hfj j) _
  have h2 : (∏ j : Fin r, M ^ e j.succ) = M ^ (∑ j : Fin r, e j.succ) :=
    Finset.prod_pow_eq_pow_sum _ _ _
  have h3 : ∑ j : Fin r, e j.succ = m + 1 - e 0 := by
    have hh := Fin.sum_univ_succ e
    omega
  have he0 : e 0 ≤ 1 := he 0
  have hstep : f 0 ^ e 0 * M ^ (m + 1 - e 0) ≤ f 0 * M ^ m := by
    rcases (show e 0 = 0 ∨ e 0 = 1 by omega) with h0 | h0
    · rw [h0, Nat.sub_zero, pow_zero, one_mul, pow_succ]
      calc M ^ m * M = M * M ^ m := by ring
        _ ≤ f 0 * M ^ m := mul_le_mul_of_nonneg_right hf0 (pow_nonneg hM m)
    · rw [h0, Nat.add_sub_cancel, pow_one]
  rw [Fin.prod_univ_succ]
  calc f 0 ^ e 0 * ∏ j : Fin r, f j.succ ^ e j.succ
      ≤ f 0 ^ e 0 * ∏ j : Fin r, M ^ e j.succ :=
        mul_le_mul_of_nonneg_left h1 (pow_nonneg hfn _)
    _ = f 0 ^ e 0 * M ^ (∑ j : Fin r, e j.succ) := by rw [h2]
    _ = f 0 ^ e 0 * M ^ (m + 1 - e 0) := by rw [h3]
    _ ≤ f 0 * M ^ m := hstep

theorem pxi_pos' (r : ℕ) : 0 < pxi r := by
  rcases Nat.eq_zero_or_pos r with h | h
  · simp [pxi, h]
  · have hr1 : (1:ℝ) ≤ r := by exact_mod_cast h
    have h1 : (0.536 : ℝ) / r ≤ 0.536 :=
      div_le_self (by norm_num) hr1
    simp only [pxi]; linarith

theorem calS_nonneg (r d h : ℕ) : 0 ≤ calS r d h := by
  have hx := pxi_pos' r
  rw [calS_eq]
  have h1 : 0 < (pxi r) ^ (-((r * pI r d : ℕ) : ℤ)) := zpow_pos hx _
  have h2 : (0:ℝ) ≤ (pS r d h : ℝ) := Nat.cast_nonneg _
  positivity

theorem calT_nonneg (r d : ℕ) (σ : Fin r → ℝ) : 0 ≤ calT r d σ := by
  have hx := pxi_pos' r
  rw [calT_eq]
  positivity

theorem log_le_two_rd {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) :
    Real.log (2*r*d) ≤ 2*r*d := by
  have := Real.log_le_sub_one_of_pos (two_rd_pos hr hd)
  linarith

/-- `2 r² d L ≤ pD`. -/
theorem pD_low2 {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1/(d:ℝ) ≤ σ j) : 2 * (r:ℝ)^2 * (d:ℝ) * Real.log (2*r*d) ≤ pD r d σ := by
  have h := pD_low hr hd σ hσ
  have hr2 : (2:ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0:ℝ) ≤ r := by linarith
  have hL := log_2rd_pos hr hd
  have h32 : (1:ℝ) ≤ (32:ℝ)^(r+1) := one_le_pow₀ (by norm_num)
  have hrr : (r:ℝ)^2 ≤ (r:ℝ)^r := by
    have hr1 : (1:ℝ) ≤ r := by linarith
    have h1 : (r:ℝ)^(2:ℕ) ≤ (r:ℝ)^r := pow_le_pow_right₀ hr1 hr
    simpa using h1
  have h3 : (0:ℝ) ≤ (r:ℝ)^r := by positivity
  have h2 : (r:ℝ)^2 ≤ (r:ℝ)^r * (32:ℝ)^(r+1) := by
    have h4 : (r:ℝ)^2 * 1 ≤ (r:ℝ)^r * (32:ℝ)^(r+1) :=
      mul_le_mul hrr h32 (by norm_num) h3
    linarith
  have h5 : 2 * (r:ℝ)^2 * (d:ℝ) * Real.log (2*r*d)
      ≤ 2 * ((r:ℝ)^r * (32:ℝ)^(r+1)) * (d:ℝ) * Real.log (2*r*d) := by
    have hd0 : (0:ℝ) ≤ d := by positivity
    have hL0 : (0:ℝ) ≤ Real.log (2*r*d) := by positivity
    have h6 : 2 * (r:ℝ)^2 ≤ 2 * ((r:ℝ)^r * (32:ℝ)^(r+1)) :=
      mul_le_mul_of_nonneg_left h2 (by norm_num)
    have h7 : 2 * (r:ℝ)^2 * (d:ℝ) ≤ 2 * ((r:ℝ)^r * (32:ℝ)^(r+1)) * (d:ℝ) :=
      mul_le_mul_of_nonneg_right h6 hd0
    exact mul_le_mul_of_nonneg_right h7 hL0
  linarith [h5, h]


/-- Positivity of `n.descFactorial k`. -/
theorem descFactorial_pos_le {n k : ℕ} (hk : k ≤ n) : 0 < n.descFactorial k := by
  induction k with
  | zero => simp
  | succ j ih =>
      rw [Nat.descFactorial_succ]
      have h1 : 0 < n - j := by omega
      have h2 : 0 < n.descFactorial j := ih (by omega)
      positivity

/-- Descending-factorial recursion for the `Q`-quantity. -/
theorem descFact_ratio (r k : ℕ) (hk : k < r) :
    (((r+1).descFactorial (k+2) : ℕ) : ℝ) * (((k+2).factorial : ℕ) : ℝ) * (r:ℝ) / (r:ℝ)^(k+1)
      = ((((r+1).descFactorial (k+1) : ℕ) : ℝ) * (((k+1).factorial : ℕ) : ℝ) * (r:ℝ) / (r:ℝ)^k)
        * (((r:ℝ) - k) * (k+2) / (r:ℝ)) := by
  have hr0 : (r:ℝ) ≠ 0 := by
    have h : (0:ℝ) < r := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le k) hk)
    positivity
  have h1 : (r+1) - (k+1) = r - k := by omega
  have h2 : (((r+1).descFactorial (k+2) : ℕ) : ℝ)
      = (((r+1).descFactorial (k+1) : ℕ) : ℝ) * ((r:ℝ) - k) := by
    rw [Nat.descFactorial_succ, h1]; push_cast
    rw [Nat.cast_sub (le_of_lt hk)]
    ring
  have h3 : (((k+2).factorial : ℕ) : ℝ) = (((k+1).factorial : ℕ) : ℝ) * ((k:ℝ)+2) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [h2, h3, pow_succ]
  field_simp

/-- The one-step recursion for the auxiliary quantity `G`. -/
theorem gf_step (r d k : ℕ) (hk : k < r) :
    (((r+1).descFactorial (k+2) : ℕ) : ℝ) * (((k+2).factorial : ℕ) : ℝ) * (r:ℝ) / (r:ℝ)^(k+1)
        * (2:ℝ)^(k+1) / ((3.85:ℝ)^(k+1) * (2*(r:ℝ)*(d:ℝ))^(2*(k+1)))
      = ((((r+1).descFactorial (k+1) : ℕ) : ℝ) * (((k+1).factorial : ℕ) : ℝ) * (r:ℝ) / (r:ℝ)^k)
          * (2:ℝ)^k / ((3.85:ℝ)^k * (2*(r:ℝ)*(d:ℝ))^(2*k))
        * (((r:ℝ) - k) * ((k:ℝ)+2) * 2 / ((r:ℝ) * 3.85 * (2*(r:ℝ)*(d:ℝ))^2)) := by
  rw [descFact_ratio r k hk]
  rw [pow_succ (2:ℝ) k, pow_succ (3.85:ℝ) k,
      show 2*(k+1) = 2*k+2 by ring, pow_add]
  field_simp

/-- The recursion factor is at most one. -/
theorem gf_factor_le {r d k : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hk : k < r) :
    ((r:ℝ) - k) * ((k:ℝ)+2) * 2 / ((r:ℝ) * 3.85 * (2*(r:ℝ)*(d:ℝ))^2) ≤ 1 := by
  have hr2 : (2:ℝ) ≤ r := by exact_mod_cast hr
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hkr : (k:ℝ) < r := by exact_mod_cast hk
  rw [div_le_one (by positivity)]
  have h2 : ((r:ℝ) - k) * ((k:ℝ)+2) ≤ (r:ℝ)^2 := by
    have h3 : ((r:ℝ)-k + ((k:ℝ)+2))^2 ≤ (2*(r:ℝ))^2 := by nlinarith [hr2]
    nlinarith [sq_nonneg (((r:ℝ)-k) - ((k:ℝ)+2)), h3]
  calc ((r:ℝ) - k) * ((k:ℝ)+2) * 2 ≤ (r:ℝ)^2 * 2 := by nlinarith [h2]
    _ ≤ (r:ℝ) * 3.85 * (2*(r:ℝ)*(d:ℝ))^2 := by
        have h3 : (r:ℝ) * 3.85 * (2*(r:ℝ)*(d:ℝ))^2 = 15.4 * (r:ℝ)^3 * (d:ℝ)^2 := by ring
        rw [h3]
        have h4 : (2:ℝ) ≤ 15.4*(r:ℝ)*(d:ℝ)^2 := by nlinarith [hr2, hd1]
        nlinarith [h4, hr2]

end Work.BW
