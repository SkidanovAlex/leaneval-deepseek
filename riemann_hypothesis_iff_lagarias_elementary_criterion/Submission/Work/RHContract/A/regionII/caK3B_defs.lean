import Mathlib
import Submission.Work.RHContract.A.regionII.Defs
import Submission.Work.RHContract.Corpus
import Submission.Commons.Analysis.Real.log_one_add_inv_bounds

/-!
# `caK3B_defs` — definitions and numeric input for `caK3_upper_B`

For `ξ ≥ 10^5` put

* `kcc ξ = (1 − 3/√ξ) / ((ξ + 0.45 ξ^{3/4} + 2) · log (ξ + 0.45 ξ^{3/4} + 2))`  (this is
  `RegionII.caClo ξ`, the certified lower bound for `caC ε` coming from `hA2`);
* `kB ξ = ξ · kcc ξ · log ξ`  (the constant `B₀` of the region-II K₃ estimate: the term
  `caK3term ε p` is at most `(1/ξ)·(1/k_p)·(1 − kB ξ + 1/(p−1))` with `k_p = e_p + 1`).

The numeric content proved here is `1 − kB ξ ≤ 3/√ξ + 0.495 ξ^{−1/4} + 2.2 ξ^{−1}`
(hence `kB ξ ≥ 24/25`), and the two "short window" bounds
`ξ^{1/3}(1 − kB ξ) < 2.88`, `ξ^{1/4}(1 − kB ξ) < 3.84`.
-/

namespace Work.RHContract.A.regionII

noncomputable section

/-- The certified constant `(1 − 3/√ξ)/((ξ + 0.45 ξ^{3/4} + 2) log(ξ + 0.45 ξ^{3/4} + 2))`. -/
noncomputable def kcc (ξ : ℝ) : ℝ :=
  (1 - 3/Real.sqrt ξ)/((ξ + 0.45*ξ^(3/4:ℝ) + 2)*Real.log (ξ + 0.45*ξ^(3/4:ℝ) + 2))

/-- `B₀ = ξ · kcc ξ · log ξ`. -/
noncomputable def kB (ξ : ℝ) : ℝ := ξ * kcc ξ * Real.log ξ

lemma kcc_eq_caClo (ξ : ℝ) : kcc ξ = Work.RHContract.A.RegionII.caClo ξ := rfl

/-- `x^(1/k) ≤ c` when `x ≤ c^k`. -/
lemma rpow_div_le_of_le_pow {x c : ℝ} (k : ℕ) (hc : 0 ≤ c) (hx : 0 ≤ x) (hk : 0 < k)
    (h : x ≤ c^k) : x^(1/(k:ℝ)) ≤ c := by
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have h1 : x^(1/(k:ℝ)) ≤ (c^k : ℝ)^(1/(k:ℝ)) := Real.rpow_le_rpow hx h (by positivity)
  have h2 : ((c^k : ℝ))^(1/(k:ℝ)) = c := by
    rw [← Real.rpow_natCast c k, ← Real.rpow_mul hc]
    have : (k:ℝ) * (1/(k:ℝ)) = 1 := by field_simp
    rw [this, Real.rpow_one]
  linarith

/-- `c ≤ x^(1/k)` when `c^k ≤ x`. -/
lemma le_rpow_div_of_pow_le {x c : ℝ} (k : ℕ) (hc : 0 ≤ c) (hx : 0 ≤ x) (hk : 0 < k)
    (h : c^k ≤ x) : c ≤ x^(1/(k:ℝ)) := by
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have h1 : ((c^k : ℝ))^(1/(k:ℝ)) ≤ x^(1/(k:ℝ)) := Real.rpow_le_rpow (by positivity) h (by positivity)
  have h2 : ((c^k : ℝ))^(1/(k:ℝ)) = c := by
    rw [← Real.rpow_natCast c k, ← Real.rpow_mul hc]
    have : (k:ℝ) * (1/(k:ℝ)) = 1 := by field_simp
    rw [this, Real.rpow_one]
  linarith

lemma log10_low : (2.2794 : ℝ) ≤ Real.log 10 := by
  have h1 : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [← Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (5:ℝ) ≠ 0)]; norm_num
  have h2 : Real.log 5 = 2 * Real.log 2 + Real.log (5/4) := by
    have h : (5:ℝ) = 4 * (5/4) := by norm_num
    rw [h, Real.log_mul (by norm_num) (by norm_num), show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    push_cast; ring
  have h3 : (1/5 : ℝ) ≤ Real.log (5/4) := by
    have hh := (Commons.Analysis.Real.log_one_add_inv_bounds (t := 4) (by norm_num)).1
    have h4 : (1:ℝ) + 1/4 = 5/4 := by norm_num
    linarith [hh]
  have h4 : (0.6931471803 : ℝ) ≤ Real.log 2 := Real.log_two_gt_d9.le
  linarith

lemma log1e5_ge : (11.3 : ℝ) ≤ Real.log 100000 := by
  have h : (100000 : ℝ) = 10^5 := by norm_num
  rw [h, Real.log_pow]
  have := log10_low
  push_cast
  nlinarith

lemma log10_up : Real.log 10 ≤ 2.3295 := by
  have h1 : Real.log 10 = 3 * Real.log 2 + Real.log (5/4) := by
    have h : (10:ℝ) = 8 * (5/4) := by norm_num
    rw [h, Real.log_mul (by norm_num) (by norm_num), show (8:ℝ) = 2^3 by norm_num, Real.log_pow]
    push_cast; ring
  have h2 : Real.log (5/4) ≤ (5/4 : ℝ) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h3 : Real.log 2 ≤ (0.6931471808 : ℝ) := Real.log_two_lt_d9.le
  rw [h1]; linarith

lemma log1e8_le (ξ : ℝ) (hlo : 1 ≤ ξ) (hhi : ξ < 10^8) : Real.log ξ ≤ (18636:ℝ)/1000 := by
  have h : Real.log ξ ≤ Real.log (10^8 : ℝ) := Real.log_le_log (by linarith) hhi.le
  rw [Real.log_pow] at h
  have := log10_up
  push_cast at h ⊢
  linarith

lemma kB_delta (ξ : ℝ) (hlo : 100000 ≤ ξ) :
    1 - kB ξ ≤ 3/Real.sqrt ξ + (495/1000)*ξ^(-(1/4:ℝ)) + (22/10)*ξ^(-(1:ℝ)) := by
  have hξ0 : 0 < ξ := by linarith
  have hξ1 : 1 ≤ ξ := by linarith
  have hL : (11.3:ℝ) ≤ Real.log ξ := le_trans log1e5_ge (Real.log_le_log (by norm_num) hlo)
  have hLpos : 0 < Real.log ξ := by linarith
  have h17 : (17:ℝ) ≤ ξ^(1/4:ℝ) :=
    le_rpow_div_of_pow_le 4 (by norm_num) hξ0.le (by norm_num) (by norm_num; linarith)
  set x0 : ℝ := ξ + 0.45 * ξ ^ (3/4:ℝ) + 2 with hx0
  have hx0pos : 0 < x0 := by rw [hx0]; positivity
  set u : ℝ := x0/ξ - 1 with hu
  have hu_eq : u = 0.45/(ξ^(1/4:ℝ)) + 2/ξ := by
    rw [hu, hx0]
    have hrpow : ξ ^ (3/4:ℝ) = ξ/ξ^(1/4:ℝ) := by
      rw [show (3/4:ℝ) = 1 - 1/4 by norm_num, Real.rpow_sub hξ0 1 (1/4), Real.rpow_one]
    rw [hrpow]
    field_simp
    ring
  have hu0 : 0 ≤ u := by rw [hu_eq]; positivity
  have hu1 : u ≤ 1 := by
    rw [hu_eq]
    have h2 : 0.45/(ξ^(1/4:ℝ)) ≤ 0.45/17 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) h17
    have h3 : 2/ξ ≤ 2/100000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlo
    linarith
  have hx0eq : x0 = ξ * (1 + u) := by
    rw [hu]; rw [hx0]; field_simp; ring
  have h1u : 0 ≤ 1 + u := by linarith
  have h1u' : 0 < 1 + u := by linarith
  set w : ℝ := Real.log (1 + u)/Real.log ξ with hw
  have hwge : 0 ≤ w := by
    rw [hw]; exact div_nonneg (Real.log_nonneg (by linarith : (1:ℝ) ≤ 1 + u)) hLpos.le
  have hwle : w ≤ u/Real.log ξ := by
    rw [hw]
    apply div_le_div_of_nonneg_right _ hLpos.le
    simpa using Real.log_le_sub_one_of_pos h1u'
  have hw1 : w ≤ 1 := by
    rw [hw, div_le_one hLpos]
    have h := Real.log_le_sub_one_of_pos h1u'
    linarith
  have hlogx0 : Real.log x0 = Real.log ξ * (1 + w) := by
    rw [hx0eq, Real.log_mul (ne_of_gt hξ0) (by positivity), hw]
    have h : Real.log ξ * (1 + Real.log (1 + u) / Real.log ξ)
        = Real.log ξ + Real.log (1 + u) := by
      rw [mul_add, mul_one, mul_div_cancel₀ (Real.log (1+u)) (ne_of_gt hLpos)]
    linarith [h]
  have hlogx0pos : 0 < Real.log x0 := by rw [hlogx0]; positivity
  have hB0 : kB ξ = (1 - 3/Real.sqrt ξ) * (1/(1 + u)) * (1/(1 + w)) := by
    have hx0' : ξ + 0.45*ξ^(3/4:ℝ) + 2 = x0 := hx0.symm
    have hmain : ξ * kcc ξ * Real.log ξ
        = (1 - 3/Real.sqrt ξ) * (ξ/x0) * (Real.log ξ / Real.log x0) := by
      rw [kcc, hx0']
      field_simp
    rw [show kB ξ = ξ * kcc ξ * Real.log ξ from rfl, hmain, hlogx0, hx0eq]
    have h1 : ξ/(ξ*(1+u)) = 1/(1+u) := by field_simp
    have h2 : Real.log ξ/(Real.log ξ*(1+w)) = 1/(1+w) := by field_simp
    rw [h1, h2]
  have hr0 : 0 ≤ 3/Real.sqrt ξ := div_nonneg (by norm_num) (Real.sqrt_nonneg ξ)
  have hr1 : 3/Real.sqrt ξ ≤ 1 := by
    rw [div_le_one (Real.sqrt_pos.mpr hξ0)]
    have : (3:ℝ) ≤ Real.sqrt ξ := by
      rw [Real.le_sqrt (by norm_num) (le_of_lt hξ0)]; linarith
    linarith
  have h1v2 : (1:ℝ)/(1 + u) ≥ 1 - u := by
    rw [ge_iff_le, le_div_iff₀ h1u']; nlinarith
  have h1w2 : (1:ℝ)/(1 + w) ≥ 1 - w := by
    rw [ge_iff_le, le_div_iff₀ (by linarith)]; nlinarith
  have hstep1 : (1 - 3/Real.sqrt ξ) * (1/(1 + u)) * (1/(1 + w))
      ≥ 1 - (3/Real.sqrt ξ + u + w) := by
    have hr : 0 ≤ 1 - 3/Real.sqrt ξ := by linarith
    have hA : (1 - 3/Real.sqrt ξ) * (1/(1 + u)) ≥ (1 - 3/Real.sqrt ξ) * (1-u) :=
      mul_le_mul_of_nonneg_left h1v2 hr
    have hC : (1 - 3/Real.sqrt ξ) * (1/(1 + u)) * (1/(1 + w))
        ≥ (1 - 3/Real.sqrt ξ) * (1-u) * (1-w) := by
      have h := mul_le_mul hA h1w2 (by linarith [hw1]) (by positivity)
      linarith [h]
    have hD : (1 - 3/Real.sqrt ξ) * (1-u) * (1-w)
        ≥ 1 - (3/Real.sqrt ξ + u + w) := by
      have h1 := hu0
      nlinarith [mul_nonneg h1 hwge, mul_nonneg hr h1, mul_nonneg hr hwge,
        mul_nonneg (mul_nonneg hr h1) hwge, mul_nonneg (mul_nonneg hr0 h1) hwge]
    linarith
  rw [hB0]
  have hfin : 3/Real.sqrt ξ + u + w ≤
      3/Real.sqrt ξ + (495/1000)*ξ^(-(1/4:ℝ)) + (22/10)*ξ^(-(1:ℝ)) := by
    rw [hu_eq]
    have h1 : ξ ^ (-(1/4:ℝ)) = 1/ξ^(1/4:ℝ) := by rw [Real.rpow_neg hξ0.le, inv_eq_one_div]
    have h2 : ξ ^ (-(1:ℝ)) = 1/ξ := by
      rw [Real.rpow_neg hξ0.le, Real.rpow_one, inv_eq_one_div]
    rw [h1, h2]
    have h3 : w ≤ (0.45/(ξ^(1/4:ℝ)) + 2/ξ)/11.3 := by
      rw [hw, div_le_div_iff₀ hLpos (by norm_num)]
      have h4 : Real.log (1 + u) ≤ 0.45/(ξ^(1/4:ℝ)) + 2/ξ := by
        have h5 := hu_eq
        have := Real.log_le_sub_one_of_pos h1u'
        linarith
      nlinarith
    have hq : 0 < ξ^(1/4:ℝ) := Real.rpow_pos_of_pos hξ0 _
    have e1 : (0.45/(ξ^(1/4:ℝ)) + 2/ξ) + (0.45/(ξ^(1/4:ℝ)) + 2/ξ)/11.3
        = (0.45*(1+1/11.3))/ξ^(1/4:ℝ) + (2*(1+1/11.3))/ξ := by
      field_simp
    have key : (0.45*(1+1/11.3))/ξ^(1/4:ℝ) + (2*(1+1/11.3))/ξ
        ≤ (495/1000)*(1/ξ^(1/4:ℝ)) + (22/10)*(1/ξ) := by
      have h2' : (0.45*(1+1/11.3) : ℝ) ≤ 495/1000 := by norm_num
      have h3' : (2*(1+1/11.3) : ℝ) ≤ 22/10 := by norm_num
      have h4' : (0.45*(1+1/11.3))/ξ^(1/4:ℝ) ≤ (495/1000)*(1/ξ^(1/4:ℝ)) := by
        simpa only [div_eq_mul_inv, one_mul, mul_one, one_div] using
          div_le_div_of_nonneg_right h2' (le_of_lt hq)
      have h5' : (2*(1+1/11.3))/ξ ≤ (22/10)*(1/ξ) := by
        simpa only [div_eq_mul_inv, one_mul, mul_one, one_div] using
          div_le_div_of_nonneg_right h3' hξ0.le
      linarith
    linarith [h3, e1.le, key]
  linarith [hstep1, hfin]



/-- `kcc ξ ≤ caC ε` from the `A2` hypothesis `ψ(ξ) ≤ ξ + 0.45ξ^{3/4} + 2`. -/
lemma kcc_le_caC (ε : ℝ) (hε : 0 < ε) (hlo : 100000 ≤ (Work.RHPlan.caXi ε : ℝ))
    (hA2 : |Chebyshev.psi (Work.RHPlan.caXi ε : ℝ) - (Work.RHPlan.caXi ε : ℝ)|
        ≤ 0.45 * (Work.RHPlan.caXi ε : ℝ) ^ (3/4:ℝ) + 2) :
    kcc (Work.RHPlan.caXi ε : ℝ) ≤ Work.RHContract.Margin.caC ε := by
  set ξ : ℝ := (Work.RHPlan.caXi ε : ℝ) with hξ
  have hξ0 : 0 < ξ := by linarith
  have hξ1 : 1 ≤ ξ := by linarith
  have hψup : Chebyshev.psi ξ ≤ ξ + 0.45 * ξ^(3/4:ℝ) + 2 := by
    have := (abs_le.mp hA2).2
    rw [hξ] at this
    linarith
  have hp34 : ξ^(3/4:ℝ) ≤ ξ := by
    rw [show (3/4:ℝ) = 1 - 1/4 by norm_num, Real.rpow_sub hξ0 1 (1/4), Real.rpow_one]
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hξ0 _)]
    have h2 : (1:ℝ) ≤ ξ^(1/4:ℝ) := Real.one_le_rpow hξ1 (by norm_num)
    nlinarith [hξ0]
  have hψlow : (1/2)*ξ ≤ Chebyshev.psi ξ := by
    have h := (abs_le.mp hA2).1
    rw [hξ] at h
    linarith
  have hψ0 : 0 < Chebyshev.psi ξ := by linarith
  have hlogψ : Real.log (Chebyshev.psi ξ) ≤ Real.log (ξ + 0.45 * ξ^(3/4:ℝ) + 2) :=
    Real.log_le_log hψ0 hψup
  have hlogx0pos : 0 < Real.log (ξ + 0.45 * ξ^(3/4:ℝ) + 2) := by
    apply Real.log_pos; nlinarith [Real.rpow_nonneg hξ0.le (3/4:ℝ)]
  have hlogψpos : 0 < Real.log (Chebyshev.psi ξ) := by
    apply Real.log_pos; linarith
  have hnum : 0 ≤ 1 - 3/Real.sqrt ξ := by
    rw [sub_nonneg, div_le_one (Real.sqrt_pos.mpr hξ0)]
    have : (3:ℝ) ≤ Real.sqrt ξ := by
      rw [Real.le_sqrt (by norm_num) (le_of_lt hξ0)]; linarith
    linarith
  have hden : Chebyshev.psi ξ * Real.log (Chebyshev.psi ξ)
      ≤ (ξ + 0.45 * ξ^(3/4:ℝ) + 2) * Real.log (ξ + 0.45 * ξ^(3/4:ℝ) + 2) :=
    mul_le_mul hψup hlogψ (le_of_lt hlogψpos) (by positivity)
  rw [kcc, Work.RHContract.Margin.caC]
  rw [hξ] at hnum hden ⊢
  exact div_le_div_of_nonneg_left hnum (by positivity) hden

lemma kB_le_one (ξ : ℝ) (hlo : 100000 ≤ ξ) : kB ξ ≤ 1 := by
  have hξ0 : 0 < ξ := by linarith
  have hξ1 : 1 ≤ ξ := by linarith
  have h34 : ξ^(3/4:ℝ) ≤ ξ := by
    rw [show (3/4:ℝ) = 1 - 1/4 by norm_num, Real.rpow_sub hξ0 1 (1/4), Real.rpow_one]
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hξ0 _)]
    have h2 : (1:ℝ) ≤ ξ^(1/4:ℝ) := Real.one_le_rpow hξ1 (by norm_num)
    nlinarith [hξ0]
  have h34nn : 0 ≤ ξ^(3/4:ℝ) := Real.rpow_nonneg hξ0.le _
  have hx0pos : 0 < ξ + 0.45*ξ^(3/4:ℝ) + 2 := by positivity
  have hx0ge : ξ ≤ ξ + 0.45*ξ^(3/4:ℝ) + 2 := by linarith
  have hlogpos : 0 < Real.log (ξ + 0.45*ξ^(3/4:ℝ) + 2) := by
    apply Real.log_pos; linarith
  have hlogle : Real.log ξ ≤ Real.log (ξ + 0.45*ξ^(3/4:ℝ) + 2) :=
    Real.log_le_log hξ0 hx0ge
  have hnum0 : 0 ≤ 1 - 3/Real.sqrt ξ := by
    rw [sub_nonneg, div_le_one (Real.sqrt_pos.mpr hξ0)]
    have : (3:ℝ) ≤ Real.sqrt ξ := by
      rw [Real.le_sqrt (by norm_num) (le_of_lt hξ0)]; linarith
    linarith
  have hnum : 1 - 3/Real.sqrt ξ ≤ 1 := by
    have : 0 ≤ 3/Real.sqrt ξ := div_nonneg (by norm_num) (Real.sqrt_nonneg ξ)
    linarith
  have hsplit : kB ξ = (1 - 3/Real.sqrt ξ) * (ξ/(ξ + 0.45*ξ^(3/4:ℝ) + 2))
        * (Real.log ξ/Real.log (ξ + 0.45*ξ^(3/4:ℝ) + 2)) := by
    rw [kB, kcc]
    field_simp
  rw [hsplit]
  have hx1 : ξ/(ξ + 0.45*ξ^(3/4:ℝ) + 2) ≤ 1 := by
    rw [div_le_one hx0pos]; linarith
  have hx0nn : 0 ≤ ξ/(ξ + 0.45*ξ^(3/4:ℝ) + 2) := by positivity
  have hl1 : Real.log ξ/Real.log (ξ + 0.45*ξ^(3/4:ℝ) + 2) ≤ 1 := by
    rw [div_le_one hlogpos]; exact hlogle
  have hLy : 0 < Real.log ξ := lt_of_lt_of_le (by norm_num)
    (le_trans log1e5_ge (Real.log_le_log (by norm_num) hlo))
  have hl0 : 0 ≤ Real.log ξ/Real.log (ξ + 0.45*ξ^(3/4:ℝ) + 2) :=
    div_nonneg hLy.le hlogpos.le
  calc (1 - 3/Real.sqrt ξ) * (ξ/(ξ + 0.45*ξ^(3/4:ℝ) + 2))
        * (Real.log ξ/Real.log (ξ + 0.45*ξ^(3/4:ℝ) + 2))
      ≤ 1 * 1 * 1 := by
        refine mul_le_mul (mul_le_mul hnum hx1 hx0nn (by norm_num)) hl1 hl0 (by norm_num)
    _ = 1 := by norm_num

lemma kB_ge (ξ : ℝ) (hlo : 100000 ≤ ξ) : (24/25:ℝ) ≤ kB ξ := by
  have hξ0 : 0 < ξ := by linarith
  have hd := kB_delta ξ hlo
  have hsp : 3/Real.sqrt ξ ≤ 3/316 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    rw [Real.le_sqrt (by norm_num) (le_of_lt hξ0)]
    linarith
  have h17 : (17:ℝ) ≤ ξ^(1/4:ℝ) :=
    le_rpow_div_of_pow_le 4 (by norm_num) hξ0.le (by norm_num) (by norm_num; linarith)
  have h14 : ξ^(-(1/4:ℝ)) ≤ 1/17 := by
    rw [Real.rpow_neg hξ0.le, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h17
  have h1 : ξ^(-(1:ℝ)) ≤ 1/100000 := by
    rw [Real.rpow_neg hξ0.le, Real.rpow_one, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hlo
  nlinarith [hd, hsp, h14, h1]

lemma rpow_facts (ξ : ℝ) (hlo : 100000 ≤ ξ) (hhi : ξ < 10^8) :
    (16:ℝ) ≤ ξ^(1/4:ℝ) ∧ (9:ℝ) ≤ ξ^(1/5:ℝ) ∧ (6.8:ℝ) ≤ ξ^(1/6:ℝ) ∧ (45:ℝ) ≤ ξ^(1/3:ℝ) ∧
    (46.4:ℝ) ≤ ξ^(1/3:ℝ) ∧ ξ^(1/12:ℝ) ≤ 4.7 ∧ (316:ℝ) ≤ Real.sqrt ξ ∧
    (17:ℝ) ≤ ξ^(1/4:ℝ) ∧
    ξ^(-(1/6:ℝ)) ≤ 1/6.8 ∧ ξ^(-(2/3:ℝ)) ≤ 1/2152 ∧ ξ^(-(3/4:ℝ)) ≤ 1/4913 ∧
    ξ^(-(1/4:ℝ)) ≤ 1/17 := by
  have hξ0 : 0 < ξ := by linarith
  have h4 : (16:ℝ) ≤ ξ^(1/4:ℝ) :=
    le_rpow_div_of_pow_le 4 (by norm_num) hξ0.le (by norm_num) (by norm_num; linarith)
  have h17 : (17:ℝ) ≤ ξ^(1/4:ℝ) :=
    le_rpow_div_of_pow_le 4 (by norm_num) hξ0.le (by norm_num) (by norm_num; linarith)
  have h5 : (9:ℝ) ≤ ξ^(1/5:ℝ) :=
    le_rpow_div_of_pow_le 5 (by norm_num) hξ0.le (by norm_num) (by norm_num; linarith)
  have h6 : (6.8:ℝ) ≤ ξ^(1/6:ℝ) :=
    le_rpow_div_of_pow_le 6 (by norm_num) hξ0.le (by norm_num) (by norm_num; linarith)
  have h3 : (45:ℝ) ≤ ξ^(1/3:ℝ) :=
    le_rpow_div_of_pow_le 3 (by norm_num) hξ0.le (by norm_num) (by norm_num; linarith)
  have h3' : (46.4:ℝ) ≤ ξ^(1/3:ℝ) :=
    le_rpow_div_of_pow_le 3 (by norm_num) hξ0.le (by norm_num) (by norm_num; linarith)
  have h12 : ξ^(1/12:ℝ) ≤ 4.7 :=
    rpow_div_le_of_le_pow 12 (by norm_num) hξ0.le (by norm_num) (by norm_num; linarith)
  have hsq : (316:ℝ) ≤ Real.sqrt ξ := by
    rw [Real.le_sqrt (by norm_num) (le_of_lt hξ0)]; linarith
  have h16 : ξ^(-(1/6:ℝ)) ≤ 1/6.8 := by
    rw [Real.rpow_neg hξ0.le, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h6
  have h23 : ξ^(-(2/3:ℝ)) ≤ 1/2152 := by
    have hpow : (2152:ℝ) ≤ ξ^(2/3:ℝ) := by
      have he : ξ^(2/3:ℝ) = ξ^(1/3:ℝ) * ξ^(1/3:ℝ) := by
        rw [show (2/3:ℝ) = 1/3 + 1/3 by norm_num, Real.rpow_add hξ0]
      rw [he]
      have h2 : (46.4:ℝ) * 46.4 ≤ ξ^(1/3:ℝ) * ξ^(1/3:ℝ) :=
        mul_le_mul h3' h3' (by norm_num) (by linarith)
      linarith
    rw [Real.rpow_neg hξ0.le, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hpow
  have h34 : ξ^(-(3/4:ℝ)) ≤ 1/4913 := by
    have hpow : (4913:ℝ) ≤ ξ^(3/4:ℝ) := by
      have he : ξ^(3/4:ℝ) = ξ^(1/4:ℝ) * ξ^(1/4:ℝ) * ξ^(1/4:ℝ) := by
        rw [show (3/4:ℝ) = 1/4 + 1/4 + 1/4 by norm_num, Real.rpow_add hξ0, Real.rpow_add hξ0]
      rw [he]
      have h2 : (17:ℝ) * 17 * 17 ≤ ξ^(1/4:ℝ) * ξ^(1/4:ℝ) * ξ^(1/4:ℝ) := by
        have h1 : (17:ℝ) * 17 ≤ ξ^(1/4:ℝ) * ξ^(1/4:ℝ) :=
          mul_le_mul h17 h17 (by norm_num) (by linarith)
        exact mul_le_mul h1 h17 (by norm_num) (by positivity)
      linarith
    rw [Real.rpow_neg hξ0.le, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hpow
  have h14 : ξ^(-(1/4:ℝ)) ≤ 1/17 := by
    rw [Real.rpow_neg hξ0.le, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h17
  exact ⟨h4, h5, h6, h3, h3', h12, hsq, h17, h16, h23, h34, h14⟩

lemma kB_win3 (ξ : ℝ) (hlo : 100000 ≤ ξ) (hhi : ξ < 10^8) :
    ξ^(1/3:ℝ) * (1 - kB ξ) < 2.88 := by
  obtain ⟨-, -, -, -, -, h12, -, -, h16, h23, -, -⟩ := rpow_facts ξ hlo hhi
  have hξ0 : 0 < ξ := by linarith
  have hd := kB_delta ξ hlo
  have hmul : ξ^(1/3:ℝ) * (3/Real.sqrt ξ + (495/1000)*ξ^(-(1/4:ℝ)) + (22/10)*ξ^(-(1:ℝ)))
      = 3*ξ^(-(1/6:ℝ)) + (495/1000)*ξ^(1/12:ℝ) + (22/10)*ξ^(-(2/3:ℝ)) := by
    have e1 : ξ^(1/3:ℝ) * (3/Real.sqrt ξ) = 3*ξ^(-(1/6:ℝ)) := by
      have hs : Real.sqrt ξ = ξ^(1/2:ℝ) := Real.sqrt_eq_rpow ξ
      rw [hs, show -(1/6:ℝ) = 1/3 - 1/2 by norm_num, Real.rpow_sub hξ0]
      field_simp
    have e2 : ξ^(1/3:ℝ) * ((495/1000)*ξ^(-(1/4:ℝ))) = (495/1000)*ξ^(1/12:ℝ) := by
      rw [show (1/12:ℝ) = 1/3 + (-(1/4)) by norm_num, Real.rpow_add hξ0]
      ring
    have e3 : ξ^(1/3:ℝ) * ((22/10)*ξ^(-(1:ℝ))) = (22/10)*ξ^(-(2/3:ℝ)) := by
      rw [show -(2/3:ℝ) = 1/3 + (-(1)) by norm_num, Real.rpow_add hξ0]
      ring
    rw [mul_add, mul_add, e1, e2, e3]
  have hfin : 3*ξ^(-(1/6:ℝ)) + (495/1000)*ξ^(1/12:ℝ) + (22/10)*ξ^(-(2/3:ℝ)) < 2.88 := by
    have h1 : 3*ξ^(-(1/6:ℝ)) ≤ 3*(1/6.8) :=
      mul_le_mul_of_nonneg_left h16 (by norm_num)
    have h2 : (495/1000)*ξ^(1/12:ℝ) ≤ (495/1000)*4.7 :=
      mul_le_mul_of_nonneg_left h12 (by norm_num)
    have h3 : (22/10)*ξ^(-(2/3:ℝ)) ≤ (22/10)*(1/2152) :=
      mul_le_mul_of_nonneg_left h23 (by norm_num)
    linarith
  have hpos : 0 < ξ^(1/3:ℝ) := Real.rpow_pos_of_pos hξ0 _
  calc ξ^(1/3:ℝ) * (1 - kB ξ)
      ≤ ξ^(1/3:ℝ) * (3/Real.sqrt ξ + (495/1000)*ξ^(-(1/4:ℝ)) + (22/10)*ξ^(-(1:ℝ))) :=
        mul_le_mul_of_nonneg_left hd (le_of_lt hpos)
    _ = 3*ξ^(-(1/6:ℝ)) + (495/1000)*ξ^(1/12:ℝ) + (22/10)*ξ^(-(2/3:ℝ)) := hmul
    _ < 2.88 := hfin

lemma kB_win4 (ξ : ℝ) (hlo : 100000 ≤ ξ) (hhi : ξ < 10^8) :
    ξ^(1/4:ℝ) * (1 - kB ξ) < 3.84 := by
  obtain ⟨-, -, -, -, -, -, -, h17, -, -, h34, -⟩ := rpow_facts ξ hlo hhi
  have hξ0 : 0 < ξ := by linarith
  have hd := kB_delta ξ hlo
  have hmul : ξ^(1/4:ℝ) * (3/Real.sqrt ξ + (495/1000)*ξ^(-(1/4:ℝ)) + (22/10)*ξ^(-(1:ℝ)))
      = 3*ξ^(-(1/4:ℝ)) + (495/1000)*ξ^(0:ℝ) + (22/10)*ξ^(-(3/4:ℝ)) := by
    have e1 : ξ^(1/4:ℝ) * (3/Real.sqrt ξ) = 3*ξ^(-(1/4:ℝ)) := by
      have hs : Real.sqrt ξ = ξ^(1/2:ℝ) := Real.sqrt_eq_rpow ξ
      rw [hs, show -(1/4:ℝ) = 1/4 - 1/2 by norm_num, Real.rpow_sub hξ0]
      field_simp
    have e2 : ξ^(1/4:ℝ) * ((495/1000)*ξ^(-(1/4:ℝ))) = (495/1000)*ξ^(0:ℝ) := by
      rw [show (0:ℝ) = 1/4 + (-(1/4)) by norm_num, Real.rpow_add hξ0]
      ring
    have e3 : ξ^(1/4:ℝ) * ((22/10)*ξ^(-(1:ℝ))) = (22/10)*ξ^(-(3/4:ℝ)) := by
      rw [show -(3/4:ℝ) = 1/4 + (-(1)) by norm_num, Real.rpow_add hξ0]
      ring
    rw [mul_add, mul_add, e1, e2, e3]
  have hfin : 3*ξ^(-(1/4:ℝ)) + (495/1000)*ξ^(0:ℝ) + (22/10)*ξ^(-(3/4:ℝ)) < 3.84 := by
    have h1 : 3*ξ^(-(1/4:ℝ)) ≤ 3*(1/17) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [Real.rpow_neg hξ0.le, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) h17
    have h2 : ξ^(0:ℝ) = (1:ℝ) := Real.rpow_zero ξ
    have h3 : (22/10)*ξ^(-(3/4:ℝ)) ≤ (22/10)*(1/4913) :=
      mul_le_mul_of_nonneg_left h34 (by norm_num)
    rw [h2]
    linarith
  have hpos : 0 < ξ^(1/4:ℝ) := Real.rpow_pos_of_pos hξ0 _
  calc ξ^(1/4:ℝ) * (1 - kB ξ)
      ≤ ξ^(1/4:ℝ) * (3/Real.sqrt ξ + (495/1000)*ξ^(-(1/4:ℝ)) + (22/10)*ξ^(-(1:ℝ))) :=
        mul_le_mul_of_nonneg_left hd (le_of_lt hpos)
    _ = 3*ξ^(-(1/4:ℝ)) + (495/1000)*ξ^(0:ℝ) + (22/10)*ξ^(-(3/4:ℝ)) := hmul
    _ < 3.84 := hfin

end
end Work.RHContract.A.regionII
