import Mathlib
import Submission.Work.RHContract.A.regionII.caNet2_defs

namespace Work.RHContract.A.regionII.netGain

open Work.RHContract.A.regionII

/-! ## Helper lemmas for `massCore` -/

lemma sqrt2_ge : (141421356237 / 100000000000 : ℝ) ≤ Real.sqrt 2 := by
  rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num

lemma sqrt_sqrt2_le : Real.sqrt (Real.sqrt 2) ≤ 11892072 / 10000000 := by
  have h2 : Real.sqrt 2 ≤ 141421356238 / 100000000000 := by
    rw [Real.sqrt_le_iff]; norm_num
  rw [Real.sqrt_le_iff]
  exact ⟨by norm_num, le_trans h2 (by norm_num)⟩

lemma sqrt_115_ge : (107238 / 100000 : ℝ) ≤ Real.sqrt (115 / 100) := by
  rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num

/-- `t ↦ t − (21/10)√t` is monotone on `[441/400, ∞)`. -/
lemma h_mono {a b : ℝ} (ha : (441 / 400 : ℝ) ≤ a) (hab : a ≤ b) :
    a - 21 / 10 * Real.sqrt a ≤ b - 21 / 10 * Real.sqrt b := by
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := le_trans ha0 hab
  have hsab : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt hab
  have hsa : (21 / 20 : ℝ) ≤ Real.sqrt a := by
    rw [Real.le_sqrt (by norm_num) ha0]; nlinarith
  have hsb : (21 / 20 : ℝ) ≤ Real.sqrt b := le_trans hsa hsab
  have hdiff : (Real.sqrt b - Real.sqrt a) * (Real.sqrt b + Real.sqrt a) = b - a := by
    have h1 := Real.sq_sqrt hb0
    have h2 := Real.sq_sqrt ha0
    nlinarith [h1, h2]
  have hnn : 0 ≤ (Real.sqrt b - Real.sqrt a) * (Real.sqrt b + Real.sqrt a - 21 / 10) :=
    mul_nonneg (by linarith) (by linarith)
  have hexp : (Real.sqrt b - Real.sqrt a) * (Real.sqrt b + Real.sqrt a - 21 / 10)
      = (b - a) - 21 / 10 * (Real.sqrt b - Real.sqrt a) := by
    rw [mul_sub, hdiff]; ring
  rw [hexp] at hnn
  linarith

/-- `t ↦ t − (1/2)√t` is monotone on `[1/16, ∞)`. -/
lemma g_mono {a b : ℝ} (ha : (1 / 16 : ℝ) ≤ a) (hab : a ≤ b) :
    a - 1 / 2 * Real.sqrt a ≤ b - 1 / 2 * Real.sqrt b := by
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := le_trans ha0 hab
  have hsab : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt hab
  have hsa : (1 / 4 : ℝ) ≤ Real.sqrt a := by
    rw [Real.le_sqrt (by norm_num) ha0]; nlinarith
  have hsb : (1 / 4 : ℝ) ≤ Real.sqrt b := le_trans hsa hsab
  have hdiff : (Real.sqrt b - Real.sqrt a) * (Real.sqrt b + Real.sqrt a) = b - a := by
    have h1 := Real.sq_sqrt hb0
    have h2 := Real.sq_sqrt ha0
    nlinarith [h1, h2]
  have hnn : 0 ≤ (Real.sqrt b - Real.sqrt a) * (Real.sqrt b + Real.sqrt a - 1 / 2) :=
    mul_nonneg (by linarith) (by linarith)
  have hexp : (Real.sqrt b - Real.sqrt a) * (Real.sqrt b + Real.sqrt a - 1 / 2)
      = (b - a) - 1 / 2 * (Real.sqrt b - Real.sqrt a) := by
    rw [mul_sub, hdiff]; ring
  rw [hexp] at hnn
  linarith

theorem massCore (ξ : ℝ) (hlo : (100000 : ℝ) ≤ ξ) (hhi : ξ < (10 : ℝ) ^ 8) :
    netMasslb (Real.sqrt ξ) (Real.log ξ)
      ≤ ((netNf ξ : ℝ) - 21 / 10 * Real.sqrt (netNf ξ))
        - ((netPf ξ : ℝ) - (1 / 2) * Real.sqrt (netPf ξ)) := by
  set s := Real.sqrt ξ with hsdef
  set L := Real.log ξ with hLdef
  have hξpos : 0 < ξ := by linarith
  have hs0 : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.mpr hξpos
  have hsnn : 0 ≤ s := le_of_lt hs0
  have hL0 : 0 < L := by rw [hLdef]; exact Real.log_pos (by linarith)
  have hs316 : (316 : ℝ) ≤ s := by
    rw [hsdef, Real.le_sqrt (by norm_num) (le_of_lt hξpos)]
    nlinarith [hlo]
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hLdef]
    have hle : Real.log (100000 : ℝ) ≤ Real.log ξ :=
      Real.log_le_log (by norm_num) hlo
    have hge : (1 : ℝ) ≤ Real.log (100000 : ℝ) := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith [Real.exp_one_lt_d9]
    linarith
  -- expansion of netQlo
  have hA : netQlo ξ = Real.sqrt 2 * s - (Real.sqrt 2 * Real.log 2 / 2) * (s / L) := by
    unfold netQlo
    rw [← hsdef, ← hLdef]
    ring
  -- lower bound netQlo ξ ≥ 3
  have hfac : (65 / 100 : ℝ) ≤ 1 - Real.log 2 / (2 * L) := by
    have h2 : Real.log 2 ≤ 6931471808 / 10000000000 := by
      have h0 := Real.log_two_lt_d9
      norm_num at h0 ⊢
      linarith
    have h1 : Real.log 2 / (2 * L) ≤ Real.log 2 / 2 := by
      apply div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num)) (by norm_num : (0:ℝ) < 2)
      linarith
    have h3l : Real.log 2 / 2 ≤ 35 / 100 := by linarith
    linarith
  have hqge3 : (3 : ℝ) ≤ netQlo ξ := by
    have heq : netQlo ξ = Real.sqrt 2 * s * (1 - Real.log 2 / (2 * L)) := by
      unfold netQlo; rw [← hsdef, ← hLdef]
    rw [heq]
    have h1 : 7 / 5 * 316 ≤ Real.sqrt 2 * s := by
      have hb := mul_le_mul (show (7 / 5 : ℝ) ≤ Real.sqrt 2 by linarith [sqrt2_ge]) hs316
        (by norm_num) (by positivity)
      linarith [hb]
    have hb := mul_le_mul h1 hfac (by norm_num) (by positivity : (0:ℝ) ≤ Real.sqrt 2 * s)
    linarith [hb]
  have hqgeo : (441 / 400 : ℝ) ≤ netQlo ξ - 1 := by linarith
  have hNfge : netQlo ξ - 1 ≤ ((netNf ξ : ℕ) : ℝ) := by
    have h0 : netQlo ξ < ((netNf ξ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one (netQlo ξ)
    linarith
  have hPfle : ((netPf ξ : ℕ) : ℝ) ≤ 115 / 100 * s := by
    have h0 : ((netPf ξ : ℕ) : ℝ) ≤ 115 / 100 * Real.sqrt ξ := Nat.floor_le (by positivity)
    rwa [← hsdef] at h0
  have hPfge : (1 / 16 : ℝ) ≤ ((netPf ξ : ℕ) : ℝ) := by
    have h363 : (363 : ℕ) ≤ netPf ξ := by
      rw [netPf]
      apply Nat.le_floor
      rw [← hsdef]
      nlinarith [hs316]
    have h363' : (363 : ℝ) ≤ ((netPf ξ : ℕ) : ℝ) := by exact_mod_cast h363
    exact le_trans (by norm_num : (1 / 16 : ℝ) ≤ 363) h363'
  -- P1
  have hP1 : 26421 / 100000 * s - 49013 / 100000 * (s / L) ≤ netQlo ξ - 115 / 100 * s := by
    rw [hA]
    have h1 : (0 : ℝ) ≤ Real.sqrt 2 - 141421 / 100000 := by linarith [sqrt2_ge]
    have h2 : (0 : ℝ) ≤ 49013 / 100000 - Real.sqrt 2 * Real.log 2 / 2 := by
      linarith [net_sqrt2_log2_half]
    have h4 : (0 : ℝ) ≤ s / L := div_nonneg hsnn (le_of_lt hL0)
    nlinarith [mul_nonneg h1 hsnn, mul_nonneg h2 h4]
  -- P2
  have hsnd : Real.sqrt (netQlo ξ - 1) ≤ 11892072 / 10000000 * Real.sqrt s := by
    have hle : netQlo ξ - 1 ≤ Real.sqrt 2 * s := by
      rw [hA]
      have hb : (0 : ℝ) ≤ (Real.sqrt 2 * Real.log 2 / 2) * (s / L) :=
        mul_nonneg (div_nonneg (mul_nonneg (Real.sqrt_nonneg 2)
          (le_of_lt (Real.log_pos (by norm_num)))) (by norm_num))
          (div_nonneg hsnn (le_of_lt hL0))
      linarith
    calc Real.sqrt (netQlo ξ - 1) ≤ Real.sqrt (Real.sqrt 2 * s) := Real.sqrt_le_sqrt hle
      _ = Real.sqrt (Real.sqrt 2) * Real.sqrt s := Real.sqrt_mul (Real.sqrt_nonneg 2) s
      _ ≤ 11892072 / 10000000 * Real.sqrt s :=
          mul_le_mul_of_nonneg_right sqrt_sqrt2_le (Real.sqrt_nonneg s)
  have hP2 : 21 / 10 * Real.sqrt (netQlo ξ - 1)
      ≤ 196189 / 100000 * Real.sqrt s + 1 / 2 * Real.sqrt (115 / 100 * s) := by
    have hh1 : 21 / 10 * Real.sqrt (netQlo ξ - 1)
        ≤ 21 / 10 * (11892072 / 10000000 * Real.sqrt s) :=
      mul_le_mul_of_nonneg_left hsnd (by norm_num)
    have hh2 : 21 / 10 * (11892072 / 10000000 * Real.sqrt s)
        ≤ 24974 / 10000 * Real.sqrt s := by
      nlinarith [Real.sqrt_nonneg s]
    have h115 : (107238 / 100000 : ℝ) * Real.sqrt s ≤ Real.sqrt (115 / 100 * s) := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 115 / 100) s]
      exact mul_le_mul_of_nonneg_right sqrt_115_ge (Real.sqrt_nonneg s)
    have hh3 : 24974 / 10000 * Real.sqrt s
        ≤ 196189 / 100000 * Real.sqrt s + 1 / 2 * Real.sqrt (115 / 100 * s) := by
      have h := mul_le_mul_of_nonneg_left h115 (by norm_num : (0:ℝ) ≤ 1 / 2)
      nlinarith [h, Real.sqrt_nonneg s]
    linarith [hh1, hh2, hh3]
  have hA2 := h_mono hqgeo hNfge
  have hB2 := g_mono hPfge hPfle
  rw [netMasslb, show 49013 / 100000 * s / L = 49013 / 100000 * (s / L) by ring]
  linarith [hP1, hP2, hA2, hB2]

end Work.RHContract.A.regionII.netGain
