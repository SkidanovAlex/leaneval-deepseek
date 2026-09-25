import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.NumberTheory.Robin.caMu_ge_iff_caF
import Submission.Commons.NumberTheory.Robin.caMu_pos
import Submission.Commons.Analysis.Real.log_one_add_inv_bounds

namespace Commons.NumberTheory.Robin

/-- `t ↦ (t+1)·log t` is strictly increasing on `[1,∞)`. -/
private lemma caG_lt {a b : ℝ} (ha : 1 ≤ a) (hab : a < b) :
    (a + 1) * Real.log a < (b + 1) * Real.log b := by
  have hb1 : 1 < b := lt_of_le_of_lt ha hab
  rcases eq_or_lt_of_le ha with h1 | h1
  · rw [← h1, Real.log_one, mul_zero]
    exact mul_pos (by linarith) (Real.log_pos hb1)
  · have hloga : 0 < Real.log a := Real.log_pos h1
    have hla : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) (le_of_lt hab)
    calc (a + 1) * Real.log a < (b + 1) * Real.log a :=
          mul_lt_mul_of_pos_right (by linarith) hloga
      _ ≤ (b + 1) * Real.log b :=
          mul_le_mul_of_nonneg_left hla (by linarith)

/-- `t ↦ (t+1)·log t` is monotone on `[1,∞)`. -/
private lemma caG_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (a + 1) * Real.log a ≤ (b + 1) * Real.log b := by
  rcases lt_or_eq_of_le hab with h | h
  · exact le_of_lt (caG_lt ha h)
  · rw [h]

/-- Numeric core: for `x ≥ 2`, `((123/250)x²+1)·log((123/250)x²) < x(x+1)·log x`. -/
private lemma caNum {x : ℝ} (hx : 2 ≤ x) :
    ((123 : ℝ) / 250 * x ^ 2 + 1) * Real.log ((123 : ℝ) / 250 * x ^ 2)
      < x * (x + 1) * Real.log x := by
  have hxpos : 0 < x := by linarith
  have hx2 : 0 < x ^ 2 := by positivity
  have hcpos : (0 : ℝ) < 123 / 250 := by norm_num
  have hclt : (123 : ℝ) / 250 < 1 := by norm_num
  have hcxpos : 0 < 123 / 250 * x ^ 2 := mul_pos hcpos hx2
  have hcxlt : 123 / 250 * x ^ 2 < x ^ 2 := by nlinarith [hx2, hclt]
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have h1 : Real.log (123 / 250 * x ^ 2) < 2 * Real.log x := by
    have h := Real.log_lt_log hcxpos hcxlt
    rw [Real.log_pow] at h
    simpa using h
  have h2 : 2 * (123 / 250 * x ^ 2 + 1) ≤ x * (x + 1) := by
    have hfac : (2 : ℝ) / 125 * x ^ 2 + x - 2
        = (x - 2) * ((2 : ℝ) / 125 * (x + 2) + 1) + 8 / 125 := by ring
    have hnn : 0 ≤ (x - 2) * ((2 : ℝ) / 125 * (x + 2) + 1) :=
      mul_nonneg (by linarith) (by nlinarith [hx])
    have hpos : 0 ≤ (2 : ℝ) / 125 * x ^ 2 + x - 2 := by
      rw [hfac]; linarith
    nlinarith [hpos]
  calc ((123 : ℝ) / 250 * x ^ 2 + 1) * Real.log (123 / 250 * x ^ 2)
      < (123 / 250 * x ^ 2 + 1) * (2 * Real.log x) :=
        mul_lt_mul_of_pos_left h1 (by positivity)
    _ ≤ x * (x + 1) * Real.log x := by
        have hm := mul_le_mul_of_nonneg_right h2 hlogx
        nlinarith [hm]

theorem ca_level_two_upper {ε ξ : ℝ} (hε : 0 < ε) (hξ : 1530 ≤ ξ)
    (hε1 : ε ≤ Real.log (1 + 1 / ξ) / Real.log ξ)
    (hε2 : Real.log (1 + 1 / (123 / 100 * ξ)) / Real.log (123 / 100 * ξ) < ε) :
    ∀ p : ℕ, Nat.Prime p →
      2 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / ((((p : ℝ) ^ (1 + ε))) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ →
      (p : ℝ) ≤ Nat.ceil (Real.sqrt (2.5 * ξ)) := by
  intro p hp hfloor
  have hp2 : 2 ≤ p := hp.two_le
  have hpr2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hprpos : (0 : ℝ) < (p : ℝ) := by linarith
  have hpr1 : (1 : ℝ) < (p : ℝ) := by linarith
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hpr1
  -- μ(p,ε) ≥ 2, hence ε ≤ F(p,2)
  have hmu_pos : 0 < Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / ((((p : ℝ) ^ (1 + ε))) - (p : ℝ))) / Real.log (p : ℝ) :=
    caMu_pos hp2 hε
  have hmu2 : (2 : ℝ) ≤ Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / ((((p : ℝ) ^ (1 + ε))) - (p : ℝ))) / Real.log (p : ℝ) :=
    le_trans (by exact_mod_cast hfloor) (Nat.floor_le (le_of_lt hmu_pos))
  have hεF : ε ≤ Real.log ((((p : ℝ) ^ (2 + 1 : ℕ)) - 1) / ((((p : ℝ) ^ (2 + 1 : ℕ))) - (p : ℝ))) / Real.log (p : ℝ) :=
    (caMu_ge_iff_caF p ε 2 hp2 hε (by norm_num)).mp hmu2
  have harg : ((p : ℝ) ^ (2 + 1 : ℕ) - 1) / ((p : ℝ) ^ (2 + 1 : ℕ) - (p : ℝ))
      = 1 + 1 / ((p : ℝ) * ((p : ℝ) + 1)) := by
    have hnum : ((p : ℝ) ^ (2 + 1 : ℕ)) = (p : ℝ) ^ 3 := by norm_num
    rw [hnum]
    have hp1ne : (p : ℝ) - 1 ≠ 0 := by linarith
    have hpp1ne : (p : ℝ) * ((p : ℝ) + 1) ≠ 0 := by positivity
    have e3 : (p : ℝ) ^ 3 - 1 = ((p : ℝ) - 1) * ((p : ℝ) ^ 2 + (p : ℝ) + 1) := by ring
    have e4 : (p : ℝ) ^ 3 - (p : ℝ) = ((p : ℝ) - 1) * ((p : ℝ) * ((p : ℝ) + 1)) := by ring
    rw [e3, e4, mul_div_mul_left _ _ hp1ne]
    rw [show (p : ℝ) ^ 2 + (p : ℝ) + 1 = (p : ℝ) * ((p : ℝ) + 1) + 1 by ring]
    rw [add_div, div_self hpp1ne]
  have hFeq : Real.log ((((p : ℝ) ^ (2 + 1 : ℕ)) - 1) / ((((p : ℝ) ^ (2 + 1 : ℕ))) - (p : ℝ))) / Real.log (p : ℝ)
      = Real.log (1 + 1 / ((p : ℝ) * ((p : ℝ) + 1))) / Real.log (p : ℝ) := by
    rw [harg]
  rw [hFeq] at hεF
  have hεlogp : ε * Real.log (p : ℝ) ≤ Real.log (1 + 1 / ((p : ℝ) * ((p : ℝ) + 1))) := by
    have h := mul_le_mul_of_nonneg_right hεF (le_of_lt hlogp)
    rwa [div_mul_cancel₀ _ (ne_of_gt hlogp)] at h
  have hlog_le : Real.log (1 + 1 / ((p : ℝ) * ((p : ℝ) + 1))) ≤ 1 / ((p : ℝ) * ((p : ℝ) + 1)) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / ((p : ℝ) * ((p : ℝ) + 1)) by positivity)
    linarith
  have hplog : (p : ℝ) * ((p : ℝ) + 1) * Real.log (p : ℝ) ≤ 1 / ε := by
    have hpos : (0 : ℝ) < (p : ℝ) * ((p : ℝ) + 1) := by positivity
    have hmain : ε * Real.log (p : ℝ) ≤ 1 / ((p : ℝ) * ((p : ℝ) + 1)) := le_trans hεlogp hlog_le
    have h2 : ((p : ℝ) * ((p : ℝ) + 1)) * (ε * Real.log (p : ℝ)) ≤ 1 := by
      have h3 := mul_le_mul_of_nonneg_left hmain (le_of_lt hpos)
      rw [mul_one_div, div_self (ne_of_gt hpos)] at h3
      exact h3
    rw [le_div_iff₀ hε]
    nlinarith [h2]
  -- second hypothesis: ε > log(1+1/s)/log s with s = 1.23 ξ
  set s : ℝ := 123 / 100 * ξ with hs
  have hs1 : 1 < s := by rw [hs]; nlinarith [hξ]
  have hspos : 0 < s := by linarith
  have hlogs : 0 < Real.log s := Real.log_pos hs1
  have hε2' : Real.log (1 + 1 / s) / Real.log s < ε := by rw [hs]; exact hε2
  have hlog1s : 0 < Real.log (1 + 1 / s) := by
    apply Real.log_pos
    have : 0 < 1 / s := one_div_pos.mpr hspos
    linarith
  have ha_lt : Real.log (1 + 1 / s) < ε * Real.log s := by
    have h := (div_lt_iff₀ hlogs).mp hε2'
    linarith
  have h1e : 1 / ε < Real.log s / Real.log (1 + 1 / s) := by
    rw [div_lt_div_iff₀ hε hlog1s]
    nlinarith [ha_lt]
  have hlow := (Commons.Analysis.Real.log_one_add_inv_bounds hspos).1
  have hgm : 1 < (s + 1) * Real.log (1 + 1 / s) := by
    have hsp1 : (0 : ℝ) < s + 1 := by linarith
    have h := mul_lt_mul_of_pos_left hlow hsp1
    rwa [mul_one_div, div_self (ne_of_gt hsp1)] at h
  have h2e : Real.log s / Real.log (1 + 1 / s) < (s + 1) * Real.log s := by
    rw [div_lt_iff₀ hlog1s]
    have h := mul_lt_mul_of_pos_right hgm hlogs
    nlinarith [h]
  have hrec : 1 / ε < (s + 1) * Real.log s := lt_trans h1e h2e
  have hKey : (p : ℝ) * ((p : ℝ) + 1) * Real.log (p : ℝ) < (s + 1) * Real.log s :=
    lt_of_le_of_lt hplog hrec
  have hA_inst : ((123 : ℝ) / 250 * (p : ℝ) ^ 2 + 1) * Real.log ((123 : ℝ) / 250 * (p : ℝ) ^ 2)
      < (p : ℝ) * ((p : ℝ) + 1) * Real.log (p : ℝ) :=
    caNum hpr2
  have hG1 : (1 : ℝ) ≤ (123 : ℝ) / 250 * (p : ℝ) ^ 2 := by nlinarith [hpr2]
  have hgt : (123 : ℝ) / 250 * (p : ℝ) ^ 2 < s := by
    by_contra hcon
    rw [not_lt] at hcon
    have hmono := caG_le (le_of_lt hs1) hcon
    linarith [hmono, hA_inst, hKey]
  have hfinal : (p : ℝ) ^ 2 < 2.5 * ξ := by
    have h1 : (250 / 123 : ℝ) * ((123 / 250) * (p : ℝ) ^ 2) < (250 / 123 : ℝ) * ((123 / 100) * ξ) :=
      mul_lt_mul_of_pos_left (by rw [← hs]; exact hgt) (by norm_num)
    have e1 : (250 / 123 : ℝ) * ((123 / 250) * (p : ℝ) ^ 2) = (p : ℝ) ^ 2 := by ring
    have e2 : (250 / 123 : ℝ) * ((123 / 100) * ξ) = 2.5 * ξ := by ring
    rw [e1, e2] at h1
    exact h1
  have h25pos : 0 < 2.5 * ξ := by nlinarith [hξ]
  have hple : (p : ℝ) ≤ Real.sqrt (2.5 * ξ) := by
    rw [Real.le_sqrt (le_of_lt hprpos) (le_of_lt h25pos)]
    exact le_of_lt hfinal
  calc (p : ℝ) ≤ Real.sqrt (2.5 * ξ) := hple
    _ ≤ Nat.ceil (Real.sqrt (2.5 * ξ)) := Nat.le_ceil _

end Commons.NumberTheory.Robin