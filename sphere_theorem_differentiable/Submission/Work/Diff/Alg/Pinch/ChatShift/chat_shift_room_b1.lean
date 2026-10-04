import Mathlib
import Submission.Work.Diff.Alg.Pinch.ChatShiftDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `b ≤ 1/2` branch of the "room" condition `ChSRoom` for the shift inclusion

This file proves `chat_shift_room_b1`: for `0 < s < 1/2` there is `ε₀ > 0`, `ε₀ ≤ 1/2 - s`, such
that for every `ε ∈ (0, ε₀]` the two *scalar* inequalities `ChSRoom` hold with

* `a = chatA n s`, `a' = chatA n (s+ε)` (the `a`-parameters of the Brendle–Schoen family),
* `b = s`, `b' = s+ε` (the `b`-parameters, both `≤ 1/2`),
* `P = chatP n s`, `P' = chatP n (s+ε)`,
* `t = α/(n(n-1))` with `α ∈ [1/4,1]`, and
* `σ` an arbitrary number in `(0, 1/(1+2(n-1)·chatA n s)]`.

## Mathematical content

Write `c = n - 2 ≥ 0`, `u = s`, `v = s+ε`.  All the content is in the two exact identities

* `chatA n v - chatA n u = (v-u)(2 + c(v+u-2uv)) / (2(1+cu²)(1+cv²))`,
* `chatP n v - chatP n u = c(v²-u²) / ((1+cu²)(1+cv²))`,

from which, for `0 ≤ u ≤ v ≤ 1/2`,

* `0 ≤ chatA n v - chatA n u ≤ (n/2)(v-u)`,  `0 ≤ chatP n v - chatP n u ≤ (n-2)(v-u)`,
* `chatA n v ≤ 1/2`, `1 ≤ (n-1)(1 - chatP n v)`.

Since `chSg1 n s (s+ε) = -ε/(1+c(s+ε))` (so `|chSg1| ≤ ε`) and
`chSg2 n a a' t σ = (t - 2σ·Δ/n)/(1+2(n-1)a') ≥ (t-ε)/n` because `Δ ≤ (n/2)ε`, `σ ≤ 1`,
`a' ≤ 1/2`, it remains to check the two linear inequalities

* `ε·C_EF·C_T ≤ (t-ε)/n`,  i.e. `ε·(n·C_EF·C_T + 1) ≤ t`,
* `ε·(n-2)·C_ric + (n-2)ε/n ≤ (t-ε)/n`, i.e. `ε·((n-1) + n(n-2)C_ric) ≤ t`,

which hold as soon as `ε₀ ≤ T0/(n·C_EF·C_T+1)` and `ε₀ ≤ T0/((n-1)+n(n-2)C_ric)` with
`T0 = (1/4)/(n(n-1)) ≤ t` (as `α ≥ 1/4`).  This is the announced `ε₀`.
-/

set_option maxHeartbeats 1600000

namespace Work.Diff.Alg.Pinch.ChatShift

open Work.Diff.Alg.Pinch

/-! ## Two exact difference identities -/

private lemma chatA_sub_eq (n : ℕ) (hn : 2 ≤ n) (u v : ℝ) :
    chatA n v - chatA n u
      = (v - u) * (2 + ((n:ℝ)-2)*(v+u-2*u*v))
          / (2*(1+((n:ℝ)-2)*u^2)*(1+((n:ℝ)-2)*v^2)) := by
  have hdu : (0:ℝ) < 1 + ((n:ℝ)-2)*u^2 := chatA_denom_pos hn u
  have hdv : (0:ℝ) < 1 + ((n:ℝ)-2)*v^2 := chatA_denom_pos hn v
  rw [chatA, chatA]
  rw [div_sub_div _ _ (by positivity) (by positivity)]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

private lemma chatP_sub_eq (n : ℕ) (hn : 2 ≤ n) (u v : ℝ) :
    chatP n v - chatP n u
      = ((n:ℝ)-2)*(v^2-u^2)/((1+((n:ℝ)-2)*u^2)*(1+((n:ℝ)-2)*v^2)) := by
  have hdu : (0:ℝ) < 1 + ((n:ℝ)-2)*u^2 := chatA_denom_pos hn u
  have hdv : (0:ℝ) < 1 + ((n:ℝ)-2)*v^2 := chatA_denom_pos hn v
  rw [chatP, chatP]
  have e : (1 - 1/(1+((n:ℝ)-2)*v^2)) - (1 - 1/(1+((n:ℝ)-2)*u^2))
      = 1/(1+((n:ℝ)-2)*u^2) - 1/(1+((n:ℝ)-2)*v^2) := by ring
  rw [e]
  rw [div_sub_div _ _ (by positivity) (by positivity)]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- `1 - chatP n t = 1/(1+(n-2)t²)`. -/
private lemma one_sub_chatP_eq (n : ℕ) (t : ℝ) :
    1 - chatP n t = 1/(1+((n:ℝ)-2)*t^2) := by
  rw [chatP]; ring

/-! ## The elementary bounds on the parameters -/

/-- For `0 ≤ u ≤ v ≤ 1/2`: `0 ≤ chatA n v - chatA n u ≤ (n/2)(v-u)`. -/
private lemma chatA_sub_bounds (n : ℕ) (hn : 2 ≤ n) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hv : v ≤ 1/2) :
    0 ≤ chatA n v - chatA n u ∧ chatA n v - chatA n u ≤ (n:ℝ)/2 * (v - u) := by
  have hc : (0:ℝ) ≤ (n:ℝ) - 2 := chat_c_nonneg hn
  have hnR : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hw0 : 0 ≤ v + u - 2*u*v := by nlinarith
  have hw1 : v + u - 2*u*v ≤ 1/2 := by nlinarith
  have hA1 : 1 ≤ 1 + ((n:ℝ)-2)*u^2 := by nlinarith [sq_nonneg u]
  have hA2 : 1 ≤ 1 + ((n:ℝ)-2)*v^2 := by nlinarith [sq_nonneg v]
  have hA1' : (0:ℝ) ≤ 1 + ((n:ℝ)-2)*u^2 := by linarith
  have hAB : (1:ℝ) ≤ (1 + ((n:ℝ)-2)*u^2)*(1 + ((n:ℝ)-2)*v^2) := by
    simpa using mul_le_mul hA1 hA2 (by norm_num) hA1'
  have hD : (0:ℝ) < 2*(1+((n:ℝ)-2)*u^2)*(1+((n:ℝ)-2)*v^2) := by positivity
  have hnD : (n:ℝ) ≤ (n:ℝ)/2 * (2*(1+((n:ℝ)-2)*u^2)*(1+((n:ℝ)-2)*v^2)) := by
    have : (2:ℝ) ≤ 2*(1+((n:ℝ)-2)*u^2)*(1+((n:ℝ)-2)*v^2) := by nlinarith
    calc (n:ℝ) = (n:ℝ)/2 * 2 := by ring
      _ ≤ (n:ℝ)/2 * (2*(1+((n:ℝ)-2)*u^2)*(1+((n:ℝ)-2)*v^2)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
  have hvu : 0 ≤ v - u := by linarith
  have hnum : 2 + ((n:ℝ)-2)*(v+u-2*u*v) ≤ (n:ℝ) := by nlinarith
  rw [chatA_sub_eq n hn]
  constructor
  · apply div_nonneg
    · exact mul_nonneg hvu (by nlinarith [hw0, hc])
    · positivity
  · rw [div_le_iff₀ hD]
    calc (v - u) * (2 + ((n:ℝ)-2)*(v+u-2*u*v))
        ≤ (v - u) * (n:ℝ) := mul_le_mul_of_nonneg_left hnum hvu
      _ = (n:ℝ) * (v - u) := by ring
      _ ≤ (n:ℝ)/2 * (2*(1+((n:ℝ)-2)*u^2)*(1+((n:ℝ)-2)*v^2)) * (v - u) :=
            mul_le_mul_of_nonneg_right hnD hvu
      _ = (n:ℝ)/2 * (v - u) * (2*(1+((n:ℝ)-2)*u^2)*(1+((n:ℝ)-2)*v^2)) := by ring

/-- For `0 ≤ u ≤ v ≤ 1/2`: `0 ≤ chatP n v - chatP n u ≤ (n-2)(v-u)`. -/
private lemma chatP_sub_bounds (n : ℕ) (hn : 2 ≤ n) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hv : v ≤ 1/2) :
    0 ≤ chatP n v - chatP n u ∧ chatP n v - chatP n u ≤ ((n:ℝ)-2) * (v - u) := by
  have hc : (0:ℝ) ≤ (n:ℝ) - 2 := chat_c_nonneg hn
  have hDu : 0 < 1 + ((n:ℝ)-2)*u^2 := chatA_denom_pos hn u
  have hDv : 0 < 1 + ((n:ℝ)-2)*v^2 := chatA_denom_pos hn v
  have hDu1 : 1 ≤ 1 + ((n:ℝ)-2)*u^2 := by linarith [mul_nonneg hc (sq_nonneg u)]
  have hDv1 : 1 ≤ 1 + ((n:ℝ)-2)*v^2 := by linarith [mul_nonneg hc (sq_nonneg v)]
  have hprod1 : (1:ℝ) ≤ (1+((n:ℝ)-2)*u^2)*(1+((n:ℝ)-2)*v^2) := by
    simpa using mul_le_mul hDu1 hDv1 (by norm_num) (by linarith)
  have hvu : 0 ≤ v - u := by linarith
  have hvu' : 0 ≤ v^2 - u^2 := by nlinarith
  have hsum1 : v + u ≤ 1 := by linarith
  rw [chatP_sub_eq n hn]
  constructor
  · apply div_nonneg
    · exact mul_nonneg hc hvu'
    · positivity
  · rw [div_le_iff₀ (by positivity : (0:ℝ) < (1+((n:ℝ)-2)*u^2)*(1+((n:ℝ)-2)*v^2))]
    have hfac : v^2 - u^2 = (v-u)*(v+u) := by ring
    rw [hfac]
    calc ((n:ℝ)-2)*((v-u)*(v+u)) = ((n:ℝ)-2)*(v-u)*(v+u) := by ring
      _ ≤ ((n:ℝ)-2)*(v-u)*1 := mul_le_mul_of_nonneg_left hsum1 (mul_nonneg hc hvu)
      _ ≤ ((n:ℝ)-2)*(v-u)*((1+((n:ℝ)-2)*u^2)*(1+((n:ℝ)-2)*v^2)) :=
            mul_le_mul_of_nonneg_left hprod1 (mul_nonneg hc hvu)

/-- For `0 ≤ v ≤ 1/2`: `chatA n v ≤ 1/2`. -/
private lemma chatA_le_half (n : ℕ) (hn : 2 ≤ n) {v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ 1/2) :
    chatA n v ≤ 1/2 := by
  have hD : 0 < 2*(1+((n:ℝ)-2)*v^2) := by
    have := chatA_denom_pos hn v
    positivity
  rcases eq_or_lt_of_le hv0 with h | h
  · rw [← h, chatA]
    simp
  · rw [chatA_eq (ne_of_gt h), div_le_iff₀ hD]
    nlinarith

/-- For `0 ≤ v ≤ 1/2`: `1 ≤ (n-1)(1 - chatP n v)`. -/
private lemma one_le_pred_mul_one_sub_chatP (n : ℕ) (hn : 2 ≤ n) {v : ℝ} (hv0 : 0 ≤ v)
    (hv : v ≤ 1/2) :
    1 ≤ ((n:ℝ)-1) * (1 - chatP n v) := by
  have hc : (0:ℝ) ≤ (n:ℝ) - 2 := chat_c_nonneg hn
  have hD : 0 < 1 + ((n:ℝ)-2)*v^2 := chatA_denom_pos hn v
  have hv2 : v^2 ≤ 1/4 := by
    have := mul_le_mul hv hv hv0 (by norm_num : (0:ℝ) ≤ 1/2)
    nlinarith
  rw [one_sub_chatP_eq]
  rw [show ((n:ℝ)-1) * (1/(1+((n:ℝ)-2)*v^2)) = ((n:ℝ)-1)/(1+((n:ℝ)-2)*v^2) from by ring]
  rw [le_div_iff₀ hD]
  nlinarith [hv2, hc]

/-! ## The main theorem -/

theorem chat_shift_room_b1 (n : ℕ) (hn : 2 ≤ n) (C_EF C_T C_ric : ℝ)
    (hC_EF : 0 ≤ C_EF) (hC_T : 0 ≤ C_T) (hC_ric : 0 ≤ C_ric) :
    ∀ s : ℝ, 0 < s → s < 1 / 2 →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 - s ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
          ∀ α σ : ℝ, 1 / 4 ≤ α → α ≤ 1 → 0 < σ →
            σ ≤ 1 / (1 + 2 * ((n : ℝ) - 1) * Work.Diff.Alg.Pinch.chatA n s) →
            Work.Diff.Alg.Pinch.ChSRoom n C_EF C_T C_ric
              (Work.Diff.Alg.Pinch.chatA n s) (Work.Diff.Alg.Pinch.chatA n (s + ε)) s (s + ε)
              (Work.Diff.Alg.Pinch.chatP n s) (Work.Diff.Alg.Pinch.chatP n (s + ε))
              (α / ((n : ℝ) * ((n : ℝ) - 1))) σ := by
  intro s hs0 hs1
  have hn0 : (0:ℝ) < (n:ℝ) := by
    have : (0:ℕ) < n := by omega
    exact_mod_cast this
  have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hc0 : (0:ℝ) ≤ (n:ℝ) - 2 := by linarith
  have hnm1 : (1:ℝ) ≤ (n:ℝ) - 1 := by linarith
  have hnm1pos : (0:ℝ) < (n:ℝ) - 1 := by linarith
  have hprodpos : (0:ℝ) < (n:ℝ) * ((n:ℝ) - 1) := mul_pos hn0 hnm1pos
  set T0 : ℝ := (1/4) / ((n:ℝ)*((n:ℝ)-1)) with hT0def
  have hT0pos : 0 < T0 := by rw [hT0def]; positivity
  have hd1pos : 0 < (n:ℝ)*C_EF*C_T + 1 := by
    have h : 0 ≤ (n:ℝ)*C_EF*C_T := mul_nonneg (mul_nonneg hn0.le hC_EF) hC_T
    linarith
  have hd2pos : 0 < ((n:ℝ)-1) + (n:ℝ)*((n:ℝ)-2)*C_ric := by
    have h : 0 ≤ (n:ℝ)*((n:ℝ)-2)*C_ric := mul_nonneg (mul_nonneg hn0.le hc0) hC_ric
    linarith
  refine ⟨min (1/2 - s)
      (min (T0/((n:ℝ)*C_EF*C_T + 1))
        (T0/(((n:ℝ)-1) + (n:ℝ)*((n:ℝ)-2)*C_ric))), ?_, ?_, ?_⟩
  · have h1 : (0:ℝ) < 1/2 - s := by linarith
    exact lt_min h1 (lt_min (div_pos hT0pos hd1pos) (div_pos hT0pos hd2pos))
  · exact min_le_left _ _
  · intro ε hε0 hεle α σ hα1 hα2 hσ0 hσle
    set t : ℝ := α / ((n:ℝ)*((n:ℝ)-1)) with htdef
    have ht0 : T0 ≤ t := by
      rw [htdef, hT0def, div_le_iff₀ hprodpos, div_mul_cancel₀ α (ne_of_gt hprodpos)]
      exact hα1
    have htpos : 0 < t := lt_of_lt_of_le hT0pos ht0
    have hε1 : ε ≤ T0/((n:ℝ)*C_EF*C_T + 1) :=
      hεle.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hε2 : ε ≤ T0/(((n:ℝ)-1) + (n:ℝ)*((n:ℝ)-2)*C_ric) :=
      hεle.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hεs : ε ≤ 1/2 - s := hεle.trans (min_le_left _ _)
    have hA1 : ε * ((n:ℝ)*C_EF*C_T + 1) ≤ T0 := (le_div_iff₀ hd1pos).mp hε1
    have hA2 : ε * (((n:ℝ)-1) + (n:ℝ)*((n:ℝ)-2)*C_ric) ≤ T0 := (le_div_iff₀ hd2pos).mp hε2
    have hεt : ε ≤ t := by
      have h1 : T0/((n:ℝ)*C_EF*C_T + 1) ≤ T0 := by
        rw [div_le_iff₀ hd1pos]
        have hge : (1:ℝ) ≤ (n:ℝ)*C_EF*C_T + 1 := by
          have h : 0 ≤ (n:ℝ)*C_EF*C_T := mul_nonneg (mul_nonneg hn0.le hC_EF) hC_T
          linarith
        simpa using mul_le_mul_of_nonneg_left hge hT0pos.le
      exact hε1.trans (h1.trans ht0)
    have htε0 : 0 ≤ t - ε := by linarith
    have hsv : s ≤ s + ε := by linarith
    have hv0 : 0 ≤ s + ε := by linarith
    have hv1 : s + ε ≤ 1/2 := by linarith
    obtain ⟨hΔ0, hΔub⟩ := chatA_sub_bounds n hn hs0.le hsv hv1
    have hΔub' : chatA n (s+ε) - chatA n s ≤ (n:ℝ)/2 * ε := by
      have h := hΔub
      rw [show s + ε - s = ε from by ring] at h
      exact h
    obtain ⟨hP0, hPub⟩ := chatP_sub_bounds n hn hs0.le hsv hv1
    have hPub' : chatP n (s+ε) - chatP n s ≤ ((n:ℝ)-2) * ε := by
      have h := hPub
      rw [show s + ε - s = ε from by ring] at h
      exact h
    have ha'0 : 0 ≤ chatA n (s+ε) := chatA_nonneg hn hv0
    have ha'half : chatA n (s+ε) ≤ 1/2 := chatA_le_half n hn hv0 hv1
    have hden'pos : 0 < 1 + 2*((n:ℝ)-1)*chatA n (s+ε) := by nlinarith [hnm1, ha'0]
    have hden'le : 1 + 2*((n:ℝ)-1)*chatA n (s+ε) ≤ (n:ℝ) := by nlinarith [hnm1, ha'half]
    have ha0 : 0 ≤ chatA n s := chatA_nonneg hn hs0.le
    have hσ1 : σ ≤ 1 := by
      have hge : (1:ℝ) ≤ 1 + 2*((n:ℝ)-1)*chatA n s := by nlinarith [hnm1, ha0]
      calc σ ≤ 1/(1 + 2*((n:ℝ)-1)*chatA n s) := hσle
        _ ≤ 1 := by
          rw [div_le_one (by linarith : (0:ℝ) < 1 + 2*((n:ℝ)-1)*chatA n s)]
          linarith
    have hγ1 : |chSg1 n s (s+ε)| ≤ ε := by
      have hd : (0:ℝ) < 1 + ((n:ℝ)-2)*(s+ε) := by nlinarith [hc0, hv0]
      rw [chSg1, show s - (s + ε) = -ε from by ring, abs_div, abs_neg,
        abs_of_nonneg hε0.le, abs_of_pos hd, div_le_iff₀ hd]
      nlinarith [hε0, mul_nonneg hc0 hv0]
    have hγ2 : (t - ε)/(n:ℝ) ≤ chSg2 n (chatA n s) (chatA n (s+ε)) t σ := by
      rw [chSg2]
      have hstep : 2*σ*(chatA n (s+ε) - chatA n s)/(n:ℝ) ≤ ε := by
        rw [div_le_iff₀ hn0]
        have h1 : 2*σ*(chatA n (s+ε) - chatA n s) ≤ 2*σ*((n:ℝ)/2*ε) :=
          mul_le_mul_of_nonneg_left hΔub' (by linarith [hσ0.le])
        have h3 : σ*(n:ℝ)*ε ≤ (n:ℝ)*ε := by
          have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hσ1 hn0.le) hε0.le
          nlinarith [h]
        nlinarith [h1, h3]
      have hnum : t - ε ≤ t + 2*σ*(chatA n s - chatA n (s+ε))/(n:ℝ) := by
        have h : 2*σ*(chatA n s - chatA n (s+ε))/(n:ℝ)
            = -(2*σ*(chatA n (s+ε) - chatA n s)/(n:ℝ)) := by ring
        rw [h]; linarith
      have hnum0 : 0 ≤ t + 2*σ*(chatA n s - chatA n (s+ε))/(n:ℝ) := by linarith
      exact div_le_div₀ hnum0 hnum hden'pos hden'le
    rw [Work.Diff.Alg.Pinch.ChSRoom]
    constructor
    · have hCT : 0 ≤ C_EF * C_T := mul_nonneg hC_EF hC_T
      have h1 : |chSg1 n s (s+ε)| * (C_EF*C_T) ≤ ε * (C_EF*C_T) :=
        mul_le_mul_of_nonneg_right hγ1 hCT
      have h2 : |chSg1 n s (s+ε)| * (C_EF*C_T) * σ ≤ ε * (C_EF*C_T) * σ :=
        mul_le_mul_of_nonneg_right h1 hσ0.le
      have h3 : ε * (C_EF*C_T) * σ ≤ ε * (C_EF*C_T) * 1 :=
        mul_le_mul_of_nonneg_left hσ1 (mul_nonneg hε0.le hCT)
      have h4 : ε * (C_EF*C_T) * 1 ≤ (t - ε)/(n:ℝ) := by
        rw [le_div_iff₀ hn0]
        have hAt : ε * ((n:ℝ)*C_EF*C_T + 1) ≤ t := le_trans hA1 ht0
        nlinarith [hAt]
      calc |chSg1 n s (s+ε)| * C_EF * C_T * σ
          ≤ ε * C_EF * C_T * σ := by nlinarith [h2]
        _ ≤ ε * C_EF * C_T := by nlinarith [h3]
        _ ≤ (t - ε)/(n:ℝ) := by nlinarith [h4]
        _ ≤ chSg2 n (chatA n s) (chatA n (s+ε)) t σ := hγ2
    · have hD : (t - ε)/(n:ℝ)
          ≤ chSg2 n (chatA n s) (chatA n (s+ε)) t σ * ((n:ℝ)-1) * (1 - chatP n (s+ε)) := by
        have h1 : 1 ≤ ((n:ℝ)-1) * (1 - chatP n (s+ε)) :=
          one_le_pred_mul_one_sub_chatP n hn hv0 hv1
        have h3 : 0 ≤ chSg2 n (chatA n s) (chatA n (s+ε)) t σ := by
          have h4 : 0 ≤ (t - ε)/(n:ℝ) := div_nonneg htε0 hn0.le
          linarith [hγ2]
        have hstep : (t - ε)/(n:ℝ) * 1
            ≤ chSg2 n (chatA n s) (chatA n (s+ε)) t σ * (((n:ℝ)-1) * (1 - chatP n (s+ε))) :=
          mul_le_mul hγ2 h1 zero_le_one h3
        nlinarith [hstep]
      have hC : ε*((n:ℝ)-2)*C_ric + ((n:ℝ)-2)*ε/(n:ℝ) ≤ (t - ε)/(n:ℝ) := by
        rw [le_div_iff₀ hn0]
        have hmul : (ε*((n:ℝ)-2)*C_ric + ((n:ℝ)-2)*ε/(n:ℝ)) * (n:ℝ)
            = ε*(((n:ℝ)-1) + (n:ℝ)*((n:ℝ)-2)*C_ric) - ε := by
          rw [add_mul, div_mul_cancel₀ (((n:ℝ)-2)*ε) (ne_of_gt hn0)]
          ring
        have hAt : ε * (((n:ℝ)-1) + (n:ℝ)*((n:ℝ)-2)*C_ric) ≤ t := le_trans hA2 ht0
        nlinarith [hmul, hAt]
      have hB : |chSg1 n s (s+ε)| * ((n:ℝ)-2) * C_ric * σ
            + σ * (chatP n (s+ε) - chatP n s)/(n:ℝ)
          ≤ ε*((n:ℝ)-2)*C_ric + ((n:ℝ)-2)*ε/(n:ℝ) := by
        have hcR : 0 ≤ ((n:ℝ)-2)*C_ric := mul_nonneg hc0 hC_ric
        have hb1 : |chSg1 n s (s+ε)| * (((n:ℝ)-2)*C_ric) * σ
            ≤ ε * (((n:ℝ)-2)*C_ric) * σ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hγ1 hcR) hσ0.le
        have hb2 : ε * (((n:ℝ)-2)*C_ric) * σ ≤ ε * (((n:ℝ)-2)*C_ric) * 1 :=
          mul_le_mul_of_nonneg_left hσ1 (mul_nonneg hε0.le hcR)
        have hb3 : σ * (chatP n (s+ε) - chatP n s) ≤ ((n:ℝ)-2)*ε := by
          simpa using mul_le_mul hσ1 hPub' hP0 zero_le_one
        have hb4 : σ * (chatP n (s+ε) - chatP n s)/(n:ℝ) ≤ ((n:ℝ)-2)*ε/(n:ℝ) := by
          rw [div_le_iff₀ hn0, div_mul_cancel₀ (((n:ℝ)-2)*ε) (ne_of_gt hn0)]
          exact hb3
        nlinarith [hb1, hb2, hb4]
      calc chSg2 n (chatA n s) (chatA n (s+ε)) t σ * ((n:ℝ)-1) * (1 - chatP n (s+ε))
          ≥ (t - ε)/(n:ℝ) := hD
        _ ≥ ε*((n:ℝ)-2)*C_ric + ((n:ℝ)-2)*ε/(n:ℝ) := hC
        _ ≥ |chSg1 n s (s+ε)| * ((n:ℝ)-2) * C_ric * σ
              + σ * (chatP n (s+ε) - chatP n s)/(n:ℝ) := hB

end Work.Diff.Alg.Pinch.ChatShift
