import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

namespace Work.Diff.C

open Real
open scoped ContDiff

/-- Basic facts about `δ = η^{1/3}` under the smallness hypothesis on `η`. -/
lemma delta_basics {n : ℕ} (hn : 2 ≤ n) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ 1 / (10 ^ 18 * ((n : ℝ) + 2) ^ 3)) :
    0 < η ^ (1 / 3 : ℝ) ∧ (η ^ (1 / 3 : ℝ)) ^ 3 = η ∧
      η ^ (1 / 3 : ℝ) ≤ 1 / (10 ^ 6 * ((n : ℝ) + 2)) := by
  have hδ0 : 0 < η ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hη0 _
  have hδ3 : (η ^ (1 / 3 : ℝ)) ^ 3 = η := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hη0.le]; norm_num
  have hδle : η ^ (1 / 3 : ℝ) ≤ 1 / (10 ^ 6 * ((n : ℝ) + 2)) := by
    have hkey : η ≤ (1 / (10 ^ 6 * ((n : ℝ) + 2))) ^ 3 := by
      have heq : (1 / (10 ^ 6 * ((n : ℝ) + 2))) ^ 3
          = 1 / (10 ^ 18 * ((n : ℝ) + 2) ^ 3) := by
        rw [div_pow, one_pow]; congr 1; ring
      rw [heq]; exact hη
    rw [← hδ3] at hkey
    exact (pow_le_pow_iff_left₀ hδ0.le (by positivity) (by norm_num : (3 : ℕ) ≠ 0)).mp hkey
  exact ⟨hδ0, hδ3, hδle⟩

theorem cend_constants {n : ℕ} (hn : 2 ≤ n) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ 1 / (10 ^ 18 * ((n : ℝ) + 2) ^ 3)) :
    let δ : ℝ := η ^ (1 / 3 : ℝ)
    let c : ℝ := 100 * δ ^ 2
    let ε₁ : ℝ := δ ^ 2
    let α : ℝ := 1000 * δ
    0 < c ∧ c ≤ 1 / 4 ∧ 0 < α ∧ α ≤ 1 / 4 ∧ 0 ≤ ε₁ ∧
    3 * c ≤ 1 - Real.cos α ∧ 4 * ε₁ * Real.pi < c ∧
    Real.arccos (-1 + c) < Real.pi / Real.sqrt (1 + η) ∧
    (∀ d : ℝ, 0 < d → d ≤ Real.arccos (-1 + c) →
      max (Real.cos d - Real.sin d * Real.sqrt (1 + η) * Real.cot (Real.sqrt (1 + η) * d)) 0
        ≤ ε₁) ∧
    100 * ((n : ℝ) + 2) * (ε₁ * Real.pi + α + Real.sqrt c) < 1 := by
  dsimp only
  set δ : ℝ := η ^ (1 / 3 : ℝ) with hδdef
  obtain ⟨hδ0', hδ3', hδle'⟩ := delta_basics hn hη0 hη
  have hδ0 : 0 < δ := by rw [hδdef]; exact hδ0'
  have hδ3 : δ ^ 3 = η := by rw [hδdef]; exact hδ3'
  have hδle : δ ≤ 1 / (10 ^ 6 * ((n : ℝ) + 2)) := by rw [hδdef]; exact hδle'
  have hA1 : (1 : ℝ) ≤ (n : ℝ) + 2 := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hδ1 : δ ≤ 1 / 10 ^ 6 := by
    calc δ ≤ 1 / (10 ^ 6 * ((n : ℝ) + 2)) := hδle
      _ ≤ 1 / (10 ^ 6 * 1) :=
            one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 10 ^ 6 * 1)
              (by nlinarith only [hA1])
      _ = 1 / 10 ^ 6 := by norm_num
  have hπδ3 : Real.pi * δ ^ 3 ≤ 4 * δ := by
    have h2 : δ ^ 2 ≤ 1 := by nlinarith only [hδ0, hδ1]
    have hπδ : Real.pi * δ ^ 2 ≤ 4 := by nlinarith only [Real.pi_lt_four, h2, Real.pi_pos]
    calc Real.pi * δ ^ 3 = (Real.pi * δ ^ 2) * δ := by ring
      _ ≤ 4 * δ := mul_le_mul_of_nonneg_right hπδ hδ0.le
  rw [← hδ3]
  set c : ℝ := 100 * δ ^ 2 with hcdef₀
  set ε₁ : ℝ := δ ^ 2 with hεdef
  set α : ℝ := 1000 * δ with hαdef
  set β : ℝ := Real.sqrt (1 + δ ^ 3) with hβdef
  have hcdef : c = 100 * δ ^ 2 := by rw [hcdef₀, hεdef]
  -- preliminary estimates, shared by several conjuncts
  have hεnn : 0 ≤ ε₁ := by rw [hεdef]; positivity
  have hc0 : 0 < c := by rw [hcdef]; positivity
  have hc1 : c ≤ 1 := by rw [hcdef]; nlinarith only [hδ0, hδ1]
  have hβpos : 0 < β := by rw [hβdef]; positivity
  have hβ1 : 1 ≤ β := by
    rw [hβdef]
    exact Real.le_sqrt_of_sq_le (by nlinarith only [pow_nonneg hδ0.le 3])
  have hD : Real.arccos (-1 + c) = Real.pi - Real.arccos (1 - c) := by
    have h := Real.arccos_neg (1 - c)
    have h2 : -(1 - c) = -1 + c := by ring
    rw [h2] at h; exact h
  have ha_ge : 10 * δ ≤ Real.arccos (1 - c) := by
    have h2c : (0 : ℝ) ≤ 2 * c := by rw [hcdef]; positivity
    have hsq : Real.sqrt (2 * c) ^ 2 = 2 * c := Real.sq_sqrt h2c
    have hq2 : Real.sqrt (2 * c) ≤ Real.pi := by
      rw [Real.sqrt_le_left Real.pi_pos.le, hcdef]
      nlinarith only [Real.pi_gt_three, hδ0, hδ1]
    have hcosq : 1 - c ≤ Real.cos (Real.sqrt (2 * c)) := by
      have h := Real.one_sub_sq_div_two_le_cos (x := Real.sqrt (2 * c))
      rw [hsq] at h
      linarith only [h]
    have h1 : Real.sqrt (2 * c) ≤ Real.arccos (1 - c) := by
      have h := Real.arccos_le_arccos hcosq
      rwa [Real.arccos_cos (Real.sqrt_nonneg _) hq2] at h
    have h100 : 100 * δ ^ 2 ≤ 2 * c := by rw [hcdef]; nlinarith only []
    have h2 : 10 * δ ≤ Real.sqrt (2 * c) := by
      calc 10 * δ = Real.sqrt ((10 * δ) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ = Real.sqrt (100 * δ ^ 2) := by rw [show (10 * δ) ^ 2 = 100 * δ ^ 2 by ring]
        _ ≤ Real.sqrt (2 * c) := Real.sqrt_le_sqrt h100
    linarith only [h1, h2]
  have ha_le : Real.arccos (1 - c) ≤ Real.pi / 2 := by
    rw [Real.arccos_le_pi_div_two]; linarith only [hc1]
  have he_le : β - 1 ≤ δ ^ 3 / 2 := by
    rw [hβdef, sub_le_iff_le_add, Real.sqrt_le_left (by positivity : (0 : ℝ) ≤ δ ^ 3 / 2 + 1)]
    nlinarith only [pow_nonneg hδ0.le 3, sq_nonneg (δ ^ 3)]
  have hpi_lt : Real.pi * (δ ^ 3 / 2) < 10 * δ := by
    rw [← mul_div_assoc, div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
    linarith only [hπδ3, hδ0]
  have hπ2 : Real.pi ^ 2 ≤ 16 := by nlinarith only [Real.pi_lt_four, Real.pi_pos]
  refine ⟨hc0, ?_, ?_, ?_, hεnn, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcdef]; nlinarith only [hδ0, hδ1]
  · rw [hαdef]; positivity
  · rw [hαdef]; nlinarith only [hδ1]
  · -- 3c ≤ 1 - cos α
    have hαpi : |α| ≤ Real.pi := by
      rw [abs_of_nonneg (by rw [hαdef]; positivity), hαdef]
      nlinarith only [hδ1, Real.pi_gt_three]
    have hcos := Real.cos_le_one_sub_mul_cos_sq hαpi
    have h3 : 3 * c ≤ 2 / Real.pi ^ 2 * α ^ 2 := by
      rw [hcdef, hαdef, div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < Real.pi ^ 2)]
      nlinarith only [hπ2, hδ0, sq_nonneg δ]
    linarith only [hcos, h3]
  · -- 4 ε₁ π < c
    rw [hcdef, hεdef]
    have hδ2pos : 0 < δ ^ 2 := pow_pos hδ0 2
    nlinarith only [Real.pi_lt_four, hδ2pos]
  · -- arccos (-1 + c) < π / β
    have hb1 : 0 ≤ β - 1 := by linarith only [hβ1]
    have h4 : Real.pi * (β - 1) ≤ Real.pi * (δ ^ 3 / 2) :=
      mul_le_mul_of_nonneg_left he_le Real.pi_pos.le
    have h6 : Real.pi * (β - 1) / β ≤ Real.pi * (β - 1) := by
      rw [div_le_iff₀ hβpos]
      calc Real.pi * (β - 1) = Real.pi * (β - 1) * 1 := by ring
        _ ≤ Real.pi * (β - 1) * β := mul_le_mul_of_nonneg_left hβ1 (by positivity)
    have h1 : Real.pi * (β - 1) / β < Real.arccos (1 - c) := by
      linarith only [h6, h4, hpi_lt, ha_ge]
    have hkey : Real.pi * (β - 1) < Real.arccos (1 - c) * β :=
      (div_lt_iff₀ hβpos).mp h1
    rw [hD, lt_div_iff₀ hβpos]
    linarith only [hkey]
  · -- the pointwise trigonometric bound
    intro d hd0 hdD
    rw [max_le_iff]
    refine ⟨?_, hεnn⟩
    have hdpi : d ≤ Real.pi := le_trans hdD (Real.arccos_le_pi _)
    have hdD' : d ≤ Real.pi - Real.arccos (1 - c) := by rw [hD] at hdD; exact hdD
    set e : ℝ := β - 1 with hedef
    set t : ℝ := β * d with htdef
    set y : ℝ := β * Real.arccos (1 - c) - Real.pi * e with hydef
    have he0 : 0 ≤ e := by rw [hedef]; linarith only [hβ1]
    have ht0 : 0 < t := by rw [htdef]; positivity
    have harccos_nn : 0 ≤ Real.arccos (1 - c) := le_trans (by linarith only [hδ0]) ha_ge
    have h1a : 10 * δ ≤ β * Real.arccos (1 - c) := by
      calc 10 * δ ≤ Real.arccos (1 - c) := ha_ge
        _ = 1 * Real.arccos (1 - c) := by ring
        _ ≤ β * Real.arccos (1 - c) := mul_le_mul_of_nonneg_right hβ1 harccos_nn
    have hy_pos : 0 < y := by
      have h3 : Real.pi * (β - 1) ≤ Real.pi * (δ ^ 3 / 2) :=
        mul_le_mul_of_nonneg_left he_le Real.pi_pos.le
      rw [hydef, hedef]
      linarith only [h1a, h3, hpi_lt]
    have hβ2 : β ≤ 2 := by
      rw [hβdef, Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 2)]
      have h2 : δ ^ 2 ≤ 1 := by nlinarith only [hδ0, hδ1]
      have hδ3le : δ ^ 3 ≤ 1 := by
        calc δ ^ 3 = δ ^ 2 * δ := by ring
          _ ≤ 1 * 1 := mul_le_mul h2 (by linarith only [hδ1]) hδ0.le (by norm_num)
          _ = 1 := by ring
      nlinarith only [hδ3le]
    have hy_le : y ≤ Real.pi := by
      have h1 : β * Real.arccos (1 - c) ≤ β * (Real.pi / 2) :=
        mul_le_mul_of_nonneg_left ha_le hβpos.le
      have h2 : β * (Real.pi / 2) ≤ Real.pi := by nlinarith only [hβ2, Real.pi_pos]
      have h3 : 0 ≤ Real.pi * e := by positivity
      rw [hydef]; linarith only [h1, h2, h3]
    have hy8 : 8 * δ ≤ y := by
      have h4 : Real.pi * (δ ^ 3 / 2) ≤ 2 * δ := by
        rw [← mul_div_assoc, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
        linarith only [hπδ3]
      have h5 : Real.pi * e ≤ Real.pi * (δ ^ 3 / 2) :=
        mul_le_mul_of_nonneg_left (by rw [hedef]; exact he_le) Real.pi_pos.le
      rw [hydef, hedef]
      linarith only [h1a, h4, h5]
    have ht_le : t ≤ Real.pi - y := by
      have h1 : t ≤ β * (Real.pi - Real.arccos (1 - c)) := by
        rw [htdef]; exact mul_le_mul_of_nonneg_left hdD' hβpos.le
      have h2 : β * (Real.pi - Real.arccos (1 - c)) = Real.pi - y := by
        rw [hydef, hedef]; ring
      rw [h2] at h1; exact h1
    have ht_pi : t < Real.pi := by linarith only [ht_le, hy_pos]
    have hsinpos : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0 ht_pi
    have hbig : t ≤ (Real.pi ^ 2 / (2 * y)) * Real.sin t := by
      have hfac : (0 : ℝ) ≤ Real.pi ^ 2 / (2 * y) := by positivity
      rcases le_or_gt t (Real.pi / 2) with hcase | hcase
      · have hsint : (2 / Real.pi) * t ≤ Real.sin t := Real.mul_le_sin ht0.le hcase
        have h1 : (Real.pi ^ 2 / (2 * y)) * ((2 / Real.pi) * t)
            ≤ (Real.pi ^ 2 / (2 * y)) * Real.sin t := mul_le_mul_of_nonneg_left hsint hfac
        have h2 : t ≤ (Real.pi ^ 2 / (2 * y)) * ((2 / Real.pi) * t) := by
          rw [show (Real.pi ^ 2 / (2 * y)) * ((2 / Real.pi) * t) = (Real.pi / y) * t by
            field_simp]
          have h3 : (1 : ℝ) ≤ Real.pi / y := by
            rw [le_div_iff₀ hy_pos]; linarith only [hy_le]
          nlinarith only [h3, ht0]
        linarith only [h1, h2]
      · have hsint : (2 / Real.pi) * (Real.pi - t) ≤ Real.sin t := by
          have h := Real.mul_le_sin (x := Real.pi - t) (by linarith only [ht_pi])
            (by linarith only [hcase])
          rwa [Real.sin_pi_sub] at h
        have h1 : (Real.pi ^ 2 / (2 * y)) * ((2 / Real.pi) * (Real.pi - t))
            ≤ (Real.pi ^ 2 / (2 * y)) * Real.sin t := mul_le_mul_of_nonneg_left hsint hfac
        have h2 : t ≤ (Real.pi ^ 2 / (2 * y)) * ((2 / Real.pi) * (Real.pi - t)) := by
          rw [show (Real.pi ^ 2 / (2 * y)) * ((2 / Real.pi) * (Real.pi - t))
              = (Real.pi / y) * (Real.pi - t) by field_simp]
          have hypt : y ≤ Real.pi - t := by linarith only [ht_le]
          have h3 : Real.pi ≤ (Real.pi / y) * (Real.pi - t) := by
            rw [div_mul_eq_mul_div, le_div_iff₀ hy_pos]
            nlinarith only [hypt, Real.pi_pos]
          linarith only [ht_pi.le, h3]
        linarith only [h1, h2]
    have h2ed : 2 * e * d ≤ ε₁ * Real.sin t := by
      rw [hεdef]
      have h_te : (2 * e / β) * t = 2 * e * d := by
        rw [htdef, div_mul_eq_mul_div]
        rw [show (2 * e) * (β * d) = β * ((2 * e) * d) by ring, mul_div_cancel_left₀ _ hβpos.ne']
      rw [← h_te]
      have h1 : 2 * e / β ≤ 2 * e := by
        rw [div_le_iff₀ hβpos]; nlinarith only [hβ1, he0]
      have h2 : (2 * e / β) * t ≤ (2 * e) * t := mul_le_mul_of_nonneg_right h1 ht0.le
      have h3 : (2 * e) * t ≤ (2 * e) * (Real.pi ^ 2 / (2 * y) * Real.sin t) :=
        mul_le_mul_of_nonneg_left hbig (by positivity)
      have h4 : (2 * e) * (Real.pi ^ 2 / (2 * y) * Real.sin t) ≤ δ ^ 2 * Real.sin t := by
        rw [show (2 * e) * (Real.pi ^ 2 / (2 * y) * Real.sin t)
            = (2 * e * (Real.pi ^ 2 / (2 * y))) * Real.sin t by ring]
        apply mul_le_mul_of_nonneg_right _ hsinpos.le
        rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * y)]
        have heπ : 2 * e * Real.pi ^ 2 ≤ 16 * δ ^ 3 := by
          nlinarith only [he_le, hπ2, hδ0, pow_nonneg hδ0.le 3]
        have hyδ : 16 * δ ^ 3 ≤ δ ^ 2 * (2 * y) := by
          nlinarith only [hy8, hδ0, pow_nonneg hδ0.le 2]
        linarith only [heπ, hyδ]
      linarith only [h2, h3, h4]
    have hcot : Real.cot t * Real.sin t = Real.cos t := by
      rw [Real.cot_eq_cos_div_sin, div_mul_cancel₀ _ (ne_of_gt hsinpos)]
    have hident : (Real.cos d - Real.sin d * β * Real.cot t) * Real.sin t
        = Real.sin (e * d) - e * Real.sin d * Real.cos t := by
      calc (Real.cos d - Real.sin d * β * Real.cot t) * Real.sin t
          = Real.cos d * Real.sin t - Real.sin d * β * (Real.cot t * Real.sin t) := by ring
        _ = Real.cos d * Real.sin t - Real.sin d * β * Real.cos t := by rw [hcot]
        _ = Real.cos d * Real.sin t - Real.sin d * Real.cos t - e * Real.sin d * Real.cos t := by
              rw [hedef]; ring
        _ = Real.sin (t - d) - e * Real.sin d * Real.cos t := by rw [Real.sin_sub]; ring
        _ = Real.sin (e * d) - e * Real.sin d * Real.cos t := by
              rw [show t - d = e * d by rw [htdef, hedef]; ring]
    refine (mul_le_mul_iff_of_pos_right hsinpos).mp ?_
    rw [hident]
    have hsd : 0 ≤ Real.sin d := Real.sin_nonneg_of_nonneg_of_le_pi hd0.le hdpi
    have hsind : Real.sin d ≤ d := Real.sin_le hd0.le
    have hsed : Real.sin (e * d) ≤ e * d := Real.sin_le (by positivity)
    have hcos2 : -1 ≤ Real.cos t := Real.neg_one_le_cos t
    have hub : Real.sin (e * d) - e * Real.sin d * Real.cos t ≤ 2 * e * d := by
      nlinarith only [hsed, hsd, hsind, hcos2, he0, hd0, mul_nonneg he0 hsd]
    linarith only [hub, h2ed]
  · -- the final arithmetic
    have hsqrtc : Real.sqrt c = 10 * δ := by
      rw [hcdef, show 100 * δ ^ 2 = (10 * δ) ^ 2 by ring,
        Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 10 * δ)]
    have hApos : (0 : ℝ) < (n : ℝ) + 2 := by linarith only
    have hAδ : ((n : ℝ) + 2) * δ ≤ 1 / 10 ^ 6 := by
      have h := mul_le_mul_of_nonneg_left hδle hApos.le
      have h2 : ((n : ℝ) + 2) * (1 / (10 ^ 6 * ((n : ℝ) + 2))) = 1 / 10 ^ 6 := by
        field_simp
      rwa [h2] at h
    rw [hsqrtc, hεdef, hαdef]
    have hsum : δ ^ 2 * Real.pi + 1000 * δ + 10 * δ ≤ δ * 1014 := by
      nlinarith only [hδ0, hδ1, Real.pi_lt_four, Real.pi_pos, sq_nonneg δ]
    have hfin : (100 : ℝ) * ((n : ℝ) + 2) * (δ * 1014) < 1 := by
      have h := mul_le_mul_of_nonneg_left hAδ (by norm_num : (0 : ℝ) ≤ 100 * 1014)
      nlinarith only [h]
    nlinarith only [hsum, hfin, hApos, hδ0]

end Work.Diff.C
