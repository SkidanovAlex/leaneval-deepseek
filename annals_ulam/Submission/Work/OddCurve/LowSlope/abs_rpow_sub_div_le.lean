import Mathlib

/-!
# A Lipschitz-type bound for the map `x ↦ x ^ β` on a capped interval

This file proves the crude finite-difference estimate

`|(b ^ β - a ^ β) / h| ≤ 6 * c * β * (a ^ (β - 1) + (2c) ^ (2β - 2))`

for `a = c ^ 2 - s ^ 2`, `b = (c + h) ^ 2 - s ^ 2` with `0 < s < c`, `0 < h < c` and `β > 0`.

The two structural inputs are the Bernoulli/tangent inequalities for the power function:
if `0 < β ≤ 1` the function is concave and its graph on `[a, b]` lies below the tangent at the
*left* endpoint `a`, while for `β ≥ 1` it is convex and lies below the tangent at the *right*
endpoint `b`.  Both are instances of `(1 + s) ^ β ≤ 1 + β s` (resp. `≥`) for `s ≥ -1`.
-/

namespace Work.OddCurve.LowSlope

/-- Concave case (`0 < β ≤ 1`): the secant slope of `t ↦ t ^ β` on `[a, b]` is at most the
derivative at the left endpoint, i.e. `t ↦ t ^ β` lies below its tangent line at `a`. -/
lemma rpow_sub_le_mul_rpow_sub_one_left {β a b : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (ha : 0 < a) (hab : a ≤ b) :
    b ^ β - a ^ β ≤ β * (b - a) * a ^ (β - 1) := by
  have ha0 : 0 ≤ a := ha.le
  have hb0 : 0 ≤ b := ha0.trans hab
  have hs : -1 ≤ (b - a) / a := by
    rw [le_div_iff₀ ha]; linarith
  have hber : (1 + (b - a) / a) ^ β ≤ 1 + β * ((b - a) / a) :=
    rpow_one_add_le_one_add_mul_self hs hβ.le hβ1
  have h1 : 1 + (b - a) / a = b / a := by field_simp; ring
  rw [h1] at hber
  have haβpos : 0 < a ^ β := Real.rpow_pos_of_pos ha β
  have hmul := mul_le_mul_of_nonneg_right hber haβpos.le
  have hl : (b / a) ^ β * a ^ β = b ^ β := by
    rw [Real.div_rpow hb0 ha0, div_mul_cancel₀ _ haβpos.ne']
  have hr : β * ((b - a) / a) * a ^ β = β * (b - a) * a ^ (β - 1) := by
    rw [Real.rpow_sub_one ha.ne' β]
    field_simp
  rw [hl, add_mul, one_mul, hr] at hmul
  linarith

/-- Convex case (`1 ≤ β`): the secant slope of `t ↦ t ^ β` on `[a, b]` is at most the
derivative at the right endpoint, i.e. `t ↦ t ^ β` lies below its tangent line at `b`. -/
lemma rpow_sub_le_mul_rpow_sub_one_right {β a b : ℝ} (hβ : 0 < β) (hβ1 : 1 ≤ β)
    (ha : 0 < a) (hab : a ≤ b) :
    b ^ β - a ^ β ≤ β * (b - a) * b ^ (β - 1) := by
  have ha0 : 0 ≤ a := ha.le
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hb0 : 0 ≤ b := hb.le
  have hs : -1 ≤ (a - b) / b := by
    rw [le_div_iff₀ hb]; linarith
  have hber : 1 + β * ((a - b) / b) ≤ (1 + (a - b) / b) ^ β :=
    one_add_mul_self_le_rpow_one_add hs hβ1
  have h1 : 1 + (a - b) / b = a / b := by field_simp; ring
  rw [h1] at hber
  have hbβpos : 0 < b ^ β := Real.rpow_pos_of_pos hb β
  have hmul := mul_le_mul_of_nonneg_right hber hbβpos.le
  have hl : (a / b) ^ β * b ^ β = a ^ β := by
    rw [Real.div_rpow ha0 hb0, div_mul_cancel₀ _ hbβpos.ne']
  have hr : β * ((a - b) / b) * b ^ β = β * (a - b) * b ^ (β - 1) := by
    rw [Real.rpow_sub_one hb.ne' β]
    field_simp
  rw [hl, add_mul, one_mul, hr] at hmul
  linarith

/-- For `β > 0`, `c > 0`, `0 < h < c` and `0 < s < c`,
`|(((c + h) ^ 2 - s ^ 2) ^ β - (c ^ 2 - s ^ 2) ^ β) / h|` is bounded by
`6 * c * β * ((c ^ 2 - s ^ 2) ^ (β - 1) + (2 * c) ^ (2 * β - 2))`. -/
theorem abs_rpow_sub_div_le {β c h s : ℝ} (hβ : 0 < β) (hc : 0 < c) (hh : 0 < h) (hhc : h < c)
    (hs : s ∈ Set.Ioo (0 : ℝ) c) :
    |(((c + h) ^ 2 - s ^ 2) ^ β - (c ^ 2 - s ^ 2) ^ β) / h|
      ≤ 6 * c * β * ((c ^ 2 - s ^ 2) ^ (β - 1) + (2 * c) ^ (2 * β - 2)) := by
  obtain ⟨hs0, hsc⟩ := hs
  set A : ℝ := c ^ 2 - s ^ 2 with hA
  set B : ℝ := (c + h) ^ 2 - s ^ 2 with hB
  have hApos : 0 < A := by
    rw [hA]
    nlinarith [mul_pos (by linarith : (0 : ℝ) < c - s) (by linarith : (0 : ℝ) < c + s)]
  have hBpos : 0 < B := by
    rw [hB]
    nlinarith [mul_pos (by linarith : (0 : ℝ) < c + h - s) (by linarith : (0 : ℝ) < c + h + s)]
  have hAB : A ≤ B := by rw [hA, hB]; nlinarith [hh, hc]
  have hB2c : B ≤ (2 * c) ^ 2 := by
    rw [hB]; nlinarith [hhc, hc, sq_nonneg s, sq_nonneg (c + h), sq_nonneg (2 * c)]
  have hBA : B - A = h * (2 * c + h) := by rw [hA, hB]; ring
  have hAβ_nn : 0 ≤ A ^ (β - 1) := Real.rpow_nonneg hApos.le _
  have hD_nn : 0 ≤ (2 * c) ^ (2 * β - 2) := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 2 * c) _
  have hcβ_nn : 0 ≤ c * β := mul_nonneg hc.le hβ.le
  have hratio : (B - A) / h ≤ 3 * c := by
    rw [hBA, mul_div_cancel_left₀ _ hh.ne']; linarith
  have hnum : 0 ≤ B ^ β - A ^ β := by
    have := Real.rpow_le_rpow hApos.le hAB hβ.le
    linarith
  rw [abs_of_nonneg (div_nonneg hnum hh.le)]
  rcases le_total β 1 with hβ1 | hβ1
  · have hL := rpow_sub_le_mul_rpow_sub_one_left hβ hβ1 hApos hAB
    have heq : (β * (B - A) * A ^ (β - 1)) / h = β * ((B - A) / h) * A ^ (β - 1) := by
      field_simp
    have h1 : 0 ≤ c * β * A ^ (β - 1) := mul_nonneg hcβ_nn hAβ_nn
    have h2 : 0 ≤ c * β * (2 * c) ^ (2 * β - 2) := mul_nonneg hcβ_nn hD_nn
    calc (B ^ β - A ^ β) / h ≤ (β * (B - A) * A ^ (β - 1)) / h :=
          div_le_div_of_nonneg_right hL hh.le
      _ = β * ((B - A) / h) * A ^ (β - 1) := heq
      _ ≤ β * (3 * c) * A ^ (β - 1) := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left hratio hβ.le
          · exact hAβ_nn
      _ ≤ 6 * c * β * (A ^ (β - 1) + (2 * c) ^ (2 * β - 2)) := by
          nlinarith [h1, h2]
  · have hL := rpow_sub_le_mul_rpow_sub_one_right hβ hβ1 hApos hAB
    have hBpow : B ^ (β - 1) ≤ (2 * c) ^ (2 * β - 2) := by
      have h1 : B ^ (β - 1) ≤ ((2 * c) ^ 2) ^ (β - 1) :=
        Real.rpow_le_rpow hBpos.le hB2c (by linarith)
      have h2 : ((2 * c) ^ 2) ^ (β - 1) = (2 * c) ^ (2 * β - 2) := by
        rw [← Real.rpow_natCast_mul (by linarith : (0 : ℝ) ≤ 2 * c) 2 (β - 1)]
        congr 1
        ring
      linarith
    have heq : (β * (B - A) * B ^ (β - 1)) / h = β * ((B - A) / h) * B ^ (β - 1) := by
      field_simp
    have h1 : 0 ≤ c * β * A ^ (β - 1) := mul_nonneg hcβ_nn hAβ_nn
    have h2 : 0 ≤ c * β * (2 * c) ^ (2 * β - 2) := mul_nonneg hcβ_nn hD_nn
    calc (B ^ β - A ^ β) / h ≤ (β * (B - A) * B ^ (β - 1)) / h :=
          div_le_div_of_nonneg_right hL hh.le
      _ = β * ((B - A) / h) * B ^ (β - 1) := heq
      _ ≤ β * (3 * c) * B ^ (β - 1) := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left hratio hβ.le
          · exact Real.rpow_nonneg hBpos.le _
      _ ≤ β * (3 * c) * (2 * c) ^ (2 * β - 2) := by
          apply mul_le_mul_of_nonneg_left hBpow
          nlinarith [hc, hβ]
      _ ≤ 6 * c * β * (A ^ (β - 1) + (2 * c) ^ (2 * β - 2)) := by
          nlinarith [h1, h2]

end Work.OddCurve.LowSlope
