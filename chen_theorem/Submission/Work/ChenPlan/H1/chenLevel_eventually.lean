import Mathlib
import Submission.Work.Chen.SwitchDefs

/-!
# The sift limit `chenSiftLimitTenth x = ⌊x^{1/10}⌋ + 1` grows like `x^{1/10}`

This file proves the elementary "level" estimates for the sift limit `M = x^{1/10}` used by the
Chen switch: `M^{49/10}` eventually dominates any constant, and is eventually trapped between `4`
and `√x / (log x)^B` for every fixed `B > 0`.  (In particular `M^{49/10} ≍ x^{49/100}` lies well
below `√x` up to a power of `log x`.)
-/

namespace Work.ChenPlan.H1

open Filter

/-- `chenSiftLimitTenth x = ⌊x^{1/10}⌋₊ + 1`. -/
private lemma chenSiftLimitTenth_def (x : ℕ) :
    Submission.chenSiftLimitTenth x = ⌊(x : ℝ) ^ ((1 : ℝ) / 10)⌋₊ + 1 := rfl

/-- `x^{1/10} < chenSiftLimitTenth x`, for every `x`. -/
private lemma rpow_ten_lt_chenSift (x : ℕ) :
    (x : ℝ) ^ ((1 : ℝ) / 10) < (Submission.chenSiftLimitTenth x : ℝ) := by
  have h := Nat.lt_floor_add_one ((x : ℝ) ^ ((1 : ℝ) / 10))
  rw [chenSiftLimitTenth_def]
  push_cast
  exact h

/-- `chenSiftLimitTenth x ≤ x^{1/10} + 1`. -/
private lemma chenSift_le_rpow_add_one (x : ℕ) :
    (Submission.chenSiftLimitTenth x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) + 1 := by
  have hy : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) := Real.rpow_nonneg (Nat.cast_nonneg x) _
  have h := Nat.floor_le hy
  rw [chenSiftLimitTenth_def]
  push_cast
  linarith

/-- `x^{49/100} ≤ (chenSiftLimitTenth x)^{49/10}`. -/
private lemma rpow_49_100_le_chenSift (x : ℕ) :
    (x : ℝ) ^ ((49 : ℝ) / 100)
      ≤ (Submission.chenSiftLimitTenth x : ℝ) ^ ((49 : ℝ) / 10) := by
  have hb : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) := Real.rpow_nonneg (Nat.cast_nonneg x) _
  have h := Real.rpow_le_rpow hb (le_of_lt (rpow_ten_lt_chenSift x))
    (by norm_num : (0 : ℝ) ≤ (49 : ℝ) / 10)
  calc (x : ℝ) ^ ((49 : ℝ) / 100)
      = ((x : ℝ) ^ ((1 : ℝ) / 10)) ^ ((49 : ℝ) / 10) := by
        rw [← Real.rpow_mul (Nat.cast_nonneg x)]
        norm_num
    _ ≤ (Submission.chenSiftLimitTenth x : ℝ) ^ ((49 : ℝ) / 10) := h

/-- `1 ≤ x^{1/10}` for `1 ≤ x`. -/
private lemma one_le_rpow_ten {x : ℕ} (hx : 1 ≤ x) :
    (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) := by
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hx1
    (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 10)
  rwa [Real.one_rpow] at h

/-- For `B > 0` and any constant `C ≥ 0`, eventually `C · (log x)^B ≤ x^{1/100}`. -/
private lemma eventually_const_mul_log_rpow_le {B : ℝ} (_hB : 0 < B) {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ x : ℕ in Filter.atTop,
      C * Real.log (x : ℝ) ^ B ≤ (x : ℝ) ^ ((1 : ℝ) / 100) := by
  have hlit : (fun x : ℝ => Real.log x ^ B)
      =o[Filter.atTop] (fun x : ℝ => x ^ ((1 : ℝ) / 100)) :=
    isLittleO_log_rpow_rpow_atTop B (by norm_num : (0 : ℝ) < (1 : ℝ) / 100)
  have hcpos : (0 : ℝ) < 1 / (C + 1) := by positivity
  have h := (Asymptotics.isLittleO_iff.mp hlit) hcpos
  have hnat : ∀ᶠ x : ℕ in Filter.atTop,
      ‖Real.log (x : ℝ) ^ B‖ ≤ (1 / (C + 1)) * ‖(x : ℝ) ^ ((1 : ℝ) / 100)‖ :=
    tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [hnat, Filter.eventually_ge_atTop 1] with x hx hx1
  have hx1' : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1') B),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg x) _)] at hx
  have hxnn : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 100) :=
    Real.rpow_nonneg (Nat.cast_nonneg x) _
  have hCc : C * (1 / (C + 1)) ≤ 1 := by
    rw [mul_one_div]
    exact (div_le_one (by linarith)).mpr (by linarith)
  calc C * Real.log (x : ℝ) ^ B
      ≤ C * ((1 / (C + 1)) * (x : ℝ) ^ ((1 : ℝ) / 100)) :=
        mul_le_mul_of_nonneg_left hx hC
    _ = (C * (1 / (C + 1))) * (x : ℝ) ^ ((1 : ℝ) / 100) := by ring
    _ ≤ 1 * (x : ℝ) ^ ((1 : ℝ) / 100) := mul_le_mul_of_nonneg_right hCc hxnn
    _ = (x : ℝ) ^ ((1 : ℝ) / 100) := by ring

theorem chenLevel_eventually (B : ℝ) (hB : 0 < B) :
    (∀ D₀ : ℝ, ∀ᶠ x : ℕ in Filter.atTop,
        D₀ ≤ (Submission.chenSiftLimitTenth x : ℝ) ^ ((49 : ℝ) / 10)) ∧
    (∀ᶠ x : ℕ in Filter.atTop,
      (1 : ℝ) < (Submission.chenSiftLimitTenth x : ℝ) ∧
      (4 : ℝ) ≤ (Submission.chenSiftLimitTenth x : ℝ) ^ ((49 : ℝ) / 10) ∧
      (Submission.chenSiftLimitTenth x : ℝ) ^ ((49 : ℝ) / 10)
        ≤ Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B) := by
  -- `(chenSiftLimitTenth x)^{49/10} → ∞`
  have hlow : Filter.Tendsto (fun x : ℕ => (x : ℝ) ^ ((49 : ℝ) / 100))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (49 : ℝ) / 100)).comp
      tendsto_natCast_atTop_atTop
  have htend : Filter.Tendsto
      (fun x : ℕ => (Submission.chenSiftLimitTenth x : ℝ) ^ ((49 : ℝ) / 10))
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono' Filter.atTop
      (Filter.Eventually.of_forall fun x => rpow_49_100_le_chenSift x) hlow
  refine ⟨fun D₀ => (Filter.tendsto_atTop.mp htend) D₀, ?_⟩
  have h2a : ∀ᶠ x : ℕ in Filter.atTop,
      (1 : ℝ) < (Submission.chenSiftLimitTenth x : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with x hx
    have h1 := one_le_rpow_ten hx
    linarith [rpow_ten_lt_chenSift x]
  have h2b : ∀ᶠ x : ℕ in Filter.atTop,
      (4 : ℝ) ≤ (Submission.chenSiftLimitTenth x : ℝ) ^ ((49 : ℝ) / 10) :=
    (Filter.tendsto_atTop.mp htend) 4
  have h2c : ∀ᶠ x : ℕ in Filter.atTop,
      (Submission.chenSiftLimitTenth x : ℝ) ^ ((49 : ℝ) / 10)
        ≤ Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B := by
    have hkey : ∀ᶠ x : ℕ in Filter.atTop,
        (2 : ℝ) ^ ((49 : ℝ) / 10) * Real.log (x : ℝ) ^ B
          ≤ (x : ℝ) ^ ((1 : ℝ) / 100) :=
      eventually_const_mul_log_rpow_le hB (by positivity)
    filter_upwards [hkey, Filter.eventually_ge_atTop 2] with x hkx hxge
    have hx1 : (1 : ℝ) < (x : ℝ) := by
      have : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hxge
      linarith
    have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
    have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
    have hLpos : 0 < Real.log (x : ℝ) ^ B := Real.rpow_pos_of_pos hlogpos B
    have hXpow : 0 < (x : ℝ) ^ ((49 : ℝ) / 100) := Real.rpow_pos_of_pos hxpos _
    have h10ge1 : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) := one_le_rpow_ten (by omega)
    -- step 1: `chenSiftLimitTenth x ≤ 2 x^{1/10}`
    have htx_le : (Submission.chenSiftLimitTenth x : ℝ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 10) := by
      linarith [chenSift_le_rpow_add_one x]
    -- step 2: raise to the power `49/10`
    have hstep := Real.rpow_le_rpow (Nat.cast_nonneg (Submission.chenSiftLimitTenth x)) htx_le
      (by norm_num : (0 : ℝ) ≤ (49 : ℝ) / 10)
    have hC : (2 * (x : ℝ) ^ ((1 : ℝ) / 10)) ^ ((49 : ℝ) / 10)
        = (2 : ℝ) ^ ((49 : ℝ) / 10) * (x : ℝ) ^ ((49 : ℝ) / 100) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
        (Real.rpow_nonneg (Nat.cast_nonneg x) _)]
      rw [show ((x : ℝ) ^ ((1 : ℝ) / 10)) ^ ((49 : ℝ) / 10)
            = (x : ℝ) ^ ((49 : ℝ) / 100) by
        rw [← Real.rpow_mul (Nat.cast_nonneg x)]
        norm_num]
    have hXsplit : (x : ℝ) ^ ((49 : ℝ) / 100) * (x : ℝ) ^ ((1 : ℝ) / 100)
        = (x : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add hxpos]
      norm_num
    have hquot : (2 : ℝ) ^ ((49 : ℝ) / 10) ≤ (x : ℝ) ^ ((1 : ℝ) / 100) / Real.log (x : ℝ) ^ B :=
      (le_div_iff₀ hLpos).mpr hkx
    calc (Submission.chenSiftLimitTenth x : ℝ) ^ ((49 : ℝ) / 10)
        ≤ (2 * (x : ℝ) ^ ((1 : ℝ) / 10)) ^ ((49 : ℝ) / 10) := hstep
      _ = (2 : ℝ) ^ ((49 : ℝ) / 10) * (x : ℝ) ^ ((49 : ℝ) / 100) := hC
      _ ≤ (x : ℝ) ^ ((49 : ℝ) / 100)
            * ((x : ℝ) ^ ((1 : ℝ) / 100) / Real.log (x : ℝ) ^ B) := by
          rw [mul_comm ((2 : ℝ) ^ ((49 : ℝ) / 10)) ((x : ℝ) ^ ((49 : ℝ) / 100))]
          exact mul_le_mul_of_nonneg_left hquot hXpow.le
      _ = ((x : ℝ) ^ ((49 : ℝ) / 100) * (x : ℝ) ^ ((1 : ℝ) / 100))
            / Real.log (x : ℝ) ^ B := by rw [mul_div_assoc]
      _ = Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ B := by
          rw [hXsplit, Real.sqrt_eq_rpow]
  filter_upwards [h2a, h2b, h2c] with x ha hb hc
  exact ⟨ha, hb, hc⟩

end Work.ChenPlan.H1
