/-
# `Submission.Work.FITop4.Red5.tauOf_le_of_Nrange`

The range hypothesis of the round-5 contract (`N` between `x^{1/4+η}` and
`x^{1/2}(log x)^{-BmaxBig η}`) forces the truncation parameter
`τ = tauOf x Asave = (log x)^{2·Asave + 2^{20}}` to be at most `x^{η/3}`.

## The mathematics

Write `L = log x ≥ 1`, `B = BmaxBig η`, `C = Aprime Asave = 2·Asave + 2^{20}`.
The two `N`-bounds give

  `x^{1/4+η} < N < x^{1/2} · L^{-B}`,  hence  `L^B < x^{1/4-η}`.

Taking logarithms (`L > 0`):  `B · log L < (1/4 - η) · L`, i.e.

  `log L < (1/4 - η) · L / B`.

The single numerical input is the round-5 numerology of `B = bFun η + 2^31`
(numerics of (9.12) at `A = Asave`):

  `3 · C · (1/4 - η) ≤ η · B    (0 < η < 3/32)`,      (`BmaxBig_mul_ge_aux`)

i.e. `C·(1/4 - η)/B ≤ η/3`.  Multiplying the logarithmic inequality by `C > 0`
and using it,

  `C · log L < C · (1/4 - η) · L / B ≤ (η/3) · L`,

so `log (L^C) < log (x^{η/3})`, whence `L^C < x^{η/3}`.  Since
`tauOf x Asave = L^C`, this is the claim.

## The numerics of `BmaxBig_mul_ge_aux`

`C = 201048576`, so `3C(1/4-η) ≤ 3C/4 = 150786432 < 2^28`.

* `η ≥ 1/16`:  `η·B ≥ η·2^31 ≥ 2^27 = 134217728`, while
  `3C(1/4-η) ≤ 3C·(3/16) = 113089824`.
* `η < 1/16`:  with `u = η^{-1} > 16` the first term of `bFun η` gives
  `η·bFun η ≥ η·2^{u log u + 4} = 2^{u log u + 4}/u = 2^{u log u - 24}·2^{28}/u`,
  and `u ≤ 2^{u log u - 24}` (`self_le_two_rpow`: `log u ≥ 2.7`, `log 2 ≥ 1/2`),
  so `η·bFun η ≥ 2^28 > 3C(1/4-η)`.
-/
import Mathlib
import Submission.Work.FITop4.Red5.window_setup

set_option autoImplicit false

namespace Work.FITop4.Red5

open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary facts about `bFun` -/

/-- The first summand of `bFun`. -/
private lemma bFun_ge_term (η : ℝ) :
    (2 : ℝ) ^ (η⁻¹ * Real.log η⁻¹ + 4) ≤ Work.FITop4.bFun η := by
  unfold Work.FITop4.bFun
  have h1 : (0 : ℝ) < (2 : ℝ) ^ (η⁻¹ * Real.log η⁻¹ + 1) :=
    Real.rpow_pos_of_pos (by norm_num) _
  linarith

private lemma bFun_nonneg' (η : ℝ) : (0 : ℝ) ≤ Work.FITop4.bFun η :=
  le_trans (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)) (bFun_ge_term η)

private lemma BmaxBig_pos' (η : ℝ) : 0 < Work.FITop4.BmaxBig η := by
  unfold Work.FITop4.BmaxBig
  have h1 : (0 : ℝ) ≤ Work.FITop4.bFun η := bFun_nonneg' η
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (31 : ℕ) := by norm_num
  linarith

private lemma rpow_neg_mul_self (L B : ℝ) (hL : 0 < L) : L ^ (-B) * L ^ B = 1 := by
  rw [← Real.rpow_add hL, show -B + B = (0 : ℝ) by ring, Real.rpow_zero]

/-! ## The numerical input -/

/-- `u ≤ 2^{u log u - 24}` for `u ≥ 16` (all the room we need: `log u ≥ 2.7`). -/
private lemma self_le_two_rpow (u : ℝ) (hu : 16 ≤ u) : u ≤ 2 ^ (u * Real.log u - 24) := by
  have hu0 : 0 < u := by linarith
  rw [← Real.logb_le_iff_le_rpow (b := 2) (by norm_num) hu0]
  have hlogu : (2.7 : ℝ) ≤ Real.log u := by
    have h1 : Real.log (16 : ℝ) ≤ Real.log u := Real.log_le_log (by norm_num) hu
    have h2 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_gt_d9]
  have hlog2pos : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  rw [← Real.log_div_log]
  rw [div_eq_mul_inv]
  have hinv : (Real.log 2)⁻¹ ≤ 2 := by
    rw [inv_le_iff_one_le_mul₀ hlog2pos]
    linarith [Real.log_two_gt_d9]
  have hmul : Real.log u * (Real.log 2)⁻¹ ≤ Real.log u * 2 :=
    mul_le_mul_of_nonneg_left hinv (by linarith)
  have hkey : Real.log u * 2 ≤ u * Real.log u - 24 := by
    have h1 : (14 : ℝ) ≤ u - 2 := by linarith
    have h3 : 14 * (2.7 : ℝ) ≤ (u - 2) * Real.log u :=
      mul_le_mul h1 hlogu (by norm_num) (by linarith)
    nlinarith [h3]
  linarith

/-- **The round-5 numerology**: `η · BmaxBig η` dominates `3 · Aprime Asave · (1/4 - η)`. -/
private lemma BmaxBig_mul_ge_aux (η : ℝ) (hη0 : 0 < η) (hη1 : η < 3 / 32) :
    3 * Work.FITop4.Aprime Work.FITop4.Asave * (1 / 4 - η) ≤ η * Work.FITop4.BmaxBig η := by
  have hC : Work.FITop4.Aprime Work.FITop4.Asave = 201048576 := by
    unfold Work.FITop4.Aprime Work.FITop4.Asave; norm_num
  have hb0 : (0 : ℝ) ≤ Work.FITop4.bFun η := bFun_nonneg' η
  rcases lt_or_ge η (1 / 16 : ℝ) with hcase | hcase
  · -- small `η`: `bFun` alone suffices
    have hu : 16 ≤ η⁻¹ := by
      have h := one_div_lt_one_div_of_lt hη0 hcase
      have h1 : (1 : ℝ) / (1 / 16) = 16 := by norm_num
      have h2 : (1 : ℝ) / η = η⁻¹ := by rw [one_div]
      rw [h1, h2] at h
      exact le_of_lt h
    have hu0 : 0 < η⁻¹ := inv_pos.mpr hη0
    have hA : (2 : ℝ) ^ (η⁻¹ * Real.log η⁻¹ + 4)
        = 2 ^ (η⁻¹ * Real.log η⁻¹ - 24) * 2 ^ (28 : ℝ) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      ring_nf
    have h1 : η⁻¹ * (2 : ℝ) ^ (28 : ℝ) ≤ (2 : ℝ) ^ (η⁻¹ * Real.log η⁻¹ + 4) := by
      rw [hA]
      exact mul_le_mul_of_nonneg_right (self_le_two_rpow η⁻¹ hu) (by positivity)
    have h2 : (2 : ℝ) ^ 28 ≤ (2 : ℝ) ^ (η⁻¹ * Real.log η⁻¹ + 4) / η⁻¹ := by
      rw [le_div_iff₀ hu0]
      have h28 : (2 : ℝ) ^ 28 ≤ 2 ^ (28 : ℝ) := le_of_eq (Real.rpow_natCast 2 28).symm
      calc (2 : ℝ) ^ 28 * η⁻¹ ≤ 2 ^ (28 : ℝ) * η⁻¹ :=
            mul_le_mul_of_nonneg_right h28 (le_of_lt hu0)
        _ = η⁻¹ * 2 ^ (28 : ℝ) := mul_comm _ _
        _ ≤ _ := h1
    have h3 : η * (2 : ℝ) ^ (η⁻¹ * Real.log η⁻¹ + 4)
        = (2 : ℝ) ^ (η⁻¹ * Real.log η⁻¹ + 4) / η⁻¹ := by
      rw [div_eq_mul_inv, inv_inv, mul_comm]
    have h4 : 3 * Work.FITop4.Aprime Work.FITop4.Asave * (1 / 4 - η) ≤ (2 : ℝ) ^ 28 := by
      rw [hC]; nlinarith [hη0]
    have hb : η * (2 : ℝ) ^ (η⁻¹ * Real.log η⁻¹ + 4) ≤ η * Work.FITop4.bFun η :=
      mul_le_mul_of_nonneg_left (bFun_ge_term η) (le_of_lt hη0)
    unfold Work.FITop4.BmaxBig
    linarith
  · -- large `η`: the `2^31` summand alone suffices
    have hR : 3 * Work.FITop4.Aprime Work.FITop4.Asave * (1 / 4 - η) ≤ 113089824 := by
      rw [hC]; nlinarith [hcase]
    have h1 : (2 : ℝ) ^ 31 ≤ Work.FITop4.bFun η + (2 : ℝ) ^ 31 := le_add_of_nonneg_left hb0
    have h2 : (1 / 16 : ℝ) * (2 : ℝ) ^ 31 ≤ η * (Work.FITop4.bFun η + (2 : ℝ) ^ 31) :=
      mul_le_mul hcase h1 (by norm_num) (le_of_lt hη0)
    have h3 : (1 / 16 : ℝ) * (2 : ℝ) ^ 31 = 134217728 := by norm_num
    unfold Work.FITop4.BmaxBig
    linarith

/-! ## The bound on `tauOf` -/

theorem tauOf_le_of_Nrange (x : ℕ) (N η : ℝ)
    (hlog : (1 : ℝ) ≤ Real.log (x : ℝ))
    (hN : (1 : ℝ) ≤ N)
    (hNlo : (x : ℝ) ^ ((1 : ℝ) / 4 + η) < N)
    (hNhi : N < (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(Work.FITop4.BmaxBig η)))
    (hη0 : 0 < η) (hη1 : η < 3 / 32) :
    Work.FITop4.tauOf x Work.FITop4.Asave ≤ (x : ℝ) ^ (η / 3) := by
  have hx0 : (0 : ℝ) < (x : ℝ) := by
    have hxne : x ≠ 0 := by
      rintro rfl
      norm_num at hlog
    exact_mod_cast Nat.pos_of_ne_zero hxne
  set L := Real.log (x : ℝ) with hLdef
  have hLpos : 0 < L := by rw [hLdef]; linarith
  set B := Work.FITop4.BmaxBig η with hBdef
  have hBpos : 0 < B := by rw [hBdef]; exact BmaxBig_pos' η
  set C := Work.FITop4.Aprime Work.FITop4.Asave with hCdef
  have hCpos : 0 < C := by
    rw [hCdef]; unfold Work.FITop4.Aprime Work.FITop4.Asave; norm_num
  -- Step 1: `L^B < x^{1/4-η}`
  have hs1 : (x : ℝ) ^ ((1 : ℝ) / 4 + η) < (x : ℝ) ^ ((1 : ℝ) / 2) * L ^ (-B) := by
    rw [hLdef, hBdef]; exact lt_trans hNlo hNhi
  have hs2 : (x : ℝ) ^ ((1 : ℝ) / 4 + η) * L ^ B < (x : ℝ) ^ ((1 : ℝ) / 2) := by
    have hyB : 0 < L ^ B := Real.rpow_pos_of_pos hLpos B
    have h := mul_lt_mul_of_pos_right hs1 hyB
    rwa [mul_assoc, rpow_neg_mul_self L B hLpos, mul_one] at h
  have hs3 : (x : ℝ) ^ ((1 : ℝ) / 2)
      = (x : ℝ) ^ ((1 : ℝ) / 4 + η) * (x : ℝ) ^ ((1 : ℝ) / 4 - η) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have hs4 : L ^ B < (x : ℝ) ^ ((1 : ℝ) / 4 - η) := by
    rw [hs3] at hs2
    exact (mul_lt_mul_iff_of_pos_left (Real.rpow_pos_of_pos hx0 _)).mp hs2
  -- Step 2: `B log L < (1/4-η) L`
  have hs5 : B * Real.log L < ((1 : ℝ) / 4 - η) * L := by
    have h := Real.log_lt_log (Real.rpow_pos_of_pos hLpos B) hs4
    rw [Real.log_rpow hLpos B, Real.log_rpow hx0 ((1 : ℝ) / 4 - η), ← hLdef] at h
    exact h
  have hs6 : Real.log L < ((1 : ℝ) / 4 - η) * L / B := by
    rw [mul_comm B (Real.log L)] at hs5
    rwa [lt_div_iff₀ hBpos]
  -- Step 3: multiply by `C` and use the numerology
  have hs7 : C * Real.log L < C * (((1 : ℝ) / 4 - η) * L / B) :=
    mul_lt_mul_of_pos_left hs6 hCpos
  have hs8 : C * (((1 : ℝ) / 4 - η) * L / B) ≤ (η / 3) * L := by
    have hkey : 3 * C * (1 / 4 - η) ≤ η * B := by
      rw [hCdef, hBdef]; exact BmaxBig_mul_ge_aux η hη0 hη1
    have h9a : C * (1 / 4 - η) / B ≤ η / 3 := by
      rw [div_le_iff₀ hBpos]
      nlinarith [hkey]
    have heq : C * (((1 : ℝ) / 4 - η) * L / B) = (C * (1 / 4 - η) / B) * L := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right h9a (le_of_lt hLpos)
  have hs9 : C * Real.log L < (η / 3) * L := lt_of_lt_of_le hs7 hs8
  -- Step 4: exponentiate back
  have hfin : L ^ C < (x : ℝ) ^ (η / 3) := by
    rw [← Real.log_lt_log_iff (Real.rpow_pos_of_pos hLpos C) (Real.rpow_pos_of_pos hx0 (η / 3))]
    rw [Real.log_rpow hLpos C, Real.log_rpow hx0 (η / 3), ← hLdef]
    exact hs9
  calc Work.FITop4.tauOf x Work.FITop4.Asave = L ^ C := rfl
    _ ≤ (x : ℝ) ^ (η / 3) := le_of_lt hfin

end

end Work.FITop4.Red5
