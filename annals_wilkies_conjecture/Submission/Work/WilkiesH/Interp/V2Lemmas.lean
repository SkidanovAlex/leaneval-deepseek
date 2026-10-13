import Mathlib
import Submission.Work.WilkiesH.Interp.V2Params

/-!
# Area I (`v2` route) — the arithmetic core

Elementary lemmas about the explicit parameters of `V2Params`, all proved by hand:
positivity of `liou` and `ε`, two "cubic" comparison lemmas `cmY_A`, `cmY_B`, the two
inequalities `ineqA`, `ineqB` reducing the parameters to the master inequality, and the
abstract Siegel cardinality argument `cardineq_abstract`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical

namespace Work.WilkiesH.Interp

open WilkiesConjecture

lemma monoCount_pos (n d : ℕ) : 0 < Work.WilkiesH.monoCount n d :=
  Fintype.card_pos_iff.mpr ⟨⟨fun _ => 0, by simp⟩⟩

lemma liou_pos' (μ d Q g H : ℕ) (hQ : 1 ≤ Q) (hH : 1 ≤ H) : 0 < liou μ d Q g H := by
  have h1 : (0 : ℝ) < ((Work.WilkiesH.monoCount (μ + 1) d : ℕ) : ℝ) := by
    exact_mod_cast (monoCount_pos (μ + 1) d)
  have h2 : (0 : ℝ) < ((Q : ℕ) : ℝ) := by exact_mod_cast hQ
  have h3 : (0 : ℝ) < ((H : ℕ) : ℝ) := by exact_mod_cast hH
  have h4 : (0 : ℝ) < ((H : ℕ) : ℝ) ^ (((μ + 1) + 1) * d * g) := pow_pos h3 _
  have h5 : (0 : ℝ) < ((Work.WilkiesH.monoCount (μ + 1) d : ℕ) : ℝ) * ((Q : ℕ) : ℝ) *
      ((H : ℕ) : ℝ) ^ (((μ + 1) + 1) * d * g) := mul_pos (mul_pos h1 h2) h4
  rw [liou, one_div]
  exact inv_pos.mpr (pow_pos h5 g)

lemma one_le_mul3 {a b c : ℝ} (h1 : 1 ≤ a) (h2 : 1 ≤ b) (h3 : 1 ≤ c) : 1 ≤ a * b * c :=
  one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2) h3

lemma eight_le_four_mul {a b c d : ℝ} (h1 : 1 ≤ a) (h2 : 2 ≤ b) (h3 : 1 ≤ c) (h4 : 1 ≤ d) :
    (8 : ℝ) ≤ 4 * a * b * c * d := by
  have h12 : 2 ≤ a * b := by nlinarith [h1, h2]
  have h123 : 2 ≤ a * b * c := by nlinarith [h12, h3]
  have h1234 : 2 ≤ a * b * c * d := by nlinarith [h123, h4]
  linarith

lemma liou_le_one (μ d Q g H : ℕ) (hQ : 1 ≤ Q) (hH : 1 ≤ H) : liou μ d Q g H ≤ 1 := by
  have h1 : (1 : ℝ) ≤ ((Work.WilkiesH.monoCount (μ + 1) d : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (ne_of_gt (monoCount_pos (μ + 1) d)))
  have h2 : (1 : ℝ) ≤ ((Q : ℕ) : ℝ) := by exact_mod_cast hQ
  have h3 : (1 : ℝ) ≤ ((H : ℕ) : ℝ) := by exact_mod_cast hH
  have h4 : (1 : ℝ) ≤ ((H : ℕ) : ℝ) ^ (((μ + 1) + 1) * d * g) := one_le_pow₀ h3
  have h5 : (1 : ℝ) ≤ ((Work.WilkiesH.monoCount (μ + 1) d : ℕ) : ℝ) * ((Q : ℕ) : ℝ) *
      ((H : ℕ) : ℝ) ^ (((μ + 1) + 1) * d * g) := one_le_mul3 h1 h2 h4
  have h6 : (1 : ℝ) ≤ (((Work.WilkiesH.monoCount (μ + 1) d : ℕ) : ℝ) * ((Q : ℕ) : ℝ) *
      ((H : ℕ) : ℝ) ^ (((μ + 1) + 1) * d * g)) ^ g := one_le_pow₀ h5
  rw [liou, one_div]
  exact inv_le_one_of_one_le₀ h6

lemma epsV_pos (μ g H : ℕ) (hH : 1 ≤ H) : 0 < epsV μ g H := by
  have hliou := liou_pos' μ (dX μ g H) (QX μ g H) g H (one_le_QV μ g H) hH
  have hN : (0 : ℝ) < ((N1X μ g H : ℕ) : ℝ) := by exact_mod_cast one_le_N1V μ g H
  have hQ : (0 : ℝ) < ((QX μ g H : ℕ) : ℝ) := by exact_mod_cast one_le_QV μ g H
  have hd : (0 : ℝ) < ((dX μ g H : ℕ) : ℝ) := by exact_mod_cast one_le_dV μ g (bX μ g H)
  have hm : (0 : ℝ) < ((μ : ℝ) + 1) := by positivity
  have hden : (0 : ℝ) < 4 * ((N1X μ g H : ℕ) : ℝ) * ((QX μ g H : ℕ) : ℝ) *
      ((dX μ g H : ℕ) : ℝ) * ((μ : ℝ) + 1) := by
    have h4 : (0 : ℝ) < 4 := by norm_num
    exact mul_pos (mul_pos (mul_pos (mul_pos h4 hN) hQ) hd) hm
  have hgoal : epsV μ g H = liou μ (dX μ g H) (QX μ g H) g H /
      (4 * ((N1X μ g H : ℕ) : ℝ) * ((QX μ g H : ℕ) : ℝ) * ((dX μ g H : ℕ) : ℝ) *
        ((μ : ℝ) + 1)) := by
    simp only [epsV, dX, bX, QX, N1X]
  rw [hgoal]
  exact div_pos hliou hden

lemma epsV_lt_one (μ g H : ℕ) (hH : 1 ≤ H) : epsV μ g H < 1 := by
  have hQ : 1 ≤ QX μ g H := one_le_QV μ g H
  have hliou := liou_le_one μ (dX μ g H) (QX μ g H) g H hQ hH
  have hliou0 : 0 ≤ liou μ (dX μ g H) (QX μ g H) g H :=
    le_of_lt (liou_pos' μ (dX μ g H) (QX μ g H) g H hQ hH)
  have hN : (1 : ℝ) ≤ ((N1X μ g H : ℕ) : ℝ) := by exact_mod_cast one_le_N1V μ g H
  have hQ2 : (2 : ℝ) ≤ ((QX μ g H : ℕ) : ℝ) := by
    have h : (2 : ℕ) ≤ QX μ g H := by simp only [QX, QV]; omega
    exact_mod_cast h
  have hd : (1 : ℝ) ≤ ((dX μ g H : ℕ) : ℝ) := by exact_mod_cast one_le_dV μ g (bX μ g H)
  have hm : (1 : ℝ) ≤ ((μ : ℝ) + 1) := by
    have : (0 : ℝ) ≤ (μ : ℝ) := Nat.cast_nonneg μ
    linarith
  have hden : (8 : ℝ) ≤ 4 * ((N1X μ g H : ℕ) : ℝ) * ((QX μ g H : ℕ) : ℝ) *
      ((dX μ g H : ℕ) : ℝ) * ((μ : ℝ) + 1) := eight_le_four_mul hN hQ2 hd hm
  have hdenpos : (0 : ℝ) < 4 * ((N1X μ g H : ℕ) : ℝ) * ((QX μ g H : ℕ) : ℝ) *
      ((dX μ g H : ℕ) : ℝ) * ((μ : ℝ) + 1) := by linarith
  have hgoal : epsV μ g H = liou μ (dX μ g H) (QX μ g H) g H /
      (4 * ((N1X μ g H : ℕ) : ℝ) * ((QX μ g H : ℕ) : ℝ) * ((dX μ g H : ℕ) : ℝ) *
        ((μ : ℝ) + 1)) := by
    simp only [epsV, dX, bX, QX, N1X]
  have hstep : epsV μ g H ≤ liou μ (dX μ g H) (QX μ g H) g H / 8 := by
    rw [hgoal]
    exact div_le_div_of_nonneg_left hliou0 (by norm_num) hden
  linarith

lemma cmY_A (μ : ℕ) {g d N1 : ℝ} (hd : 0 ≤ d) (hN1 : 1 ≤ N1) (hg : 0 ≤ g) :
    CM μ * (g + 1) * ((d + 1) * (Real.log (d + 1) + 1) + Real.log N1 + 1) ≥
      Real.log 4 + (1 / 2) * Real.log N1 + (Real.sqrt (μ : ℝ)) ^ 3 * d +
        g * (2 * Real.log N1 + Real.log 16) := by
  have hlogd : 0 ≤ Real.log (d + 1) := Real.log_nonneg (by linarith)
  have hlogN : 0 ≤ Real.log N1 := Real.log_nonneg hN1
  set Y : ℝ := (d + 1) * (Real.log (d + 1) + 1) + Real.log N1 + 1 with hY
  have hY1 : 1 ≤ Y := by rw [hY]; nlinarith
  have hYd : d ≤ Y := by rw [hY]; nlinarith
  have hYN : Real.log N1 ≤ Y := by rw [hY]; nlinarith
  have hg1 : 1 ≤ g + 1 := by linarith
  have hsqrt : (Real.sqrt (μ : ℝ)) ^ 3 ≤ ((μ : ℝ) + 2) ^ 2 := by
    rcases Nat.eq_zero_or_pos μ with h | h
    · subst h; norm_num
    · have h1 : (1 : ℝ) ≤ (μ : ℝ) := by exact_mod_cast h
      have hs : Real.sqrt (μ : ℝ) ≤ (μ : ℝ) := by
        rw [Real.sqrt_le_iff]
        exact ⟨by linarith, by nlinarith⟩
      have h3 : Real.sqrt (μ : ℝ) ^ 3 = (Real.sqrt (μ : ℝ)) ^ 2 * Real.sqrt (μ : ℝ) := by ring
      rw [h3, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ (μ : ℝ))]
      nlinarith
  have hCM : ((μ : ℝ) + 2) ^ 2 + 30 ≤ CM μ := by
    simp only [CM]; nlinarith [sq_nonneg ((μ : ℝ) + 2)]
  have hlog4 : Real.log 4 ≤ 4 := Real.log_le_self (by norm_num)
  have hlog16 : Real.log 16 ≤ 16 := Real.log_le_self (by norm_num)
  have hYY : 1 ≤ (g + 1) * Y := by nlinarith
  nlinarith [hY1, hYd, hYN, hg1, hsqrt, hCM, hlog4, hlog16, hlogN, hYY,
    mul_nonneg hg hlogN, mul_nonneg hg (le_of_lt (by linarith : (0:ℝ) < Y)),
    mul_nonneg (le_of_lt (by linarith : (0:ℝ) < Y)) (le_of_lt (by linarith : (0:ℝ) < Y))]

lemma cmY_B (μ : ℕ) {g d N1 : ℝ} (hd : 0 ≤ d) (hN1 : 1 ≤ N1) (hg : 0 ≤ g) :
    CM μ * (g + 1) * ((d + 1) * (Real.log (d + 1) + 1) + Real.log N1 + 1) ≥
      Real.log 4 + Real.log 16 + 2 * Real.log N1 + (d + 2) * Real.log (d + 1) +
        g * (2 * Real.log N1 + Real.log 16) := by
  have hlogd : 0 ≤ Real.log (d + 1) := Real.log_nonneg (by linarith)
  have hlogN : 0 ≤ Real.log N1 := Real.log_nonneg hN1
  set Y : ℝ := (d + 1) * (Real.log (d + 1) + 1) + Real.log N1 + 1 with hY
  have hY1 : 1 ≤ Y := by rw [hY]; nlinarith
  have hYd : d ≤ Y := by rw [hY]; nlinarith
  have hYN : Real.log N1 ≤ Y := by rw [hY]; nlinarith
  have hYdlog : (d + 2) * Real.log (d + 1) ≤ 2 * Y := by rw [hY]; nlinarith
  have hg1 : 1 ≤ g + 1 := by linarith
  have hCM : 100 ≤ CM μ := by simp only [CM]; nlinarith [sq_nonneg ((μ : ℝ) + 2)]
  have hlog4 : Real.log 4 ≤ 4 := Real.log_le_self (by norm_num)
  have hlog16 : Real.log 16 ≤ 16 := Real.log_le_self (by norm_num)
  have hYY : 1 ≤ (g + 1) * Y := by nlinarith
  nlinarith [hY1, hYd, hYN, hYdlog, hg1, hCM, hlog4, hlog16, hlogN, hYY,
    mul_nonneg hg hlogN, mul_nonneg hg (le_of_lt (by linarith : (0:ℝ) < Y))]

lemma ineqA (μ g H : ℕ) (hH : 1 ≤ H) (hlam : 8 * g + 8 ≤ lamX μ g H)
    (hsharp : Real.log ((QX μ g H : ℕ) : ℝ) ≤
      Real.log 16 + Real.log ((N1X μ g H : ℕ) : ℝ) + ((bX μ g H : ℕ) : ℝ) * Real.log (Kr μ) /
        (8 * (g : ℝ) + 8))
    (hM : (1 / 4) * ((bX μ g H : ℕ) : ℝ) * Real.log (Kr μ) >
      CM μ * ((g : ℝ) + 1) *
          ((((dX μ g H : ℕ) : ℝ) + 1) * (Real.log (((dX μ g H : ℕ) : ℝ) + 1) + 1) +
            Real.log ((N1X μ g H : ℕ) : ℝ) + 1) +
        (((μ : ℝ) + 2) * ((dX μ g H : ℕ) : ℝ) * (g : ℝ) ^ 2 * Real.log (H : ℝ))) :
    ((bX μ g H : ℕ) : ℝ) * Real.log (Kr μ) >
      Real.log 4 + (1 / 2) * Real.log ((N1X μ g H : ℕ) : ℝ) +
        (Real.sqrt (μ : ℝ)) ^ 3 * ((dX μ g H : ℕ) : ℝ) +
        (g : ℝ) * Real.log (((N1X μ g H : ℕ) : ℝ) * ((QX μ g H : ℕ) : ℝ)) +
        ((μ : ℝ) + 2) * ((dX μ g H : ℕ) : ℝ) * (g : ℝ) ^ 2 * Real.log (H : ℝ) := by
  have hN1 : (1 : ℝ) ≤ ((N1X μ g H : ℕ) : ℝ) := by exact_mod_cast one_le_N1V μ g H
  have hN1pos : (0 : ℝ) < ((N1X μ g H : ℕ) : ℝ) := by linarith
  have hQpos : (0 : ℝ) < ((QX μ g H : ℕ) : ℝ) := by exact_mod_cast one_le_QV μ g H
  have hd0 : (0 : ℝ) ≤ ((dX μ g H : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le _
  have hg0 : (0 : ℝ) ≤ (g : ℝ) := by exact_mod_cast Nat.zero_le g
  have hb0 : (0 : ℝ) ≤ ((bX μ g H : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le _
  have hlogK : 0 ≤ Real.log (Kr μ) := Real.log_nonneg (by
    simp only [Kr]; exact_mod_cast (le_of_lt (one_lt_KK μ)))
  have hden : (0 : ℝ) < 8 * (g : ℝ) + 8 := by linarith [hg0]
  have hlogNQ : Real.log (((N1X μ g H : ℕ) : ℝ) * ((QX μ g H : ℕ) : ℝ)) =
      Real.log ((N1X μ g H : ℕ) : ℝ) + Real.log ((QX μ g H : ℕ) : ℝ) :=
    Real.log_mul (ne_of_gt hN1pos) (ne_of_gt hQpos)
  have hgQ : (g : ℝ) * Real.log ((QX μ g H : ℕ) : ℝ) ≤
      (g : ℝ) * (Real.log 16 + Real.log ((N1X μ g H : ℕ) : ℝ) +
        ((bX μ g H : ℕ) : ℝ) * Real.log (Kr μ) / (8 * (g : ℝ) + 8)) :=
    mul_le_mul_of_nonneg_left hsharp hg0
  have hg3 : (g : ℝ) * (((bX μ g H : ℕ) : ℝ) * Real.log (Kr μ) / (8 * (g : ℝ) + 8)) ≤
      ((bX μ g H : ℕ) : ℝ) * Real.log (Kr μ) / 8 := by
    have hX : (0 : ℝ) ≤ ((bX μ g H : ℕ) : ℝ) * Real.log (Kr μ) := mul_nonneg hb0 hlogK
    rw [← mul_div_assoc, div_le_iff₀ hden]
    nlinarith [hX, hg0]
  have hRNQ : (g : ℝ) * Real.log (((N1X μ g H : ℕ) : ℝ) * ((QX μ g H : ℕ) : ℝ)) ≤
      (g : ℝ) * (2 * Real.log ((N1X μ g H : ℕ) : ℝ) + Real.log 16) +
        ((bX μ g H : ℕ) : ℝ) * Real.log (Kr μ) / 8 := by
    rw [hlogNQ]
    nlinarith [hgQ, hg3]
  have hstar := cmY_A μ hd0 hN1 hg0
  have h78 : (1 / 4) * ((bX μ g H : ℕ) : ℝ) * Real.log (Kr μ) >
      Real.log 4 + (1 / 2) * Real.log ((N1X μ g H : ℕ) : ℝ) +
        (Real.sqrt (μ : ℝ)) ^ 3 * ((dX μ g H : ℕ) : ℝ) +
        (g : ℝ) * (2 * Real.log ((N1X μ g H : ℕ) : ℝ) + Real.log 16) +
        ((μ : ℝ) + 2) * ((dX μ g H : ℕ) : ℝ) * (g : ℝ) ^ 2 * Real.log (H : ℝ) := by
    linarith [hM, hstar]
  have hbL : (0 : ℝ) ≤ ((bX μ g H : ℕ) : ℝ) * Real.log (Kr μ) := mul_nonneg hb0 hlogK
  linarith [hRNQ, h78, hbL]

lemma ineqB (μ g H : ℕ) (hH : 1 ≤ H)
    (hsharp : Real.log ((QX μ g H : ℕ) : ℝ) ≤
      Real.log 16 + Real.log ((N1X μ g H : ℕ) : ℝ) + ((bX μ g H : ℕ) : ℝ) * Real.log (Kr μ) /
        (8 * (g : ℝ) + 8))
    (hM : (1 / 4) * ((bX μ g H : ℕ) : ℝ) * Real.log (Kr μ) >
      CM μ * ((g : ℝ) + 1) *
          ((((dX μ g H : ℕ) : ℝ) + 1) * (Real.log (((dX μ g H : ℕ) : ℝ) + 1) + 1) +
            Real.log ((N1X μ g H : ℕ) : ℝ) + 1) +
        (((μ : ℝ) + 2) * ((dX μ g H : ℕ) : ℝ) * (g : ℝ) ^ 2 * Real.log (H : ℝ))) :
    (((bX μ g H : ℕ) : ℝ) + 1) *
        (Real.log (Kr μ) - (1 / 2) * Real.log (μ : ℝ)) >
      Real.log 4 + Real.log (((N1X μ g H : ℕ) : ℝ) * ((QX μ g H : ℕ) : ℝ)) +
        (((dX μ g H : ℕ) : ℝ) + 2) * (Real.log (((dX μ g H : ℕ) : ℝ) + 1)) +
        (g : ℝ) * Real.log (((N1X μ g H : ℕ) : ℝ) * ((QX μ g H : ℕ) : ℝ)) +
        ((μ : ℝ) + 2) * ((dX μ g H : ℕ) : ℝ) * (g : ℝ) ^ 2 * Real.log (H : ℝ) := by
  have hN1 : (1 : ℝ) ≤ ((N1X μ g H : ℕ) : ℝ) := by exact_mod_cast one_le_N1V μ g H
  have hN1pos : (0 : ℝ) < ((N1X μ g H : ℕ) : ℝ) := by linarith
  have hQpos : (0 : ℝ) < ((QX μ g H : ℕ) : ℝ) := by exact_mod_cast one_le_QV μ g H
  have hd0 : (0 : ℝ) ≤ ((dX μ g H : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le _
  have hg0 : (0 : ℝ) ≤ (g : ℝ) := by exact_mod_cast Nat.zero_le g
  have hb0 : (0 : ℝ) ≤ ((bX μ g H : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le _
  have hlogK : 0 ≤ Real.log (Kr μ) := Real.log_nonneg (by
    simp only [Kr]; exact_mod_cast (le_of_lt (one_lt_KK μ)))
  have hbL : (0 : ℝ) ≤ ((bX μ g H : ℕ) : ℝ) * Real.log (Kr μ) := mul_nonneg hb0 hlogK
  have hden : (0 : ℝ) < 8 * (g : ℝ) + 8 := by linarith [hg0]
  have hlogNQ : Real.log (((N1X μ g H : ℕ) : ℝ) * ((QX μ g H : ℕ) : ℝ)) =
      Real.log ((N1X μ g H : ℕ) : ℝ) + Real.log ((QX μ g H : ℕ) : ℝ) :=
    Real.log_mul (ne_of_gt hN1pos) (ne_of_gt hQpos)
  have hdiv8 : ((bX μ g H : ℕ) : ℝ) * Real.log (Kr μ) / (8 * (g : ℝ) + 8) ≤
      ((bX μ g H : ℕ) : ℝ) * Real.log (Kr μ) / 8 := by
    rw [div_le_iff₀ hden]
    have hX : (((bX μ g H : ℕ) : ℝ) * Real.log (Kr μ) / 8) * (8 * (g : ℝ) + 8)
        = ((bX μ g H : ℕ) : ℝ) * Real.log (Kr μ) * (g + 1) := by ring
    rw [hX]
    nlinarith [hbL, hg0]
  have hbnd : Real.log (((N1X μ g H : ℕ) : ℝ) * ((QX μ g H : ℕ) : ℝ)) ≤
      2 * Real.log ((N1X μ g H : ℕ) : ℝ) + Real.log 16 + ((bX μ g H : ℕ) : ℝ) * Real.log (Kr μ) / 8 := by
    rw [hlogNQ]
    linarith [hsharp, hdiv8]
  have hbndg : (g : ℝ) * Real.log (((N1X μ g H : ℕ) : ℝ) * ((QX μ g H : ℕ) : ℝ)) ≤
      (g : ℝ) * (2 * Real.log ((N1X μ g H : ℕ) : ℝ) + Real.log 16) +
        ((bX μ g H : ℕ) : ℝ) * Real.log (Kr μ) / 8 := by
    have hgQ : (g : ℝ) * Real.log ((QX μ g H : ℕ) : ℝ) ≤
        (g : ℝ) * (Real.log 16 + Real.log ((N1X μ g H : ℕ) : ℝ) +
          ((bX μ g H : ℕ) : ℝ) * Real.log (Kr μ) / (8 * (g : ℝ) + 8)) :=
      mul_le_mul_of_nonneg_left hsharp hg0
    have hg3 : (g : ℝ) * (((bX μ g H : ℕ) : ℝ) * Real.log (Kr μ) / (8 * (g : ℝ) + 8)) ≤
        ((bX μ g H : ℕ) : ℝ) * Real.log (Kr μ) / 8 := by
      rw [← mul_div_assoc, div_le_iff₀ hden]
      nlinarith [hbL, hg0]
    rw [hlogNQ]
    nlinarith [hgQ, hg3]
  have hlogKm : Real.log (μ : ℝ) ≤ Real.log (Kr μ) := by
    rcases Nat.eq_zero_or_pos μ with h | h
    · subst h
      simp only [Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg (by simp [Kr, KK])
    · have h2 : (μ : ℝ) ≤ Kr μ := by
        have h3 : μ ≤ KK μ := by simp only [KK]; omega
        simp only [Kr]
        exact_mod_cast h3
      exact Real.log_le_log (by exact_mod_cast h) h2
  have hLHS : (((bX μ g H : ℕ) : ℝ) + 1) * (Real.log (Kr μ) - (1 / 2) * Real.log (μ : ℝ)) ≥
      ((bX μ g H : ℕ) : ℝ) * Real.log (Kr μ) / 2 := by
    have h1 : Real.log (Kr μ) - (1 / 2) * Real.log (μ : ℝ) ≥ (1 / 2) * Real.log (Kr μ) := by
      linarith
    nlinarith [h1, hb0, hlogK]
  have hstar := cmY_B μ hd0 hN1 hg0
  have h4 : (1 / 4) * ((bX μ g H : ℕ) : ℝ) * Real.log (Kr μ) >
      Real.log 4 + Real.log 16 + 2 * Real.log ((N1X μ g H : ℕ) : ℝ) +
        (((dX μ g H : ℕ) : ℝ) + 2) * (Real.log (((dX μ g H : ℕ) : ℝ) + 1)) +
        (g : ℝ) * (2 * Real.log ((N1X μ g H : ℕ) : ℝ) + Real.log 16) +
        ((μ : ℝ) + 2) * ((dX μ g H : ℕ) : ℝ) * (g : ℝ) ^ 2 * Real.log (H : ℝ) := by
    linarith [hM, hstar]
  linarith [hLHS, h4, hbnd, hbndg]


lemma pow_add_one_gt (Q : ℕ) (hQ : 1 ≤ Q) (n : ℕ) (hn : 2 ≤ n) : Q ^ n + 1 < (Q + 1) ^ n := by
  obtain ⟨m, hm⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  subst hm
  induction m with
  | zero =>
      show Q ^ 2 + 1 < (Q + 1) ^ 2
      nlinarith [hQ]
  | succ m ih =>
      have h2 : 1 ≤ Q ^ (m + 2) := one_le_pow₀ hQ
      have h3 : Q ^ (m + 2) < (Q + 1) ^ (m + 2) := by omega
      have e1 : Q ^ (m + 1 + 2) = Q ^ (m + 2) * Q := by
        rw [show m + 1 + 2 = m + 2 + 1 by omega, pow_succ]
      have e2 : (Q + 1) ^ (m + 1 + 2) = (Q + 1) ^ (m + 2) * (Q + 1) := by
        rw [show m + 1 + 2 = m + 2 + 1 by omega, pow_succ]
      rw [e1, e2]
      have h4 : Q ^ (m + 2) * Q + 1 ≤ Q ^ (m + 2) * Q + Q ^ (m + 2) := by omega
      have h5 : Q ^ (m + 2) * Q + Q ^ (m + 2) = Q ^ (m + 2) * (Q + 1) := by ring
      have h6 : Q ^ (m + 2) * (Q + 1) < (Q + 1) ^ (m + 2) * (Q + 1) :=
        Nat.mul_lt_mul_of_pos_right h3 (by omega)
      omega

lemma cardineq_abstract (K : ℝ) (hK1 : (1 : ℝ) ≤ K) (lam b N1 m c Q : ℕ)
    (hQ1 : 1 ≤ Q) (hN1 : 1 ≤ N1) (hm : 1 ≤ m) (hlam1 : 1 ≤ lam)
    (hce : ((c : ℕ) : ℝ) ≤ 2 * K ^ b)
    (hQV : 4 * ((N1 : ℕ) : ℝ) *
      Real.exp (((b : ℕ) : ℝ) * Real.log K / ((lam : ℕ) : ℝ)) ≤ ((Q : ℕ) : ℝ))
    (hlam : lam + 1 = N1 / m) :
    (Q + 1) ^ N1 > (2 * (N1 * c * Q) + 1) ^ m := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  have hNpos : (0 : ℝ) < ((N1 : ℕ) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN1)
  have hQpos : (0 : ℝ) < ((Q : ℕ) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hQ1)
  have hQ1r : (1 : ℝ) ≤ ((Q : ℕ) : ℝ) := by exact_mod_cast hQ1
  have hlampos : 0 < ((lam : ℕ) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hlam1)
  have hexp : K ^ b ≤ (((Q : ℕ) : ℝ) / (4 * ((N1 : ℕ) : ℝ))) ^ lam := by
    have h4N : 0 < 4 * ((N1 : ℕ) : ℝ) := by linarith
    have hstep : Real.exp (((b : ℕ) : ℝ) * Real.log K / ((lam : ℕ) : ℝ)) ≤
        ((Q : ℕ) : ℝ) / (4 * ((N1 : ℕ) : ℝ)) := by
      rw [le_div_iff₀ h4N]
      nlinarith [hQV]
    calc K ^ b = Real.exp (((b : ℕ) : ℝ) * Real.log K) := by
          rw [Real.exp_nat_mul, Real.exp_log hKpos]
      _ = Real.exp (((lam : ℕ) : ℝ) * (((b : ℕ) : ℝ) * Real.log K / ((lam : ℕ) : ℝ))) := by
          rw [mul_div_cancel₀ _ (ne_of_gt hlampos)]
      _ = (Real.exp (((b : ℕ) : ℝ) * Real.log K / ((lam : ℕ) : ℝ))) ^ lam := by
          rw [Real.exp_nat_mul]
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le hstep lam
  have hkey : 2 * ((N1 : ℕ) : ℝ) * (2 * K ^ b) * ((Q : ℕ) : ℝ) + 1 <
      (((Q : ℕ) : ℝ) + 1) ^ (lam + 1) := by
    have hN1r : (1 : ℝ) ≤ ((N1 : ℕ) : ℝ) := by exact_mod_cast hN1
    have h4N1 : (1 : ℝ) ≤ 4 * ((N1 : ℕ) : ℝ) := by linarith
    have h4N1pow : 4 * ((N1 : ℕ) : ℝ) ≤ (4 * ((N1 : ℕ) : ℝ)) ^ lam := by
      have hp : (1 : ℝ) ≤ (4 * ((N1 : ℕ) : ℝ)) ^ (lam - 1) := one_le_pow₀ h4N1
      rw [show (4 * ((N1 : ℕ) : ℝ)) ^ lam =
          (4 * ((N1 : ℕ) : ℝ)) ^ (lam - 1) * (4 * ((N1 : ℕ) : ℝ)) by
        rw [← pow_succ]; congr 1; omega]
      nlinarith [hp, h4N1]
    have hstep1 : 4 * ((N1 : ℕ) : ℝ) * K ^ b * ((Q : ℕ) : ℝ) ≤ ((Q : ℕ) : ℝ) ^ (lam + 1) := by
      have h1 : 4 * ((N1 : ℕ) : ℝ) * K ^ b ≤ 4 * ((N1 : ℕ) : ℝ) *
          (((Q : ℕ) : ℝ) / (4 * ((N1 : ℕ) : ℝ))) ^ lam := by nlinarith [hexp, hNpos]
      have h4Npos : (0 : ℝ) < 4 * ((N1 : ℕ) : ℝ) := by linarith
      have hQlam : (0 : ℝ) ≤ ((Q : ℕ) : ℝ) ^ lam := by positivity
      have h2 : 4 * ((N1 : ℕ) : ℝ) * (((Q : ℕ) : ℝ) / (4 * ((N1 : ℕ) : ℝ))) ^ lam *
          ((Q : ℕ) : ℝ) ≤ ((Q : ℕ) : ℝ) ^ (lam + 1) := by
        have hbase : (((Q : ℕ) : ℝ) / (4 * ((N1 : ℕ) : ℝ))) ^ lam ≤
            ((Q : ℕ) : ℝ) ^ lam / (4 * ((N1 : ℕ) : ℝ)) := by
          rw [div_pow]
          exact div_le_div_of_nonneg_left hQlam h4Npos h4N1pow
        have hstep2 : 4 * ((N1 : ℕ) : ℝ) * (((Q : ℕ) : ℝ) / (4 * ((N1 : ℕ) : ℝ))) ^ lam *
            ((Q : ℕ) : ℝ) ≤ 4 * ((N1 : ℕ) : ℝ) * (((Q : ℕ) : ℝ) ^ lam / (4 * ((N1 : ℕ) : ℝ))) *
              ((Q : ℕ) : ℝ) := by
          have := mul_le_mul_of_nonneg_right hbase hQpos.le
          nlinarith [this, h4Npos]
        have hfin : 4 * ((N1 : ℕ) : ℝ) * (((Q : ℕ) : ℝ) ^ lam / (4 * ((N1 : ℕ) : ℝ))) *
            ((Q : ℕ) : ℝ) = ((Q : ℕ) : ℝ) ^ (lam + 1) := by
          field_simp
          ring
        linarith [hstep2, hfin]
      have h1' : 4 * ((N1 : ℕ) : ℝ) * K ^ b * ((Q : ℕ) : ℝ) ≤
          4 * ((N1 : ℕ) : ℝ) * (((Q : ℕ) : ℝ) / (4 * ((N1 : ℕ) : ℝ))) ^ lam *
            ((Q : ℕ) : ℝ) := mul_le_mul_of_nonneg_right h1 hQpos.le
      linarith [h1', h2]
    have hstrict : (Q ^ (lam + 1) + 1 : ℕ) < ((Q + 1) ^ (lam + 1) : ℕ) :=
      pow_add_one_gt Q hQ1 (lam + 1) (by omega)
    have hstrictR : ((Q : ℕ) : ℝ) ^ (lam + 1) + 1 < (((Q : ℕ) : ℝ) + 1) ^ (lam + 1) := by
      exact_mod_cast hstrict
    nlinarith [hstep1, hstrictR]
  have hLHS : ((2 * (N1 * c * Q) + 1 : ℕ) : ℝ) ≤
      2 * ((N1 : ℕ) : ℝ) * (2 * K ^ b) * ((Q : ℕ) : ℝ) + 1 := by
    push_cast
    have h1 : ((c : ℕ) : ℝ) * (((N1 : ℕ) : ℝ) * ((Q : ℕ) : ℝ)) ≤
        (2 * K ^ b) * (((N1 : ℕ) : ℝ) * ((Q : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hce (by positivity)
    linarith [h1]
  have hfinal : (((2 * (N1 * c * Q) + 1) ^ m : ℕ) : ℝ) < (((Q + 1) ^ N1 : ℕ) : ℝ) := by
    have hpow : (2 * ((N1 : ℕ) : ℝ) * (2 * K ^ b) * ((Q : ℕ) : ℝ) + 1) ^ m <
        ((((Q : ℕ) : ℝ) + 1) ^ (lam + 1)) ^ m :=
      pow_lt_pow_left₀ hkey (by positivity) (by omega : m ≠ 0)
    have hpow2 : ((((Q : ℕ) : ℝ) + 1) ^ (lam + 1)) ^ m =
        (((Q : ℕ) : ℝ) + 1) ^ ((lam + 1) * m) := by rw [pow_mul]
    have hle : (lam + 1) * m ≤ N1 := by
      rw [hlam]; exact Nat.div_mul_le_self _ _
    have hmono : (((Q : ℕ) : ℝ) + 1) ^ ((lam + 1) * m) ≤ (((Q : ℕ) : ℝ) + 1) ^ N1 :=
      pow_le_pow_right₀ (by linarith) hle
    have hcastL : (((2 * (N1 * c * Q) + 1) ^ m : ℕ) : ℝ) =
        ((2 * (N1 * c * Q) + 1 : ℕ) : ℝ) ^ m := by push_cast; ring
    have hcastR : (((Q + 1) ^ N1 : ℕ) : ℝ) = (((Q : ℕ) : ℝ) + 1) ^ N1 := by push_cast; ring
    rw [hcastL, hcastR]
    calc ((2 * (N1 * c * Q) + 1 : ℕ) : ℝ) ^ m
        ≤ (2 * ((N1 : ℕ) : ℝ) * (2 * K ^ b) * ((Q : ℕ) : ℝ) + 1) ^ m :=
          pow_le_pow_left₀ (by positivity) hLHS m
      _ < ((((Q : ℕ) : ℝ) + 1) ^ (lam + 1)) ^ m := hpow
      _ = (((Q : ℕ) : ℝ) + 1) ^ ((lam + 1) * m) := hpow2
      _ ≤ (((Q : ℕ) : ℝ) + 1) ^ N1 := hmono
  exact_mod_cast hfinal


lemma lamX_eq (μ g H : ℕ) (hlam : 8 * g + 8 ≤ lamX μ g H) :
    lamX μ g H + 1 = N1X μ g H / mX μ g H := by
  have hge : 8 * g + 8 ≤ N1V μ g H / mV μ g H - 1 := by simpa only [lamX, lamV] using hlam
  simp only [lamX, lamV, N1X, mX]
  omega


end Work.WilkiesH.Interp
