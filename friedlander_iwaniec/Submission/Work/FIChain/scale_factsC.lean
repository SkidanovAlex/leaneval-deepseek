/-
# `Submission.Work.FIChain.scale_factsC` — the scale facts of the `B`-dependent family

The family is that of `Submission/Work/FIChain/Defs.lean`: with `η_c = 1/32`,
`s = sc x B = 2^{Jc x B}` the power of two just below `x^{3/16}/(2(log x)^{B+2})` and
`Yc x B = √x/(s·(log x)^{B+2})`, one has the sandwich

  `x^{5/16} < Yc x B ≤ 2·x^{5/16}`

(`Submission.Work.FIChain.window_marginsC`).  This file derives from it the sixteen
numerical facts about the family that the `ρ`-window (`window_marginsC`,
`rhoWindowC_param`), the `b̃`-window (`bprimeWindowC`) and the §8 estimate
(`smAvg_S3_leC`) consume:

* the size of the window ends `⌊Yc⌋₊`, `⌊e·Yc⌋₊` and their logs, including
  `(log ⌊e·Yc⌋₊)^6 ≤ ⌊Yc⌋₊^{3/16}` (the exponent hypothesis of `LocalS5c`);
* `Δ², Δ⁴ ≤ ⌊Yc⌋₊` and `Δ < z = ⌊Yc⌋₊`;
* `1 ≤ ⌊s·z⌋₊` and the product identity `x ≤ 2·s²·Yc·z·(log x)^{2B+4}` (the floor `z = ⌊Yc⌋₊`
  differs from `Yc` by less than a factor `2`);
* `Δ·⌊e·Yc⌋₊·⌊Yc⌋₊ ≤ D` and `Δ·⌊e·Yc⌋₊ ≤ D` for the modulus cutoff `D = ⌊x^{11/16}⌋`.

All constants are explicit (`Δ = ⌈x^{1/100}⌉`, `⌊Yc⌋₊ ≍ x^{5/16}`); every estimate is proved
by the asymptotics toolkit `Submission.Work.FITop.RCPrelude`.
-/
import Mathlib
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.window_marginsC

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Filter

noncomputable section

private lemma etac_quarter : (1 : ℝ) / 4 - 2 * etac = 3 / 16 := by norm_num [etac]

/-! ## 1. The sandwich for `Yc` -/

/-- `u = x^{1/4-2η_c}/(2(log x)^{B+2}) ≤ sc x B`. -/
private lemma u_le_sc (x : ℕ) (B : ℝ) (hx1 : 1 < (x : ℝ)) :
    (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2)) ≤ sc x B := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hLpos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hupos : 0 < (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2)) :=
    div_pos (Real.rpow_pos_of_pos hxpos _) (by positivity)
  have ht : Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2)))
      / Real.log 2 ≤ (Jc x B : ℝ) := by rw [Jc]; exact Nat.le_ceil _
  have hpow : (2 : ℝ) ^ (Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
      / (2 * (Real.log (x : ℝ)) ^ (B + 2))) / Real.log 2)
      = (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2)) :=
    Work.FITop.FI_two_rpow_log_div_log _ hupos
  calc (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2))
      = (2 : ℝ) ^ (Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
          / (2 * (Real.log (x : ℝ)) ^ (B + 2))) / Real.log 2) := hpow.symm
    _ ≤ (2 : ℝ) ^ ((Jc x B : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) ht
    _ = sc x B := by rw [sc, Real.rpow_natCast]

/-- `sc x B · (log x)^{B+2} < x^{3/16}`. -/
private lemma sc_mul_lt (x : ℕ) (B : ℝ) (hx1 : 1 < (x : ℝ))
    (hu : 1 ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2))) :
    sc x B * (Real.log (x : ℝ)) ^ (B + 2) < (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hLpos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hLp_pos : 0 < (Real.log (x : ℝ)) ^ (B + 2) := Real.rpow_pos_of_pos hLpos _
  have hupos : 0 < (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2)) :=
    lt_of_lt_of_le zero_lt_one hu
  have ht0 : 0 ≤ Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2)))
      / Real.log 2 :=
    div_nonneg (Real.log_nonneg hu) (Real.log_pos (by norm_num)).le
  have hJlt : (Jc x B : ℝ) <
      Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2)))
        / Real.log 2 + 1 := by
    rw [Jc]; exact Nat.ceil_lt_add_one ht0
  have hpow : (2 : ℝ) ^ (Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
      / (2 * (Real.log (x : ℝ)) ^ (B + 2))) / Real.log 2)
      = (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2)) :=
    Work.FITop.FI_two_rpow_log_div_log _ hupos
  have hlt : (2 : ℝ) ^ (Jc x B) < 2 * ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
      / (2 * (Real.log (x : ℝ)) ^ (B + 2))) := by
    calc (2 : ℝ) ^ (Jc x B) = (2 : ℝ) ^ ((Jc x B : ℝ)) := (Real.rpow_natCast 2 (Jc x B)).symm
      _ < (2 : ℝ) ^ (Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
            / (2 * (Real.log (x : ℝ)) ^ (B + 2))) / Real.log 2 + 1) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hJlt
      _ = 2 * ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2))) := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one, hpow]; ring
  calc sc x B * (Real.log (x : ℝ)) ^ (B + 2)
      = (2 : ℝ) ^ (Jc x B) * (Real.log (x : ℝ)) ^ (B + 2) := rfl
    _ < (2 * ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2))))
          * (Real.log (x : ℝ)) ^ (B + 2) := mul_lt_mul_of_pos_right hlt hLp_pos
    _ = (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) := by field_simp

/-- `x^{5/16} < Yc x B`. -/
private lemma Yc_lower (x : ℕ) (B : ℝ) (hx1 : 1 < (x : ℝ))
    (hu : 1 ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2))) :
    (x : ℝ) ^ ((5 : ℝ) / 16) < Yc x B := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hLpos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hLp_pos : 0 < (Real.log (x : ℝ)) ^ (B + 2) := Real.rpow_pos_of_pos hLpos _
  have hsc_pos : 0 < sc x B := pow_pos (by norm_num : (0 : ℝ) < 2) (Jc x B)
  have hden_pos : 0 < sc x B * (Real.log (x : ℝ)) ^ (B + 2) := mul_pos hsc_pos hLp_pos
  have hsc_lt := sc_mul_lt x B hx1 hu
  have hmain : Real.sqrt (x : ℝ) / (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
      < Real.sqrt (x : ℝ) / (sc x B * (Real.log (x : ℝ)) ^ (B + 2)) :=
    div_lt_div_of_pos_left (Real.sqrt_pos.mpr hxpos) hden_pos hsc_lt
  have heq : Real.sqrt (x : ℝ) / (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) = (x : ℝ) ^ ((5 : ℝ) / 16) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hxpos]
    congr 1
    norm_num [etac]
  calc (x : ℝ) ^ ((5 : ℝ) / 16)
      = Real.sqrt (x : ℝ) / (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) := heq.symm
    _ < Real.sqrt (x : ℝ) / (sc x B * (Real.log (x : ℝ)) ^ (B + 2)) := hmain
    _ = Yc x B := rfl

/-- `Yc x B ≤ 2·x^{5/16}`. -/
private lemma Yc_upper (x : ℕ) (B : ℝ) (hx1 : 1 < (x : ℝ)) :
    Yc x B ≤ 2 * (x : ℝ) ^ ((5 : ℝ) / 16) := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hLpos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hLp_pos : 0 < (Real.log (x : ℝ)) ^ (B + 2) := Real.rpow_pos_of_pos hLpos _
  have hupos : 0 < (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2)) :=
    div_pos (Real.rpow_pos_of_pos hxpos _) (by positivity)
  have hle := u_le_sc x B hx1
  have hden : 0 < (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2))
      * (Real.log (x : ℝ)) ^ (B + 2) := mul_pos hupos hLp_pos
  have hstep : Yc x B ≤ Real.sqrt (x : ℝ) /
      ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2))
        * (Real.log (x : ℝ)) ^ (B + 2)) := by
    rw [Yc]
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hden
      (mul_le_mul_of_nonneg_right hle hLp_pos.le)
  have hval : (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2))
      * (Real.log (x : ℝ)) ^ (B + 2) = (x : ℝ) ^ ((3 : ℝ) / 16) / 2 := by
    rw [etac_quarter, div_mul_eq_mul_div]
    exact mul_div_mul_right _ _ (ne_of_gt hLp_pos)
  have hval2 : Real.sqrt (x : ℝ) / ((x : ℝ) ^ ((3 : ℝ) / 16) / 2)
      = 2 * (x : ℝ) ^ ((5 : ℝ) / 16) := by
    have hx3 : (x : ℝ) ^ ((3 : ℝ) / 16) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hxpos _)
    have hA : Real.sqrt (x : ℝ) / ((x : ℝ) ^ ((3 : ℝ) / 16) / 2)
        = 2 * ((x : ℝ) ^ ((1 : ℝ) / 2) / (x : ℝ) ^ ((3 : ℝ) / 16)) := by
      rw [Real.sqrt_eq_rpow]
      field_simp
    rw [hA, ← Real.rpow_sub hxpos]
    congr 1
    norm_num
  calc Yc x B
      ≤ Real.sqrt (x : ℝ) /
        ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2))
          * (Real.log (x : ℝ)) ^ (B + 2)) := hstep
    _ = Real.sqrt (x : ℝ) / ((x : ℝ) ^ ((3 : ℝ) / 16) / 2) := by rw [hval]
    _ = 2 * (x : ℝ) ^ ((5 : ℝ) / 16) := hval2

private lemma Yc_nonneg (x : ℕ) (B : ℝ) (hL : 0 < Real.log (x : ℝ)) : 0 ≤ Yc x B := by
  rw [Yc]
  exact div_nonneg (Real.sqrt_nonneg _)
    (mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2) (Jc x B)) (Real.rpow_pos_of_pos hL _)).le

private lemma Yc_pos (x : ℕ) (B : ℝ) (hx1 : 1 < (x : ℝ)) : 0 < Yc x B := by
  rw [Yc]
  exact div_pos (Real.sqrt_pos.mpr (by linarith))
    (mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2) (Jc x B))
      (Real.rpow_pos_of_pos (Real.log_pos hx1) _))

/-- `x^{5/16}/2 ≤ ⌊Yc x B⌋₊`. -/
private lemma floor_Yc_lower (x : ℕ) (B : ℝ) (hx1 : 1 < (x : ℝ))
    (hu : 1 ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2)))
    (hP : 2 ≤ (x : ℝ) ^ ((5 : ℝ) / 16)) :
    (x : ℝ) ^ ((5 : ℝ) / 16) / 2 ≤ (⌊Yc x B⌋₊ : ℝ) := by
  have hYlow : (x : ℝ) ^ ((5 : ℝ) / 16) < Yc x B := Yc_lower x B hx1 hu
  have hlt := Nat.lt_floor_add_one (Yc x B)
  have h1 : (1 : ℝ) ≤ (x : ℝ) ^ ((5 : ℝ) / 16) / 2 := by linarith
  linarith

/-- `⌊Yc x B⌋₊ ≤ 2·x^{5/16}`. -/
private lemma floor_Yc_upper (x : ℕ) (B : ℝ) (hx1 : 1 < (x : ℝ)) :
    (⌊Yc x B⌋₊ : ℝ) ≤ 2 * (x : ℝ) ^ ((5 : ℝ) / 16) :=
  le_trans (Nat.floor_le (Yc_nonneg x B (Real.log_pos hx1))) (Yc_upper x B hx1)

/-- `u = x^{1/4-2η_c}/(2(log x)^{B+2}) ≥ 1` eventually. -/
private lemma ev_u_ge_one (B : ℝ) :
    ∀ᶠ x : ℕ in Filter.atTop,
      1 ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2)) := by
  filter_upwards [Work.FITop.FI_ev_log_rpow_le_nat (b := B + 2) (ε := (3 : ℝ) / 16)
      (C := 1 / 2) (by norm_num) (by norm_num), eventually_ge_atTop 2] with x hle hx2
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hLpos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  rw [etac_quarter, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (Real.log (x : ℝ)) ^ (B + 2))]
  linarith

theorem scale_factsC (B : ℝ) (hB : 0 < B) :
    ∀ᶠ x : ℕ in Filter.atTop,
      256 ≤ ⌊Work.FIChain.Yc x B⌋₊ ∧ ⌊Work.FIChain.Yc x B⌋₊ ≤ ⌊Real.exp 1 * Work.FIChain.Yc x B⌋₊ ∧
      ⌊Real.exp 1 * Work.FIChain.Yc x B⌋₊ ≤ x ∧
      Real.log (x : ℝ) ≤ 4 * Real.log (⌊Work.FIChain.Yc x B⌋₊ : ℝ) ∧
      (Real.log (⌊Real.exp 1 * Work.FIChain.Yc x B⌋₊ : ℝ)) ^ 6 ≤ (⌊Work.FIChain.Yc x B⌋₊ : ℝ) ^ ((3 : ℝ) / 16) ∧
      Work.FIChain.Deltac x ^ 2 ≤ ⌊Work.FIChain.Yc x B⌋₊ ∧ Work.FIChain.Deltac x ^ 4 ≤ ⌊Work.FIChain.Yc x B⌋₊ ∧
      (Work.FIChain.Deltac x : ℝ) < Work.FIChain.zc x B ∧ Work.FIChain.zc x B ≤ (x : ℝ) ∧
      1 ≤ Work.FIChain.Zc x B ∧ Work.FIChain.Deltac x ≤ Work.FIChain.Zc x B ∧
      (Work.FIChain.Deltac x : ℝ) < Work.FIChain.sc x B * Work.FIChain.zc x B ∧
      (x : ℝ) ≤ 2 * (Work.FIChain.sc x B ^ 2 * Work.FIChain.Yc x B * Work.FIChain.zc x B
        * (Real.log (x : ℝ)) ^ (2 * B + 4)) ∧
      Work.FIChain.Deltac x * ⌊Real.exp 1 * Work.FIChain.Yc x B⌋₊ * Work.FIChain.Zc x B ≤ Work.FIChain.Dc x ∧
      Work.FIChain.Deltac x * ⌊Real.exp 1 * Work.FIChain.Yc x B⌋₊ ≤ Work.FIChain.Dc x ∧
      1 ≤ ⌊Work.FIChain.sc x B * Work.FIChain.zc x B⌋₊ := by
  have _ : (0 : ℝ) < B := hB
  filter_upwards [ev_u_ge_one B, eventually_ge_atTop 2,
    Work.FITop.FI_ev_log_ge_nat (16 * Real.log 2 + 16),
    Work.FITop.FI_ev_rpow_ge_nat ((5 : ℝ) / 16) (by norm_num) 4096,
    Work.FITop.FI_ev_rpow_ge_nat ((109 : ℝ) / 400) (by norm_num) 32,
    Work.FITop.FI_ev_rpow_ge_nat ((121 : ℝ) / 400) (by norm_num) 4,
    Work.FITop.FI_ev_Delta1_le_two_Lam1,
    Work.FITop.FI_ev_Lam1_ge_one,
    Work.FITop.FI_ev_Dcut_lower,
    Work.FITop.FI_ev_rpow_ge_nat ((21 : ℝ) / 400) (by norm_num) (16 * Real.exp 1),
    Work.FITop.FI_ev_rpow_ge_nat ((73 : ℝ) / 200) (by norm_num) (8 * Real.exp 1),
    Work.FITop.FI_ev_rpow_ge_nat ((11 : ℝ) / 16) (by norm_num) (2 * Real.exp 1),
    Work.FITop.FI_ev_log_rpow_le_nat (b := (6 : ℝ)) (ε := (15 : ℝ) / 256)
      (C := (8 / 3) ^ 6 * (2 : ℝ) ^ (-((3 : ℝ) / 16)))
      (mul_pos (by positivity) (Real.rpow_pos_of_pos (by norm_num) _)) (by norm_num)]
    with x hu hx2 hlog hP hR2 hR3 hD2raw hLam1raw hDlraw hE1 hE2 hE3 hlog6
  have hD2 : (Deltac x : ℝ) ≤ 2 * Work.FITop.Lam1 x := hD2raw
  have hLam1 : (1 : ℝ) ≤ Work.FITop.Lam1 x := hLam1raw
  have hDl : (x : ℝ) ^ ((11 : ℝ) / 16) / 2 ≤ (Dc x : ℝ) := hDlraw
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := hxpos.le
  have hLpos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hLp_pos : 0 < (Real.log (x : ℝ)) ^ (B + 2) := Real.rpow_pos_of_pos hLpos _
  have hsc_pos : 0 < sc x B := pow_pos (by norm_num : (0 : ℝ) < 2) (Jc x B)
  have hsc_one : (1 : ℝ) ≤ sc x B := by
    rw [sc]
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hYpos : 0 < Yc x B := Yc_pos x B hx1
  have hYlow : (x : ℝ) ^ ((5 : ℝ) / 16) < Yc x B := Yc_lower x B hx1 hu
  have hYup : Yc x B ≤ 2 * (x : ℝ) ^ ((5 : ℝ) / 16) := Yc_upper x B hx1
  have hYc_ge2 : (2 : ℝ) ≤ Yc x B := by linarith [hP, hYlow]
  have hFloorLow : (x : ℝ) ^ ((5 : ℝ) / 16) / 2 ≤ (⌊Yc x B⌋₊ : ℝ) :=
    floor_Yc_lower x B hx1 hu (by linarith [hP])
  have hFloorUp : (⌊Yc x B⌋₊ : ℝ) ≤ 2 * (x : ℝ) ^ ((5 : ℝ) / 16) := floor_Yc_upper x B hx1
  have hYc_floor : Yc x B - 1 ≤ (⌊Yc x B⌋₊ : ℝ) := by
    have h := Nat.lt_floor_add_one (Yc x B)
    linarith
  have hzc_eq : zc x B = (⌊Yc x B⌋₊ : ℝ) := rfl
  have hZc_eq : Zc x B = ⌊Yc x B⌋₊ := rfl
  have hE3' : (2 : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 16) := by
    have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    linarith [hE3, he]
  have hDlat : (Deltac x : ℝ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 100) := by
    have h := hD2
    rwa [Work.FITop.Lam1] at h
  -- 1
  have hC1 : 256 ≤ ⌊Yc x B⌋₊ := by
    refine Nat.le_floor ?_
    have h256 : ((256 : ℕ) : ℝ) = 256 := by norm_num
    rw [h256]
    linarith [hP, hYlow]
  -- 2
  have hC2 : ⌊Yc x B⌋₊ ≤ ⌊Real.exp 1 * Yc x B⌋₊ := by
    refine Nat.floor_le_floor ?_
    exact le_mul_of_one_le_left hYpos.le (Real.one_le_exp (by norm_num))
  -- 3
  have hC3 : ⌊Real.exp 1 * Yc x B⌋₊ ≤ x := by
    have hfl : (⌊Real.exp 1 * Yc x B⌋₊ : ℝ) ≤ (x : ℝ) := by
      have h1 : (⌊Real.exp 1 * Yc x B⌋₊ : ℝ) ≤ Real.exp 1 * Yc x B :=
        Nat.floor_le (mul_nonneg (Real.exp_pos 1).le hYpos.le)
      have h2 : Real.exp 1 * Yc x B ≤ Real.exp 1 * (2 * (x : ℝ) ^ ((5 : ℝ) / 16)) :=
        mul_le_mul_of_nonneg_left hYup (Real.exp_pos 1).le
      have h4 : (2 * Real.exp 1) * (x : ℝ) ^ ((5 : ℝ) / 16)
          ≤ (x : ℝ) ^ ((11 : ℝ) / 16) * (x : ℝ) ^ ((5 : ℝ) / 16) :=
        mul_le_mul_of_nonneg_right hE3 (Real.rpow_nonneg hx0 ((5 : ℝ) / 16))
      have h5 : (x : ℝ) ^ ((11 : ℝ) / 16) * (x : ℝ) ^ ((5 : ℝ) / 16) = (x : ℝ) := by
        rw [← Real.rpow_add hxpos, show (11 : ℝ) / 16 + 5 / 16 = 1 by norm_num, Real.rpow_one]
      have h3 : Real.exp 1 * (2 * (x : ℝ) ^ ((5 : ℝ) / 16)) ≤ (x : ℝ) := by
        linarith [h4, h5]
      linarith
    exact_mod_cast hfl
  -- 4
  have hC4 : Real.log (x : ℝ) ≤ 4 * Real.log (⌊Yc x B⌋₊ : ℝ) := by
    have hpos : 0 < (x : ℝ) ^ ((5 : ℝ) / 16) / 2 := by linarith [hP]
    have hmono : Real.log ((x : ℝ) ^ ((5 : ℝ) / 16) / 2) ≤ Real.log (⌊Yc x B⌋₊ : ℝ) :=
      Real.log_le_log hpos hFloorLow
    have hval : Real.log ((x : ℝ) ^ ((5 : ℝ) / 16) / 2)
        = (5 : ℝ) / 16 * Real.log (x : ℝ) - Real.log 2 := by
      rw [Real.log_div (ne_of_gt (Real.rpow_pos_of_pos hxpos _)) (by norm_num : (2 : ℝ) ≠ 0),
        Real.log_rpow hxpos]
    rw [hval] at hmono
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith [hmono, hlog, hl2]
  -- 5
  have hC5 : (Real.log (⌊Real.exp 1 * Yc x B⌋₊ : ℝ)) ^ 6
      ≤ (⌊Yc x B⌋₊ : ℝ) ^ ((3 : ℝ) / 16) := by
    have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have hE1n : (1 : ℕ) ≤ ⌊Real.exp 1 * Yc x B⌋₊ := by
      refine Nat.le_floor ?_
      push_cast
      have hm := mul_le_mul_of_nonneg_right he1 hYpos.le
      have h1 : (1 : ℝ) ≤ (4096 : ℝ) := by norm_num
      linarith [hm, hP, hYlow, h1]
    have hE1' : (1 : ℝ) ≤ (⌊Real.exp 1 * Yc x B⌋₊ : ℝ) := by exact_mod_cast hE1n
    have hfloor_le : (⌊Real.exp 1 * Yc x B⌋₊ : ℝ) ≤ Real.exp 1 * (2 * (x : ℝ) ^ ((5 : ℝ) / 16)) := by
      calc (⌊Real.exp 1 * Yc x B⌋₊ : ℝ) ≤ Real.exp 1 * Yc x B :=
            Nat.floor_le (mul_nonneg (Real.exp_pos 1).le hYpos.le)
        _ ≤ Real.exp 1 * (2 * (x : ℝ) ^ ((5 : ℝ) / 16)) :=
            mul_le_mul_of_nonneg_left hYup (Real.exp_pos 1).le
    have hlogYc_le : Real.log (⌊Real.exp 1 * Yc x B⌋₊ : ℝ) ≤ (3 : ℝ) / 8 * Real.log (x : ℝ) := by
      have h2 : Real.log (Real.exp 1 * (2 * (x : ℝ) ^ ((5 : ℝ) / 16)))
          = 1 + Real.log 2 + (5 : ℝ) / 16 * Real.log (x : ℝ) := by
        rw [Real.log_mul (ne_of_gt (Real.exp_pos 1))
              (ne_of_gt (mul_pos (by norm_num) (Real.rpow_pos_of_pos hxpos _))),
          Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt (Real.rpow_pos_of_pos hxpos _)),
          Real.log_exp, Real.log_rpow hxpos]
        ring
      have h3 : 1 + Real.log 2 + (5 : ℝ) / 16 * Real.log (x : ℝ)
          ≤ (3 : ℝ) / 8 * Real.log (x : ℝ) := by
        have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        linarith [hlog, hl2]
      have h4 : Real.log (⌊Real.exp 1 * Yc x B⌋₊ : ℝ)
          ≤ Real.log (Real.exp 1 * (2 * (x : ℝ) ^ ((5 : ℝ) / 16))) :=
        Real.log_le_log (by exact_mod_cast hE1') hfloor_le
      rw [h2] at h4
      linarith [h4, h3]
    have hnonneg : 0 ≤ Real.log (⌊Real.exp 1 * Yc x B⌋₊ : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hE1')
    have h6 : (Real.log (⌊Real.exp 1 * Yc x B⌋₊ : ℝ)) ^ 6
        ≤ ((3 : ℝ) / 8 * Real.log (x : ℝ)) ^ 6 := pow_le_pow_left₀ hnonneg hlogYc_le 6
    have h6' : ((3 : ℝ) / 8 * Real.log (x : ℝ)) ^ 6
        ≤ (2 : ℝ) ^ (-((3 : ℝ) / 16)) * (x : ℝ) ^ ((15 : ℝ) / 256) := by
      have hlog6' : (Real.log (x : ℝ)) ^ 6
          ≤ ((8 / 3) ^ 6 * (2 : ℝ) ^ (-((3 : ℝ) / 16))) * (x : ℝ) ^ ((15 : ℝ) / 256) := by
        have h : (Real.log (x : ℝ)) ^ ((6 : ℕ) : ℝ)
            ≤ ((8 / 3) ^ 6 * (2 : ℝ) ^ (-((3 : ℝ) / 16))) * (x : ℝ) ^ ((15 : ℝ) / 256) := hlog6
        rwa [Real.rpow_natCast] at h
      have hconst : ((3 : ℝ) / 8) ^ 6 * ((8 / 3) ^ 6 * (2 : ℝ) ^ (-((3 : ℝ) / 16)))
          = (2 : ℝ) ^ (-((3 : ℝ) / 16)) := by
        have h1 : ((3 : ℝ) / 8) ^ 6 * ((8 / 3) ^ 6 * (2 : ℝ) ^ (-((3 : ℝ) / 16)))
            = (((3 : ℝ) / 8) * (8 / 3)) ^ 6 * (2 : ℝ) ^ (-((3 : ℝ) / 16)) := by
          rw [← mul_assoc, ← mul_pow]
        rw [h1, show ((3 : ℝ) / 8) * (8 / 3) = 1 by norm_num, one_pow, one_mul]
      calc ((3 : ℝ) / 8 * Real.log (x : ℝ)) ^ 6
          = ((3 : ℝ) / 8) ^ 6 * (Real.log (x : ℝ)) ^ 6 := by rw [mul_pow]
        _ ≤ ((3 : ℝ) / 8) ^ 6 * (((8 / 3) ^ 6 * (2 : ℝ) ^ (-((3 : ℝ) / 16)))
              * (x : ℝ) ^ ((15 : ℝ) / 256)) := mul_le_mul_of_nonneg_left hlog6' (by positivity)
        _ = (2 : ℝ) ^ (-((3 : ℝ) / 16)) * (x : ℝ) ^ ((15 : ℝ) / 256) := by
            rw [← mul_assoc, hconst]
    have h7 : (2 : ℝ) ^ (-((3 : ℝ) / 16)) * (x : ℝ) ^ ((15 : ℝ) / 256)
        ≤ (⌊Yc x B⌋₊ : ℝ) ^ ((3 : ℝ) / 16) := by
      have hbase : ((x : ℝ) ^ ((5 : ℝ) / 16) / 2) ^ ((3 : ℝ) / 16)
          = (2 : ℝ) ^ (-((3 : ℝ) / 16)) * (x : ℝ) ^ ((15 : ℝ) / 256) := by
        rw [Real.div_rpow (Real.rpow_nonneg hx0 _) (by norm_num : (0 : ℝ) ≤ 2)]
        rw [← Real.rpow_mul hx0, show (5 : ℝ) / 16 * ((3 : ℝ) / 16) = (15 : ℝ) / 256 by norm_num]
        rw [div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        ring
      rw [← hbase]
      exact Real.rpow_le_rpow (div_nonneg (Real.rpow_nonneg hx0 _) (by norm_num)) hFloorLow
        (by norm_num)
    exact le_trans h6 (le_trans h6' h7)
  -- 6 and 7
  have hD1 : 1 ≤ Deltac x := by
    have h : (1 : ℝ) ≤ (Deltac x : ℝ) := by
      have hle := Nat.le_ceil (Work.FITop.Lam1 x)
      show (1 : ℝ) ≤ ((⌈Work.FITop.Lam1 x⌉₊ : ℕ) : ℝ)
      linarith [hLam1, hle]
    exact_mod_cast h
  have hD4real : (Deltac x : ℝ) ^ 4 ≤ (⌊Yc x B⌋₊ : ℝ) := by
    have hLam4 : (Work.FITop.Lam1 x) ^ 4 = (x : ℝ) ^ ((1 : ℝ) / 25) := by
      rw [Work.FITop.Lam1, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
      congr 1
      norm_num
    have h2 : (2 * Work.FITop.Lam1 x) ^ 4 = 16 * (x : ℝ) ^ ((1 : ℝ) / 25) := by
      rw [mul_pow, hLam4]
      norm_num
    have h3 : 16 * (x : ℝ) ^ ((1 : ℝ) / 25) ≤ (x : ℝ) ^ ((5 : ℝ) / 16) / 2 := by
      have hx25 : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 25) := Real.rpow_nonneg hx0 _
      have hsplit : (x : ℝ) ^ ((5 : ℝ) / 16)
          = (x : ℝ) ^ ((109 : ℝ) / 400) * (x : ℝ) ^ ((1 : ℝ) / 25) := by
        rw [← Real.rpow_add hxpos]
        congr 1
        norm_num
      have hm := mul_le_mul_of_nonneg_right hR2 hx25
      rw [hsplit]
      linarith
    calc (Deltac x : ℝ) ^ 4 ≤ (2 * Work.FITop.Lam1 x) ^ 4 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hD2 4
      _ = 16 * (x : ℝ) ^ ((1 : ℝ) / 25) := h2
      _ ≤ (x : ℝ) ^ ((5 : ℝ) / 16) / 2 := h3
      _ ≤ (⌊Yc x B⌋₊ : ℝ) := hFloorLow
  have hC7 : Deltac x ^ 4 ≤ ⌊Yc x B⌋₊ := by
    have h : ((Deltac x ^ 4 : ℕ) : ℝ) ≤ ((⌊Yc x B⌋₊ : ℕ) : ℝ) := by
      push_cast
      exact hD4real
    exact_mod_cast h
  have hC6 : Deltac x ^ 2 ≤ ⌊Yc x B⌋₊ :=
    le_trans (pow_le_pow_right₀ hD1 (by norm_num : 2 ≤ 4)) hC7
  -- 8
  have hC8 : (Deltac x : ℝ) < zc x B := by
    have h2 : 2 * Work.FITop.Lam1 x ≤ (x : ℝ) ^ ((5 : ℝ) / 16) / 2 := by
      have hx100 : (0 : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 100) := Real.rpow_pos_of_pos hxpos _
      have hsplit : (x : ℝ) ^ ((5 : ℝ) / 16)
          = (x : ℝ) ^ ((121 : ℝ) / 400) * (x : ℝ) ^ ((1 : ℝ) / 100) := by
        rw [← Real.rpow_add hxpos]
        congr 1
        norm_num
      have hm := mul_le_mul_of_nonneg_right hR3 hx100.le
      have hlam : Work.FITop.Lam1 x = (x : ℝ) ^ ((1 : ℝ) / 100) := rfl
      rw [hlam, hsplit]
      linarith
    have hDlt : (Deltac x : ℝ) < 2 * Work.FITop.Lam1 x := by
      have h0 : 0 ≤ Work.FITop.Lam1 x := le_trans zero_le_one hLam1
      have hlt : ((⌈Work.FITop.Lam1 x⌉₊ : ℕ) : ℝ) < Work.FITop.Lam1 x + 1 :=
        Nat.ceil_lt_add_one h0
      show ((⌈Work.FITop.Lam1 x⌉₊ : ℕ) : ℝ) < 2 * Work.FITop.Lam1 x
      linarith
    rw [hzc_eq]
    linarith [hDlt, h2, hFloorLow]
  -- 9
  have hC9 : zc x B ≤ (x : ℝ) := by
    have h2 : 2 * (x : ℝ) ^ ((5 : ℝ) / 16) ≤ (x : ℝ) := by
      have hm : (2 : ℝ) * (x : ℝ) ^ ((5 : ℝ) / 16)
          ≤ (x : ℝ) ^ ((11 : ℝ) / 16) * (x : ℝ) ^ ((5 : ℝ) / 16) :=
        mul_le_mul_of_nonneg_right hE3' (Real.rpow_nonneg hx0 ((5 : ℝ) / 16))
      have hsum : (x : ℝ) ^ ((11 : ℝ) / 16) * (x : ℝ) ^ ((5 : ℝ) / 16) = (x : ℝ) := by
        rw [← Real.rpow_add hxpos, show (11 : ℝ) / 16 + 5 / 16 = 1 by norm_num, Real.rpow_one]
      linarith [hm, hsum]
    rw [hzc_eq]
    linarith [hFloorUp, h2]
  -- 10 and 11
  have hC10 : 1 ≤ Zc x B := by
    rw [hZc_eq]
    exact le_trans (by norm_num : 1 ≤ 256) hC1
  have hC11 : Deltac x ≤ Zc x B := by
    rw [hZc_eq]
    have h := hC8
    rw [hzc_eq] at h
    exact_mod_cast h.le
  -- 12
  have hC12 : (Deltac x : ℝ) < sc x B * zc x B :=
    lt_of_lt_of_le hC8 (le_mul_of_one_le_left (by rw [hzc_eq]; exact Nat.cast_nonneg _) hsc_one)
  -- 13
  have hC13 : (x : ℝ) ≤ 2 * (sc x B ^ 2 * Yc x B * zc x B * (Real.log (x : ℝ)) ^ (2 * B + 4)) := by
    have hkey : sc x B * Yc x B * (Real.log (x : ℝ)) ^ (B + 2) = Real.sqrt (x : ℝ) := by
      have h1 : sc x B * Yc x B = Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ (B + 2) := by
        rw [Yc]
        field_simp
      rw [h1]
      field_simp
    have hxeq : sc x B ^ 2 * Yc x B ^ 2 * ((Real.log (x : ℝ)) ^ (B + 2)) ^ 2 = (x : ℝ) := by
      have h1 : (sc x B * Yc x B * (Real.log (x : ℝ)) ^ (B + 2)) ^ 2 = (Real.sqrt (x : ℝ)) ^ 2 := by
        rw [hkey]
      rw [Real.sq_sqrt hx0] at h1
      calc sc x B ^ 2 * Yc x B ^ 2 * ((Real.log (x : ℝ)) ^ (B + 2)) ^ 2
          = (sc x B * Yc x B * (Real.log (x : ℝ)) ^ (B + 2)) ^ 2 := by ring
        _ = (x : ℝ) := h1
    have hzc_ge : Yc x B / 2 ≤ zc x B := by
      rw [hzc_eq]
      linarith [hYc_floor, hYc_ge2]
    have hnn : 0 ≤ sc x B ^ 2 * Yc x B := mul_nonneg (pow_nonneg hsc_pos.le 2) hYpos.le
    have hLp2_nn : 0 ≤ ((Real.log (x : ℝ)) ^ (B + 2)) ^ 2 := pow_nonneg hLp_pos.le 2
    have h1 : sc x B ^ 2 * Yc x B * (Yc x B / 2) * ((Real.log (x : ℝ)) ^ (B + 2)) ^ 2
        ≤ sc x B ^ 2 * Yc x B * zc x B * ((Real.log (x : ℝ)) ^ (B + 2)) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzc_ge hnn) hLp2_nn
    have h3 : sc x B ^ 2 * Yc x B * (Yc x B / 2) * ((Real.log (x : ℝ)) ^ (B + 2)) ^ 2
        = (x : ℝ) / 2 := by
      rw [show sc x B ^ 2 * Yc x B * (Yc x B / 2) * ((Real.log (x : ℝ)) ^ (B + 2)) ^ 2
          = (sc x B ^ 2 * Yc x B ^ 2 * ((Real.log (x : ℝ)) ^ (B + 2)) ^ 2) / 2 by ring]
      rw [hxeq]
    have hLp_sq : (Real.log (x : ℝ)) ^ (2 * B + 4) = ((Real.log (x : ℝ)) ^ (B + 2)) ^ 2 := by
      rw [show 2 * B + 4 = (B + 2) + (B + 2) by ring, Real.rpow_add hLpos]
      ring
    rw [hLp_sq]
    linarith [h1, h3]
  -- 14
  have hflE : (⌊Real.exp 1 * Yc x B⌋₊ : ℝ) ≤ 2 * Real.exp 1 * (x : ℝ) ^ ((5 : ℝ) / 16) := by
    calc (⌊Real.exp 1 * Yc x B⌋₊ : ℝ) ≤ Real.exp 1 * Yc x B :=
          Nat.floor_le (mul_nonneg (Real.exp_pos 1).le hYpos.le)
      _ ≤ Real.exp 1 * (2 * (x : ℝ) ^ ((5 : ℝ) / 16)) :=
          mul_le_mul_of_nonneg_left hYup (Real.exp_pos 1).le
      _ = 2 * Real.exp 1 * (x : ℝ) ^ ((5 : ℝ) / 16) := by ring
  have hflZ : (Zc x B : ℝ) ≤ 2 * (x : ℝ) ^ ((5 : ℝ) / 16) := hFloorUp
  have hC14 : Deltac x * ⌊Real.exp 1 * Yc x B⌋₊ * Zc x B ≤ Dc x := by
    have hall : (Deltac x : ℝ) * (⌊Real.exp 1 * Yc x B⌋₊ : ℝ) * (Zc x B : ℝ)
        ≤ (2 * (x : ℝ) ^ ((1 : ℝ) / 100)) * (2 * Real.exp 1 * (x : ℝ) ^ ((5 : ℝ) / 16))
          * (2 * (x : ℝ) ^ ((5 : ℝ) / 16)) := by
      have h1 : (Deltac x : ℝ) * (⌊Real.exp 1 * Yc x B⌋₊ : ℝ)
          ≤ (2 * (x : ℝ) ^ ((1 : ℝ) / 100))
            * (2 * Real.exp 1 * (x : ℝ) ^ ((5 : ℝ) / 16)) :=
        mul_le_mul hDlat hflE (Nat.cast_nonneg _) (by positivity)
      exact mul_le_mul h1 hflZ (Nat.cast_nonneg _) (by positivity)
    have hval : (2 * (x : ℝ) ^ ((1 : ℝ) / 100)) * (2 * Real.exp 1 * (x : ℝ) ^ ((5 : ℝ) / 16))
          * (2 * (x : ℝ) ^ ((5 : ℝ) / 16)) = 8 * Real.exp 1 * (x : ℝ) ^ ((127 : ℝ) / 200) := by
      rw [show (2 * (x : ℝ) ^ ((1 : ℝ) / 100)) * (2 * Real.exp 1 * (x : ℝ) ^ ((5 : ℝ) / 16))
            * (2 * (x : ℝ) ^ ((5 : ℝ) / 16))
          = 8 * Real.exp 1 * ((x : ℝ) ^ ((1 : ℝ) / 100)
              * ((x : ℝ) ^ ((5 : ℝ) / 16) * (x : ℝ) ^ ((5 : ℝ) / 16))) by ring]
      rw [← Real.rpow_add hxpos (5 / 16) (5 / 16),
        ← Real.rpow_add hxpos (1 / 100) (5 / 16 + 5 / 16),
        show (1 : ℝ) / 100 + (5 / 16 + 5 / 16) = 127 / 200 by norm_num]
    have hbound : 8 * Real.exp 1 * (x : ℝ) ^ ((127 : ℝ) / 200) ≤ (x : ℝ) ^ ((11 : ℝ) / 16) / 2 := by
      have hsplit : (x : ℝ) ^ ((11 : ℝ) / 16)
          = (x : ℝ) ^ ((21 : ℝ) / 400) * (x : ℝ) ^ ((127 : ℝ) / 200) := by
        rw [← Real.rpow_add hxpos, show (21 : ℝ) / 400 + 127 / 200 = 11 / 16 by norm_num]
      have hm : 16 * Real.exp 1 * (x : ℝ) ^ ((127 : ℝ) / 200)
          ≤ (x : ℝ) ^ ((21 : ℝ) / 400) * (x : ℝ) ^ ((127 : ℝ) / 200) :=
        mul_le_mul_of_nonneg_right hE1 (Real.rpow_nonneg hx0 ((127 : ℝ) / 200))
      rw [hsplit]
      linarith
    have hcast : ((Deltac x * ⌊Real.exp 1 * Yc x B⌋₊ * Zc x B : ℕ) : ℝ)
        = (Deltac x : ℝ) * (⌊Real.exp 1 * Yc x B⌋₊ : ℝ) * (Zc x B : ℝ) := by
      push_cast
      ring
    have hgoal : ((Deltac x * ⌊Real.exp 1 * Yc x B⌋₊ * Zc x B : ℕ) : ℝ) ≤ (Dc x : ℝ) := by
      rw [hcast]
      exact le_trans (le_trans hall (le_of_eq hval)) (le_trans hbound hDl)
    exact_mod_cast hgoal
  -- 15
  have hC15 : Deltac x * ⌊Real.exp 1 * Yc x B⌋₊ ≤ Dc x := by
    have hall : (Deltac x : ℝ) * (⌊Real.exp 1 * Yc x B⌋₊ : ℝ)
        ≤ (2 * (x : ℝ) ^ ((1 : ℝ) / 100)) * (2 * Real.exp 1 * (x : ℝ) ^ ((5 : ℝ) / 16)) :=
      mul_le_mul hDlat hflE (Nat.cast_nonneg _) (by positivity)
    have hval : (2 * (x : ℝ) ^ ((1 : ℝ) / 100)) * (2 * Real.exp 1 * (x : ℝ) ^ ((5 : ℝ) / 16))
        = 4 * Real.exp 1 * (x : ℝ) ^ ((129 : ℝ) / 400) := by
      rw [show (2 * (x : ℝ) ^ ((1 : ℝ) / 100)) * (2 * Real.exp 1 * (x : ℝ) ^ ((5 : ℝ) / 16))
          = 4 * Real.exp 1 * ((x : ℝ) ^ ((1 : ℝ) / 100) * (x : ℝ) ^ ((5 : ℝ) / 16)) by ring]
      rw [← Real.rpow_add hxpos, show (1 : ℝ) / 100 + 5 / 16 = 129 / 400 by norm_num]
    have hbound : 4 * Real.exp 1 * (x : ℝ) ^ ((129 : ℝ) / 400) ≤ (x : ℝ) ^ ((11 : ℝ) / 16) / 2 := by
      have hsplit : (x : ℝ) ^ ((11 : ℝ) / 16)
          = (x : ℝ) ^ ((73 : ℝ) / 200) * (x : ℝ) ^ ((129 : ℝ) / 400) := by
        rw [← Real.rpow_add hxpos, show (73 : ℝ) / 200 + 129 / 400 = 11 / 16 by norm_num]
      have hm : 8 * Real.exp 1 * (x : ℝ) ^ ((129 : ℝ) / 400)
          ≤ (x : ℝ) ^ ((73 : ℝ) / 200) * (x : ℝ) ^ ((129 : ℝ) / 400) :=
        mul_le_mul_of_nonneg_right hE2 (Real.rpow_nonneg hx0 ((129 : ℝ) / 400))
      rw [hsplit]
      linarith
    have hcast : ((Deltac x * ⌊Real.exp 1 * Yc x B⌋₊ : ℕ) : ℝ)
        = (Deltac x : ℝ) * (⌊Real.exp 1 * Yc x B⌋₊ : ℝ) := by
      push_cast
      ring
    have hgoal : ((Deltac x * ⌊Real.exp 1 * Yc x B⌋₊ : ℕ) : ℝ) ≤ (Dc x : ℝ) := by
      rw [hcast]
      exact le_trans (le_trans hall (le_of_eq hval)) (le_trans hbound hDl)
    exact_mod_cast hgoal
  -- 16
  have hC16 : 1 ≤ ⌊sc x B * zc x B⌋₊ := by
    have hzc1 : (1 : ℝ) ≤ zc x B := by
      rw [hzc_eq]
      exact_mod_cast (le_trans (by norm_num : 1 ≤ 256) hC1)
    have h : (1 : ℝ) * 1 ≤ sc x B * zc x B :=
      mul_le_mul hsc_one hzc1 (by norm_num) (le_trans zero_le_one hsc_one)
    refine Nat.le_floor ?_
    push_cast
    linarith [h]
  exact ⟨hC1, hC2, hC3, hC4, hC5, hC6, hC7, hC8, hC9, hC10, hC11, hC12, hC13, hC14, hC15, hC16⟩

end

end Work.FIChain
