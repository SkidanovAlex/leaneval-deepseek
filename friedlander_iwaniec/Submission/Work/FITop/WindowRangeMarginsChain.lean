import Mathlib
import Submission.Work.FITop.Defs
import Submission.ASP.S7c
import Submission.ASP.S8b
import Submission.ASP.S20
import Submission.ASP.S21
import Submission.ASP.S22
import Submission.ASP.S23
import Submission.ASP.S24
import Submission.ASP.S25
import Submission.Work.FITop.RangeCheckChain

set_option autoImplicit false

namespace Work.FITop

open Filter

noncomputable section

/-! ## Elementary eventualities -/

/-- `2 ≤ loglog x` eventually. -/
private lemma WA_ev_loglog_ge_two :
    ∀ᶠ x : ℕ in atTop, 2 ≤ Real.log (Real.log (x : ℝ)) := by
  filter_upwards [FI_ev_log_ge_nat (Real.exp (Real.exp 2))] with x hx
  have h := Real.log_le_log (Real.exp_pos (Real.exp 2)) hx
  rw [Real.log_exp] at h
  linarith [Real.add_one_le_exp 2]

/-- `2 ≤ Pcut x` eventually. -/
private lemma WA_ev_Pcut_ge_two : ∀ᶠ x : ℕ in atTop, 2 ≤ Pcut x := by
  filter_upwards [WA_ev_loglog_ge_two] with x hx
  have h1 : (1 : ℝ) ≤ Real.log (Real.log (x : ℝ)) := by linarith
  have h2 : (1 : ℝ) ≤ (Real.log (Real.log (x : ℝ))) ^ 2 := one_le_pow₀ h1
  have h3 : Real.exp 1 ≤ Real.exp ((Real.log (Real.log (x : ℝ))) ^ 2) := Real.exp_le_exp.mpr h2
  have h4 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have h5 : (2 : ℝ) ≤ (Pcut x : ℝ) := le_trans h4 (le_trans h3 (FI_Pcut_ge x))
  exact_mod_cast h5

/-! ## The top margin `2·(s·e·Y) + 1 ≤ √x` -/

private lemma WA_ev_top_margin :
    ∀ᶠ x : ℕ in atTop,
      2 * (s1 x * (Real.exp 1 * Y1 x)) + 1 ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
  filter_upwards [FI_ev_s1_le_two_W1, FI_ev_W1_upper, FI_ev_Y1_upper,
    FI_ev_rpow_ge_nat ((1 : ℝ) / 100) (by norm_num) (Real.exp 1 + 1),
    FI_ev_rpow_ge_nat ((49 : ℝ) / 100) (by norm_num) 1, FI_ev_ge_one]
    with x hs1 hWu hYu hx1 hx49 hxge
  have hxpos : (0 : ℝ) < x := FI_cast_pos hxge
  have hYnn : 0 ≤ Y1 x := FI_Y1_nonneg x
  have hs1' : s1 x ≤ (1 / 2) * (x : ℝ) ^ ((5 : ℝ) / 32) := by
    have h2 := mul_le_mul_of_nonneg_left hWu (by norm_num : (0 : ℝ) ≤ 2)
    calc s1 x ≤ 2 * W1 x := hs1
      _ ≤ 2 * ((1 / 4) * (x : ℝ) ^ ((5 : ℝ) / 32)) := h2
      _ = (1 / 2) * (x : ℝ) ^ ((5 : ℝ) / 32) := by ring
  have hprod : s1 x * (Real.exp 1 * Y1 x)
      ≤ (Real.exp 1 / 2) * (x : ℝ) ^ ((49 : ℝ) / 100) := by
    have h1 : s1 x * Y1 x
        ≤ (1 / 2) * (x : ℝ) ^ ((5 : ℝ) / 32) * (x : ℝ) ^ ((267 : ℝ) / 800) :=
      mul_le_mul hs1' hYu hYnn (by positivity)
    have halg : (1 / 2) * (x : ℝ) ^ ((5 : ℝ) / 32) * (x : ℝ) ^ ((267 : ℝ) / 800)
        = (1 / 2) * (x : ℝ) ^ ((49 : ℝ) / 100) := by
      rw [show (1 / 2) * (x : ℝ) ^ ((5 : ℝ) / 32) * (x : ℝ) ^ ((267 : ℝ) / 800)
            = (1 / 2) * ((x : ℝ) ^ ((5 : ℝ) / 32) * (x : ℝ) ^ ((267 : ℝ) / 800)) by ring]
      rw [← Real.rpow_add hxpos]
      congr 1
      norm_num
    rw [halg] at h1
    calc s1 x * (Real.exp 1 * Y1 x) = Real.exp 1 * (s1 x * Y1 x) := by ring
      _ ≤ Real.exp 1 * ((1 / 2) * (x : ℝ) ^ ((49 : ℝ) / 100)) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos 1).le
      _ = (Real.exp 1 / 2) * (x : ℝ) ^ ((49 : ℝ) / 100) := by ring
  have h2 : 2 * (s1 x * (Real.exp 1 * Y1 x)) ≤ Real.exp 1 * (x : ℝ) ^ ((49 : ℝ) / 100) := by
    calc 2 * (s1 x * (Real.exp 1 * Y1 x))
        ≤ 2 * ((Real.exp 1 / 2) * (x : ℝ) ^ ((49 : ℝ) / 100)) :=
          mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = Real.exp 1 * (x : ℝ) ^ ((49 : ℝ) / 100) := by ring
  have hsplit : (x : ℝ) ^ ((1 : ℝ) / 2)
      = (x : ℝ) ^ ((1 : ℝ) / 100) * (x : ℝ) ^ ((49 : ℝ) / 100) := by
    rw [← Real.rpow_add hxpos]
    congr 1
    norm_num
  have hstep1 : Real.exp 1 * (x : ℝ) ^ ((49 : ℝ) / 100) + 1
      ≤ (Real.exp 1 + 1) * (x : ℝ) ^ ((49 : ℝ) / 100) := by
    have ht : (1 : ℝ) ≤ (x : ℝ) ^ ((49 : ℝ) / 100) := hx49
    nlinarith [ht]
  have hstep2 : (Real.exp 1 + 1) * (x : ℝ) ^ ((49 : ℝ) / 100)
      ≤ (x : ℝ) ^ ((1 : ℝ) / 100) * (x : ℝ) ^ ((49 : ℝ) / 100) :=
    mul_le_mul_of_nonneg_right hx1 (Real.rpow_nonneg hxpos.le _)
  calc 2 * (s1 x * (Real.exp 1 * Y1 x)) + 1
      ≤ Real.exp 1 * (x : ℝ) ^ ((49 : ℝ) / 100) + 1 := by linarith [h2]
    _ ≤ (Real.exp 1 + 1) * (x : ℝ) ^ ((49 : ℝ) / 100) := hstep1
    _ ≤ (x : ℝ) ^ ((1 : ℝ) / 100) * (x : ℝ) ^ ((49 : ℝ) / 100) := hstep2
    _ = (x : ℝ) ^ ((1 : ℝ) / 2) := hsplit.symm

/-! ## The bottom margin `x^{1/4+η} + 2 < Y/Δ` -/

private lemma WA_ev_bottom_margin (η : ℝ) (hη2 : η < 1 / 16) :
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) ^ ((1 : ℝ) / 4 + η) + 2 < Y1 x / (Delta1 x : ℝ) := by
  filter_upwards [FI_ev_Y1_lower, FI_ev_Delta1_le_two_Lam1, FI_ev_Lam1_ge_one,
    FI_ev_rpow_ge_nat ((5 : ℝ) / 16) (by norm_num) 3,
    FI_ev_rpow_ge_nat ((9 : ℝ) / 800) (by norm_num) 8, FI_ev_ge_one]
    with x hY hD2 hLam hx5 hx9 hxge
  have hxpos : (0 : ℝ) < x := FI_cast_pos hxge
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := FI_cast_one_le hxge
  have hDpos : 0 < (Delta1 x : ℝ) :=
    lt_of_lt_of_le zero_lt_one (le_trans hLam (FI_Lam1_le_Delta1 x))
  have hLam_inv : (Lam1 x)⁻¹ = (x : ℝ) ^ (-((1 : ℝ) / 100)) := by
    rw [Lam1, ← Real.rpow_neg (le_of_lt hxpos) ((1 : ℝ) / 100)]
  have halg : ((x : ℝ) ^ ((267 : ℝ) / 800) / 2) / (2 * Lam1 x)
      = (1 / 4) * (x : ℝ) ^ ((259 : ℝ) / 800) := by
    have hpe : (x : ℝ) ^ ((267 : ℝ) / 800) * (x : ℝ) ^ (-((1 : ℝ) / 100))
        = (x : ℝ) ^ ((259 : ℝ) / 800) := by
      rw [← Real.rpow_add hxpos]
      congr 1
      norm_num
    calc ((x : ℝ) ^ ((267 : ℝ) / 800) / 2) / (2 * Lam1 x)
        = ((x : ℝ) ^ ((267 : ℝ) / 800) * (Lam1 x)⁻¹) / 4 := by ring
      _ = ((x : ℝ) ^ ((267 : ℝ) / 800) * (x : ℝ) ^ (-((1 : ℝ) / 100))) / 4 := by
            rw [hLam_inv]
      _ = ((x : ℝ) ^ ((259 : ℝ) / 800)) / 4 := by rw [hpe]
      _ = (1 / 4) * (x : ℝ) ^ ((259 : ℝ) / 800) := by ring
  have hA : (1 / 4) * (x : ℝ) ^ ((259 : ℝ) / 800) ≤ Y1 x / (Delta1 x : ℝ) := by
    have h1 : ((x : ℝ) ^ ((267 : ℝ) / 800) / 2) / (2 * Lam1 x) ≤ Y1 x / (2 * Lam1 x) :=
      div_le_div_of_nonneg_right hY (by linarith [hLam])
    have h2 : Y1 x / (2 * Lam1 x) ≤ Y1 x / (Delta1 x : ℝ) :=
      div_le_div_of_nonneg_left (FI_Y1_nonneg x) hDpos hD2
    rw [halg] at h1
    linarith
  have hsplit : (x : ℝ) ^ ((259 : ℝ) / 800)
      = (x : ℝ) ^ ((5 : ℝ) / 16) * (x : ℝ) ^ ((9 : ℝ) / 800) := by
    rw [← Real.rpow_add hxpos]
    congr 1
    norm_num
  have hB : (x : ℝ) ^ ((1 : ℝ) / 4 + η) + 2 < (1 / 4) * (x : ℝ) ^ ((259 : ℝ) / 800) := by
    have hle : (x : ℝ) ^ ((1 : ℝ) / 4 + η) ≤ (x : ℝ) ^ ((5 : ℝ) / 16) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hApos : (0 : ℝ) ≤ (x : ℝ) ^ ((5 : ℝ) / 16) := Real.rpow_nonneg hxpos.le _
    rw [hsplit]
    have hs1 : (x : ℝ) ^ ((1 : ℝ) / 4 + η) + 2 < 2 * (x : ℝ) ^ ((5 : ℝ) / 16) := by
      linarith [hle, hx5]
    have hs2 : 2 * (x : ℝ) ^ ((5 : ℝ) / 16)
        ≤ (1 / 4) * ((x : ℝ) ^ ((5 : ℝ) / 16) * (x : ℝ) ^ ((9 : ℝ) / 800)) := by
      have h2 : (2 : ℝ) ≤ (1 / 4) * (x : ℝ) ^ ((9 : ℝ) / 800) := by linarith [hx9]
      calc 2 * (x : ℝ) ^ ((5 : ℝ) / 16)
          ≤ ((1 / 4) * (x : ℝ) ^ ((9 : ℝ) / 800)) * (x : ℝ) ^ ((5 : ℝ) / 16) :=
            mul_le_mul_of_nonneg_right h2 hApos
        _ = (1 / 4) * ((x : ℝ) ^ ((5 : ℝ) / 16) * (x : ℝ) ^ ((9 : ℝ) / 800)) := by ring
    linarith [hs1, hs2]
  linarith [hA, hB]

/-- The window range of the `Lam1 = x^{1/100}` family (`Y1, Delta1, s1, Pcut`) **with margins**:
a `+2` margin at the bottom end, the margin `2·(s1 x · e · Y1 x) + 1 ≤ √x` at the top, and the
two elementary `Pcut`/`loglog` eventualities.  This is the `Delta1` analogue of the proved
`Work.FITop.WindowRangeMargins` (`Submission/Work/FITop/WindowRangeMargins.lean`, which is the
`Lam0`/`Delta0`/`Y0`/`s0` family with `η < 3/32`, `B ≤ 2^31`); here `η < 1/16` and `B > 0` is
arbitrary.

Proof route (adapt `WindowRangeMargins.lean`, whose proof is self-contained and relies only on
elementary asymptotics; alternatively reuse the proved `RangeCheckChain` conjuncts `RangeC1`,
`RangeC2` and the `Pcut`/`loglog` lemmas `RangeC3`, `RangeC4`, `RangeC9` and strengthen them):
* `Y1 x / Delta1 x ≍ x^{11/32 - 1/100} = x^{267/800}` while `x^{1/4+η} ≤ x^{5/16}`, so the bottom
  inequality with the `+2` margin holds for large `x` (the exponent gap `267/800 - 5/16 > 0`);
* `s1 x ≈ √x/(8 δ √D)` with `δ = (log x)²`, `√D = x^{11/32}`, so
  `s1 x · e · Y1 x ≈ e√x/(8 (log x)² x^{1/100}) ≪ √x (log x)^{-B}` for every fixed `B > 0`,
  and `2·(s1 x · e · Y1 x) + 1 ≤ √x`;
* `2 ≤ Pcut x`, `(loglog x)² ≤ log (Pcut x)` and
  `log (Pcut x) ≤ (log x)(loglog x)^{-2}` are the `Pcut` facts, and `3 ≤ x`, `2 ≤ loglog x` are
  elementary eventualities. -/
theorem WindowRangeMarginsChain (η B : ℝ) (hη : 0 < η) (hη2 : η < 1 / 16) (hB : 0 < B) :
    ∀ᶠ x : ℕ in Filter.atTop,
      (x : ℝ) ^ ((1 : ℝ) / 4 + η) + 2 < Y1 x / (Delta1 x : ℝ) ∧
      s1 x * (Real.exp 1 * Y1 x) < (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-B) ∧
      2 * (s1 x * (Real.exp 1 * Y1 x)) + 1 ≤ (x : ℝ) ^ ((1 : ℝ) / 2) ∧
      2 ≤ Pcut x ∧
      (Real.log (Real.log (x : ℝ))) ^ 2 ≤ Real.log (Pcut x : ℝ) ∧
      Real.log (Pcut x : ℝ) ≤ Real.log (x : ℝ) * (Real.log (Real.log (x : ℝ))) ^ (-2 : ℤ) ∧
      (3 : ℝ) ≤ (x : ℝ) ∧ 2 ≤ Real.log (Real.log (x : ℝ)) := by
  filter_upwards [WA_ev_bottom_margin η hη2, RangeCheckChain η B hη hη2 hB,
    WA_ev_top_margin, WA_ev_Pcut_ge_two, eventually_ge_atTop 3, WA_ev_loglog_ge_two]
    with x h1 hRC h3 h4 h7 h8
  exact ⟨h1, hRC.2.1, h3, h4, hRC.2.2.1, hRC.2.2.2.1, by exact_mod_cast h7, h8⟩

end

end Work.FITop
