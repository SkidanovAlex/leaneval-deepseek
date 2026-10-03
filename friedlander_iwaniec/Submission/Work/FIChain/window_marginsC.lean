/-
# `Submission.Work.FIChain.window_marginsC` — the window margins of the `B`-dependent family

This file proves the range check for the family `(Yc, sc, Deltac, Pzc)` of
`Submission/Work/FIChain/Defs.lean`:

* `Yc x B = √x / (s·(log x)^{B+2})` with `s = sc x B = 2^{Jc x B}` and
  `Jc x B = ⌈log(x^{1/4-2η_c}/(2(log x)^{B+2}))/log 2⌉₊`, `η_c = 1/32`;
* `Deltac x = ⌈x^{1/100}⌉`;
* `Pzc x = ⌈exp((loglog x)²)⌉`.

Since `s` is the power of two *just below* `x^{1/4-2η_c}/(2(log x)^{B+2})`, one has the sandwich
`x^{3/16}/2 ≤ sc x B·(log x)^{B+2} < x^{3/16}`, hence
`x^{5/16} < Yc x B ≤ 2·x^{5/16}`.  This is exactly the room needed at the bottom end of the
window: `Yc/Δ > x^{5/16}/(2x^{1/100}) = (1/2)·x^{9/32}·x^{17/800} ≫ x^{9/32}` while
`x^{1/4+η} ≤ x^{9/32}` for `η < 1/32`.  At the top, `sc·(e·Yc) = e√x/(log x)^{B+2}`, which is
`≤ √x/2` for large `x` (any fixed `B > 0`), giving the margin `2sc·e·Yc + 1 ≤ √x`.
-/
import Mathlib
import Submission.Work.FIChain.Defs
import Submission.Work.FITop.WindowRangeMarginsChain

set_option autoImplicit false

namespace Work.FIChain

open Filter

noncomputable section

/-! ## 0. The value `η_c = 1/32` of the exponent -/

private lemma etac_val : (1 : ℝ) / 4 - 2 * etac = 3 / 16 := by norm_num [etac]

/-! ## 1. The sandwich for the dyadic scale

`sc x B` is `2^J` with `J = ⌈log u / log 2⌉₊`, `u = x^{1/4-2η_c}/(2(log x)^{B+2})`; hence
`u ≤ 2^J` and, when `u ≥ 1`, `2^J < 2u`.  Multiplying by `(log x)^{B+2}` gives
`x^{3/16}/2 ≤ sc·(log x)^{B+2} < x^{3/16}`. -/

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

private lemma le_sc (x : ℕ) (B : ℝ) (hx1 : 1 < (x : ℝ)) :
    (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2)) ≤ sc x B := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hLpos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hupos : 0 < (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2)) := by
    apply div_pos (Real.rpow_pos_of_pos hxpos _); positivity
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

/-! ## 2. `Yc` and the product `sc · e · Yc` -/

/-- `Yc x B > x^{5/16}`: from `sc·(log x)^{B+2} < x^{3/16}`. -/
private lemma Yc_lower (x : ℕ) (B : ℝ) (hx1 : 1 < (x : ℝ))
    (hu : 1 ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2))) :
    (x : ℝ) ^ ((5 : ℝ) / 16) < Yc x B := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hLpos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hLp_pos : 0 < (Real.log (x : ℝ)) ^ (B + 2) := Real.rpow_pos_of_pos hLpos _
  have hsc_pos : 0 < sc x B := by rw [sc]; positivity
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

/-- The exact value of the top of the window: `sc·(e·Yc) = e√x/(log x)^{B+2}`. -/
private lemma Yc_mul_exp (x : ℕ) (B : ℝ) (hL : 0 < Real.log (x : ℝ)) :
    sc x B * (Real.exp 1 * Yc x B)
      = Real.exp 1 * Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ (B + 2) := by
  rw [Yc]
  have hsc : sc x B ≠ 0 := by rw [sc]; positivity
  have hLp : (Real.log (x : ℝ)) ^ (B + 2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hL _)
  field_simp

/-! ## 3. Eventualities -/

/-- `u = x^{1/4-2η_c}/(2(log x)^{B+2}) ≥ 1` eventually. -/
private lemma ev_u_ge_one (B : ℝ) :
    ∀ᶠ x : ℕ in Filter.atTop,
      1 ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2)) := by
  filter_upwards [Work.FITop.FI_ev_log_rpow_le_nat (b := B + 2) (ε := (3 : ℝ) / 16)
      (C := 1 / 2) (by norm_num) (by norm_num), eventually_ge_atTop 2] with x hle hx2
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hLpos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  rw [etac_val, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (Real.log (x : ℝ)) ^ (B + 2))]
  linarith

/-- **The bottom margin.** `Yc/Δ > x^{1/4+η} + 2` for `η < 1/32`, eventually. -/
private lemma WM1C (η B : ℝ) (hη : 0 < η) (hη16 : η < 1 / 32) (hB : 0 < B) :
    ∀ᶠ x : ℕ in Filter.atTop,
      (x : ℝ) ^ ((1 : ℝ) / 4 + η) + 2 < Yc x B / (Deltac x : ℝ) := by
  have _ : (0 : ℝ) < B := hB
  filter_upwards [ev_u_ge_one B, Work.FITop.FI_ev_Delta1_le_two_Lam1,
      Work.FITop.FI_ev_Lam1_ge_one,
      Work.FITop.FI_ev_rpow_ge_nat ((17 : ℝ) / 800) (by norm_num) 8,
      Work.FITop.FI_ev_rpow_ge_nat ((9 : ℝ) / 32) (by norm_num) 4,
      eventually_ge_atTop 2] with x hu hΔ2 hLam1 hx17 hx9 hx2
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hxpos : (0 : ℝ) < x := by linarith
  have hYlow : (x : ℝ) ^ ((5 : ℝ) / 16) < Yc x B := Yc_lower x B hx1 hu
  have hΔge : (1 : ℝ) ≤ (Deltac x : ℝ) := le_trans hLam1 (Work.FITop.FI_Lam1_le_Delta1 x)
  have hΔpos : 0 < (Deltac x : ℝ) := lt_of_lt_of_le zero_lt_one hΔge
  have hA1 : (x : ℝ) ^ ((5 : ℝ) / 16) / (2 * Work.FITop.Lam1 x)
      ≤ (x : ℝ) ^ ((5 : ℝ) / 16) / (Deltac x : ℝ) :=
    div_le_div_of_nonneg_left (Real.rpow_nonneg hxpos.le _) hΔpos hΔ2
  have hYdiv : (x : ℝ) ^ ((5 : ℝ) / 16) / (Deltac x : ℝ) < Yc x B / (Deltac x : ℝ) :=
    div_lt_div_of_pos_right hYlow hΔpos
  refine lt_of_lt_of_le ?_ (le_of_lt (lt_of_le_of_lt hA1 hYdiv))
  -- the arithmetic: `x^{1/4+η} + 2 < x^{5/16}/(2·Lam1 x)`
  have hpos9 : 0 < (x : ℝ) ^ ((9 : ℝ) / 32) := Real.rpow_pos_of_pos hxpos _
  have hle_eta : (x : ℝ) ^ ((1 : ℝ) / 4 + η) ≤ (x : ℝ) ^ ((9 : ℝ) / 32) :=
    Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
  have heq : (x : ℝ) ^ ((5 : ℝ) / 16) / (2 * Work.FITop.Lam1 x)
      = (1 / 2) * ((x : ℝ) ^ ((9 : ℝ) / 32) * (x : ℝ) ^ ((17 : ℝ) / 800)) := by
    rw [Work.FITop.Lam1]
    have hxA : 0 < (x : ℝ) ^ ((1 : ℝ) / 100) := Real.rpow_pos_of_pos hxpos _
    have h1 : (x : ℝ) ^ ((5 : ℝ) / 16) / (x : ℝ) ^ ((1 : ℝ) / 100)
        = (x : ℝ) ^ ((9 : ℝ) / 32) * (x : ℝ) ^ ((17 : ℝ) / 800) := by
      rw [← Real.rpow_sub hxpos, ← Real.rpow_add hxpos]
      congr 1; norm_num
    rw [← h1]
    field_simp
  have hprod : 8 * (x : ℝ) ^ ((9 : ℝ) / 32)
      ≤ (x : ℝ) ^ ((9 : ℝ) / 32) * (x : ℝ) ^ ((17 : ℝ) / 800) := by
    calc 8 * (x : ℝ) ^ ((9 : ℝ) / 32) = (x : ℝ) ^ ((9 : ℝ) / 32) * 8 := by ring
      _ ≤ (x : ℝ) ^ ((9 : ℝ) / 32) * (x : ℝ) ^ ((17 : ℝ) / 800) :=
          mul_le_mul_of_nonneg_left hx17 hpos9.le
  rw [heq]
  have h1 : 4 * (x : ℝ) ^ ((9 : ℝ) / 32)
      ≤ (1 / 2) * ((x : ℝ) ^ ((9 : ℝ) / 32) * (x : ℝ) ^ ((17 : ℝ) / 800)) := by
    nlinarith [hprod]
  have h2 : (x : ℝ) ^ ((9 : ℝ) / 32) + 2 < 4 * (x : ℝ) ^ ((9 : ℝ) / 32) := by linarith
  linarith

/-- **The top margin.** `2·(sc · e · Yc) + 1 ≤ √x`, eventually. -/
private lemma WM2C (B : ℝ) (hB : 0 < B) :
    ∀ᶠ x : ℕ in Filter.atTop,
      2 * (sc x B * (Real.exp 1 * Yc x B)) + 1 ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
  have _ : (0 : ℝ) < B := hB
  filter_upwards [Work.FITop.FI_ev_log_ge_nat (4 * Real.exp 1),
      Work.FITop.FI_ev_rpow_ge_nat ((1 : ℝ) / 2) (by norm_num) 4,
      eventually_ge_atTop 2] with x hlog hx4 hx2
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hLpos : 0 < Real.log (x : ℝ) := by linarith [Real.exp_pos 1]
  have hLp_pos : 0 < (Real.log (x : ℝ)) ^ (B + 2) := Real.rpow_pos_of_pos hLpos _
  have hL1 : (1 : ℝ) ≤ Real.log (x : ℝ) := by
    linarith [Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1), Real.exp_pos 1]
  have hLp_ge : 4 * Real.exp 1 ≤ (Real.log (x : ℝ)) ^ (B + 2) := by
    have h2 : Real.log (x : ℝ) ≤ (Real.log (x : ℝ)) ^ (B + 2) := by
      have h := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith : (1 : ℝ) ≤ B + 2)
      rwa [Real.rpow_one] at h
    linarith
  rw [Yc_mul_exp x B hLpos]
  have key : 2 * (Real.exp 1 * Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ (B + 2))
      ≤ Real.sqrt (x : ℝ) / 2 := by
    have hdiv : (2 * Real.exp 1) / (Real.log (x : ℝ)) ^ (B + 2) ≤ 1 / 2 := by
      rw [div_le_iff₀ hLp_pos]; linarith
    calc 2 * (Real.exp 1 * Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ (B + 2))
        = ((2 * Real.exp 1) / (Real.log (x : ℝ)) ^ (B + 2)) * Real.sqrt (x : ℝ) := by
          field_simp
      _ ≤ (1 / 2) * Real.sqrt (x : ℝ) := mul_le_mul_of_nonneg_right hdiv (Real.sqrt_nonneg _)
      _ = Real.sqrt (x : ℝ) / 2 := by ring
  have hsqrt : 2 ≤ Real.sqrt (x : ℝ) := by rw [Real.sqrt_eq_rpow]; linarith
  rw [← Real.sqrt_eq_rpow]
  linarith

/-! ## 4. The statement -/

theorem window_marginsC (η B : ℝ) (hη : 0 < η) (hη16 : η < 1 / 32) (hB : 0 < B) :
    ∀ᶠ x : ℕ in Filter.atTop,
      (x : ℝ) ^ ((1 : ℝ) / 4 + η) + 2 < Work.FIChain.Yc x B / (Work.FIChain.Deltac x : ℝ) ∧
      2 * (Work.FIChain.sc x B * (Real.exp 1 * Work.FIChain.Yc x B)) + 1 ≤ (x : ℝ) ^ ((1 : ℝ) / 2) ∧
      2 ≤ Work.FIChain.Pzc x ∧
      (Real.log (Real.log (x : ℝ))) ^ 2 ≤ Real.log (Work.FIChain.Pzc x : ℝ) ∧
      Real.log (Work.FIChain.Pzc x : ℝ) ≤ Real.log (x : ℝ) * (Real.log (Real.log (x : ℝ))) ^ (-2 : ℤ) ∧
      (3 : ℝ) ≤ (x : ℝ) ∧ 2 ≤ Real.log (Real.log (x : ℝ)) := by
  have hwrm := Work.FITop.WindowRangeMarginsChain η B hη (by linarith) hB
  filter_upwards [WM1C η B hη hη16 hB, WM2C B hB, hwrm] with x h1 h2 h3
  exact ⟨h1, h2, h3.2.2.2.1, h3.2.2.2.2.1, h3.2.2.2.2.2.1,
    h3.2.2.2.2.2.2.1, h3.2.2.2.2.2.2.2⟩

end

end Work.FIChain
