/-
# `Submission.Work.FIChain.Yc_lower_sharp` — the sharp lower bound for the outer scale `Yc`

The `B`-dependent family of `Submission/Work/FIChain/Defs.lean` has

  `Yc x B = √x / (sc x B · (log x)^{B+2})`,

where `sc x B = 2^{Jc x B}` is the power of two *just below* `x^{1/4-2η_c}/(2(log x)^{B+2})`
(`η_c = 1/32`).  The dyadic ceiling gives the upper half of the sandwich

  `sc x B · (log x)^{B+2} ≤ x^{3/16}`   (eventually),

whence

  `x^{5/16} = √x / x^{3/16} ≤ √x / (sc x B · (log x)^{B+2}) = Yc x B`.

This is the *sharp* lower bound: together with `Yc x B ≤ 2·x^{5/16}` (the mirror estimate, in
`window_marginsC`) it pins `Yc x B ≍ x^{5/16}`, the exponent `5/16 = 1/2 - (1/4 - 2η_c)` being
exactly the `x`-room that the whole endgame chapter consumes.
-/
import Mathlib
import Submission.Work.FIChain.Defs
import Submission.Work.FITop.RCPrelude

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Filter

noncomputable section

/-- The value of the `sc`-exponent: `η_c = 1/32`, so `1/4 - 2η_c = 3/16`. -/
private lemma etac_val : (1 : ℝ) / 4 - 2 * etac = 3 / 16 := by norm_num [etac]

/-- `u = x^{1/4-2η_c}/(2(log x)^{B+2}) ≥ 1` eventually (the point where the dyadic ceiling
becomes lossy only by the factor `2`). -/
private lemma ev_u_ge_one (B : ℝ) :
    ∀ᶠ x : ℕ in Filter.atTop,
      1 ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2)) := by
  filter_upwards [Work.FITop.FI_ev_log_rpow_le_nat (b := B + 2) (ε := (3 : ℝ) / 16)
      (C := 1 / 2) (by norm_num) (by norm_num), eventually_ge_atTop 2] with x hle hx2
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hLpos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  rw [etac_val, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (Real.log (x : ℝ)) ^ (B + 2))]
  linarith

/-- The upper half of the dyadic sandwich: `sc x B · (log x)^{B+2} ≤ x^{3/16}` eventually. -/
private lemma ev_sc_mul_le (B : ℝ) :
    ∀ᶠ x : ℕ in Filter.atTop,
      sc x B * (Real.log (x : ℝ)) ^ (B + 2) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) := by
  filter_upwards [ev_u_ge_one B, eventually_ge_atTop 2] with x hu hx2
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hLpos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hupos : 0 < (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2)) :=
    lt_of_lt_of_le zero_lt_one hu
  have ht : 0 ≤ Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
      / (2 * (Real.log (x : ℝ)) ^ (B + 2))) / Real.log 2 :=
    div_nonneg (Real.log_nonneg hu) (Real.log_pos (by norm_num)).le
  have hceil : ((Jc x B : ℕ) : ℝ) <
      Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
        / (2 * (Real.log (x : ℝ)) ^ (B + 2))) / Real.log 2 + 1 := by
    rw [Jc]; exact Nat.ceil_lt_add_one ht
  have hpow : (2 : ℝ) ^ (Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
      / (2 * (Real.log (x : ℝ)) ^ (B + 2))) / Real.log 2)
      = (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2)) :=
    Work.FITop.FI_two_rpow_log_div_log _ hupos
  have hsc_le : sc x B ≤ 2 * ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
      / (2 * (Real.log (x : ℝ)) ^ (B + 2))) := by
    calc sc x B = (2 : ℝ) ^ (((Jc x B : ℕ) : ℝ)) := by rw [sc, Real.rpow_natCast]
      _ ≤ (2 : ℝ) ^ (Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
            / (2 * (Real.log (x : ℝ)) ^ (B + 2))) / Real.log 2 + 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hceil.le
      _ = 2 * ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2))) := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one, hpow]; ring
  calc sc x B * (Real.log (x : ℝ)) ^ (B + 2)
      ≤ 2 * ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2)))
          * (Real.log (x : ℝ)) ^ (B + 2) :=
        mul_le_mul_of_nonneg_right hsc_le (Real.rpow_nonneg hLpos.le _)
    _ = (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) := by
        field_simp

theorem Yc_lower_sharp (B : ℝ) (hB : 0 < B) :
    ∀ᶠ x : ℕ in Filter.atTop, (x : ℝ) ^ ((5 : ℝ) / 16) ≤ Work.FIChain.Yc x B := by
  filter_upwards [ev_sc_mul_le B, eventually_ge_atTop 2] with x hsc hx2
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hxpos : (0 : ℝ) < x := by linarith
  have hLpos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hLp_pos : 0 < (Real.log (x : ℝ)) ^ (B + 2) := Real.rpow_pos_of_pos hLpos _
  have hsc_pos : 0 < sc x B := by rw [sc]; positivity
  have hden_pos : 0 < sc x B * (Real.log (x : ℝ)) ^ (B + 2) := mul_pos hsc_pos hLp_pos
  have hmain : Real.sqrt (x : ℝ) / (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
      ≤ Real.sqrt (x : ℝ) / (sc x B * (Real.log (x : ℝ)) ^ (B + 2)) :=
    div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hden_pos hsc
  have heq : Real.sqrt (x : ℝ) / (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
      = (x : ℝ) ^ ((5 : ℝ) / 16) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hxpos]
    congr 1
    norm_num [etac]
  calc (x : ℝ) ^ ((5 : ℝ) / 16)
      = Real.sqrt (x : ℝ) / (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) := heq.symm
    _ ≤ Real.sqrt (x : ℝ) / (sc x B * (Real.log (x : ℝ)) ^ (B + 2)) := hmain
    _ = Yc x B := rfl

end

end Work.FIChain
