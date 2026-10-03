/-
# The numeric core of the non-aliasing of `diffFreqs ρ l` at the repaired window

`Work.KMTAreas.A7.lp_T_le`: in the second regime `l > iwC0 ρ` (`ρ ≤ 1/8`) the bound
`T = Q_0^{(l)} · (2^l)^{D_ρ^2}` on the denominators of `iwP ρ l` satisfies
`4 T² ≤ 2^{2·2^{2ρl}}`, which is at most `2^{2du}` at the repaired window (because `d·u ≥ 2^{2ρl}`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LpNonAliasAux

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

open scoped BigOperators
open Work.Analysis.IonescuWainger

noncomputable section

/-- `(a^y)^m = a^(y·m)` for `a ≥ 0`. -/
lemma lp_rpow_pow (a y : ℝ) (ha : 0 ≤ a) (m : ℕ) : (a ^ y) ^ m = a ^ (y * m) := by
  rw [← Real.rpow_natCast (a ^ y) m, ← Real.rpow_mul ha y (m : ℝ)]

/-- **Elementary numeric core.**  For `x ≥ 16`, `6x²2^x + 2.25x⁴ + 1 ≤ 2^{4x}`. -/
lemma lp_numeric_core {x : ℝ} (hx : 16 ≤ x) :
    6 * x ^ 2 * (2 : ℝ) ^ x + 2.25 * x ^ 4 + 1 ≤ (2 : ℝ) ^ (4 * x) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx1sq : (1 : ℝ) ≤ x ^ 2 := one_le_pow₀ hx1
  have hx1four : (1 : ℝ) ≤ x ^ 4 := one_le_pow₀ hx1
  have h3 : (3 * x) ^ 4 / 2 ≤ (2 : ℝ) ^ (3 * x) := lp_two_rpow_ge (3 * x) (by linarith)
  have h4 : (4 * x) ^ 4 / 2 ≤ (2 : ℝ) ^ (4 * x) := lp_two_rpow_ge (4 * x) (by linarith)
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ x := Real.rpow_pos_of_pos (by norm_num) _
  have hA : 6 * x ^ 2 * (2 : ℝ) ^ x ≤ (2 : ℝ) ^ (4 * x) / 3 := by
    have hsplit : (2 : ℝ) ^ (4 * x) = (2 : ℝ) ^ (3 * x) * (2 : ℝ) ^ x := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    have key : 18 * x ^ 2 ≤ (2 : ℝ) ^ (3 * x) := by
      have h40 : (40.5 : ℝ) * x ^ 4 = (3 * x) ^ 4 / 2 := by ring
      nlinarith [h3, h40, hx1sq]
    calc 6 * x ^ 2 * (2 : ℝ) ^ x
        = (18 * x ^ 2 * (2 : ℝ) ^ x) / 3 := by ring
      _ ≤ ((2 : ℝ) ^ (3 * x) * (2 : ℝ) ^ x) / 3 := by
          refine div_le_div_of_nonneg_right ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_right key (le_of_lt h2pos)
      _ = (2 : ℝ) ^ (4 * x) / 3 := by rw [hsplit]
  have hB : 2.25 * x ^ 4 + 1 ≤ 2 * (2 : ℝ) ^ (4 * x) / 3 := by
    have h128 : (128 : ℝ) * x ^ 4 = (4 * x) ^ 4 / 2 := by ring
    have key : 128 * x ^ 4 ≤ (2 : ℝ) ^ (4 * x) := by linarith [h4, h128]
    nlinarith [key, hx1four]
  have hC : (1 : ℝ) ≤ (2 : ℝ) ^ (4 * x) / 3 := by
    have h2 : (3 : ℝ) ≤ (2 : ℝ) ^ (4 * x) := by
      have h2' : (2 : ℝ) ^ ((32 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (4 * x) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
      have h3' : (3 : ℝ) ≤ (2 : ℝ) ^ ((32 : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]; norm_num
      linarith
    linarith
  linarith [hA, hB, hC]

/-- `4 T² ≤ 2^Z` from `T ≤ 2^K` and `2K + 2 ≤ Z` (for `T ≥ 0`). -/
lemma lp_sq_le {T K Z : ℝ} (hT : 0 ≤ T) (hK : T ≤ (2 : ℝ) ^ K) (hZK : 2 * K + 2 ≤ Z) :
    4 * T ^ 2 ≤ (2 : ℝ) ^ Z := by
  have h3 : ((2 : ℝ) ^ K) ^ 2 = (2 : ℝ) ^ (K + K) := by
    rw [lp_rpow_pow (2 : ℝ) K (by norm_num) 2]
    congr 1
    push_cast
    ring
  have h1 : T ^ 2 ≤ (2 : ℝ) ^ (K + K) := by
    have h2 : T ^ 2 ≤ ((2 : ℝ) ^ K) ^ 2 := by
      rw [sq, sq]
      exact mul_self_le_mul_self hT hK
    rwa [h3] at h2
  have h4 : (4 : ℝ) = (2 : ℝ) ^ ((2 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    norm_num
  have h5 : 4 * ((2 : ℝ) ^ (K + K)) = (2 : ℝ) ^ (K + K + 2) := by
    rw [h4, (Real.rpow_add (by norm_num : (0 : ℝ) < 2) ((2 : ℕ) : ℝ) (K + K)).symm]
    congr 1
    push_cast
    ring
  calc 4 * T ^ 2 ≤ 4 * (2 : ℝ) ^ (K + K) := by linarith
    _ = (2 : ℝ) ^ (K + K + 2) := h5
    _ ≤ (2 : ℝ) ^ Z := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- **The denominator bound `T` in the second regime.**  For `ρ ≤ 1/8` and `l > iwC0 ρ`,
`4 T² ≤ 2^{2·2^{2ρl}}` with `T = Q_0^{(l)}·(2^l)^{D_ρ^2}`. -/
lemma lp_T_le {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 8) {l : ℕ} (hl : iwC0 ρ < l) :
    4 * (((iwQ0 ρ l * (2 ^ l) ^ (iwD ρ * iwD ρ) : ℕ) : ℝ)) ^ 2
      ≤ (2 : ℝ) ^ (2 * (2 : ℝ) ^ (2 * ρ * (l : ℝ))) := by
  set x : ℝ := ρ * (l : ℝ) / 2 with hx
  have hlR : (iwC0 ρ : ℝ) < (l : ℝ) := by exact_mod_cast hl
  have hxgt : 2 / ρ < x := by
    have h1 : 4 / ρ ^ 2 < (l : ℝ) := lt_of_le_of_lt (lp_iwC0_ge hρ) hlR
    have h1' : 4 < (l : ℝ) * ρ ^ 2 := by
      rwa [div_lt_iff₀ (by positivity : (0 : ℝ) < ρ ^ 2)] at h1
    rw [hx, div_lt_iff₀ hρ]
    nlinarith
  have h2ρ : 2 / ρ ≥ 16 := by
    rw [ge_iff_le, le_div_iff₀ hρ]
    linarith
  have hx16 : 16 ≤ x := le_trans h2ρ (le_of_lt hxgt)
  have hρx : 2 < x * ρ := by
    have h : 1 / ρ < x / 2 := by
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have hid : (2 : ℝ) / ρ = 1 / ρ * 2 := by ring
      linarith [hxgt]
    have h2 : 1 / ρ * ρ < x / 2 * ρ := mul_lt_mul_of_pos_right h hρ
    rw [div_mul_cancel₀ 1 (ne_of_gt hρ)] at h2
    linarith
  have hD : (iwD ρ : ℝ) ≤ 3 * x / 2 := by
    have h1 := lp_iwD_le ρ hρ
    have h2 : (1 : ℝ) ≤ x / 2 := by linarith
    have h3 : 2 / ρ + 1 < x + 1 := by linarith
    have h4 : x + 1 ≤ 3 * x / 2 := by linarith
    linarith
  have hl_le : (l : ℝ) ≤ x ^ 2 := by
    have h2x : (l : ℝ) = 2 * x / ρ := by
      rw [hx]
      field_simp
    rw [h2x, div_le_iff₀ hρ]
    nlinarith [hρx, le_of_lt (by positivity : (0 : ℝ) < x)]
  have hn0 : ((iwN0 ρ l : ℕ) : ℝ) ≤ (2 : ℝ) ^ (x + 1) := by
    have h := lp_iwN0_le_two ρ hρ.le l
    have hy : (2 : ℝ) ^ (ρ * (l : ℝ) / 2) = (2 : ℝ) ^ x := by rw [hx]
    rw [hy] at h
    calc (iwN0 ρ l : ℝ) ≤ 2 * (2 : ℝ) ^ x := h
      _ = (2 : ℝ) ^ (x + 1) := by
          rw [Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)]
          ring
  have hQ : (iwQ0 ρ l : ℝ) ≤ ((iwN0 ρ l : ℕ) : ℝ) ^ (iwN0 ρ l * iwD ρ) := by
    have := lp_iwQ0_le ρ l
    exact_mod_cast this
  set T : ℝ := ((iwQ0 ρ l * (2 ^ l) ^ (iwD ρ * iwD ρ) : ℕ) : ℝ) with hTdef
  have hT1 : T ≤ ((iwN0 ρ l : ℕ) : ℝ) ^ (iwN0 ρ l * iwD ρ)
      * ((2 : ℝ) ^ l) ^ (iwD ρ * iwD ρ) := by
    rw [hTdef]
    push_cast
    exact mul_le_mul hQ le_rfl (by positivity) (by positivity)
  set K : ℝ := (x + 1) * ((iwN0 ρ l : ℕ) : ℝ) * (iwD ρ : ℝ)
    + (l : ℝ) * ((iwD ρ : ℝ)) ^ 2 with hK
  have hDnn : (0 : ℝ) ≤ (iwD ρ : ℝ) := by positivity
  have hT2 : ((iwN0 ρ l : ℕ) : ℝ) ^ (iwN0 ρ l * iwD ρ)
        * ((2 : ℝ) ^ l) ^ (iwD ρ * iwD ρ) ≤ (2 : ℝ) ^ K := by
    have h1 : ((iwN0 ρ l : ℕ) : ℝ) ^ (iwN0 ρ l * iwD ρ)
        ≤ (2 : ℝ) ^ ((x + 1) * ((iwN0 ρ l : ℕ) : ℝ) * (iwD ρ : ℝ)) := by
      have hstep : ((iwN0 ρ l : ℕ) : ℝ) ^ (iwN0 ρ l * iwD ρ)
          ≤ ((2 : ℝ) ^ (x + 1)) ^ (iwN0 ρ l * iwD ρ) :=
        pow_le_pow_left₀ (by positivity) hn0 _
      have hp := lp_rpow_pow (2 : ℝ) (x + 1) (by norm_num) (iwN0 ρ l * iwD ρ)
      rw [hp] at hstep
      refine hstep.trans ?_
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hcast : (((iwN0 ρ l) * iwD ρ : ℕ) : ℝ)
          = ((iwN0 ρ l : ℕ) : ℝ) * (iwD ρ : ℝ) := by push_cast; ring
      rw [hcast]
      nlinarith [hn0, hDnn, hx16]
    have h2 : ((2 : ℝ) ^ l) ^ (iwD ρ * iwD ρ)
        = (2 : ℝ) ^ ((l : ℝ) * (iwD ρ : ℝ) ^ 2) := by
      rw [← Real.rpow_natCast (2 : ℝ) l]
      rw [lp_rpow_pow (2 : ℝ) (l : ℝ) (by norm_num) (iwD ρ * iwD ρ)]
      congr 1
      push_cast
      ring
    have hmul : ((iwN0 ρ l : ℕ) : ℝ) ^ (iwN0 ρ l * iwD ρ) * ((2 : ℝ) ^ l) ^ (iwD ρ * iwD ρ)
        ≤ (2 : ℝ) ^ ((x + 1) * ((iwN0 ρ l : ℕ) : ℝ) * (iwD ρ : ℝ))
          * (2 : ℝ) ^ ((l : ℝ) * (iwD ρ : ℝ) ^ 2) := by
      refine mul_le_mul h1 ?_ (by positivity) (by positivity)
      rw [h2]
    rw [hK]
    refine hmul.trans (le_of_eq ?_)
    exact (Real.rpow_add (by norm_num : (0 : ℝ) < 2)
      ((x + 1) * ((iwN0 ρ l : ℕ) : ℝ) * (iwD ρ : ℝ)) ((l : ℝ) * (iwD ρ : ℝ) ^ 2)).symm
  have hTle : T ≤ (2 : ℝ) ^ K := hT1.trans hT2
  have hKbound : 2 * K + 2 ≤ 2 * (2 : ℝ) ^ (2 * ρ * (l : ℝ)) := by
    have h4x : (2 : ℝ) ^ (4 * x) = (2 : ℝ) ^ (2 * ρ * (l : ℝ)) := by
      congr 1
      rw [hx]
      ring
    have h3 : (x + 1) * ((iwN0 ρ l : ℕ) : ℝ) * (iwD ρ : ℝ) ≤ 6 * x ^ 2 * (2 : ℝ) ^ x := by
      have h2x : (2 : ℝ) ^ (x + 1) = 2 * (2 : ℝ) ^ x := by
        rw [Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)]
        ring
      have hstep : (x + 1) * ((iwN0 ρ l : ℕ) : ℝ) * (iwD ρ : ℝ)
          ≤ (x + 1) * (2 : ℝ) ^ (x + 1) * (iwD ρ : ℝ) := by
        have h := mul_le_mul_of_nonneg_right hn0 (by positivity : (0 : ℝ) ≤ (iwD ρ : ℝ))
        nlinarith
      have hkey : (x + 1) * (iwD ρ : ℝ) ≤ 3 * x ^ 2 := by
        have h1 : (x + 1) * (iwD ρ : ℝ) ≤ (x + 1) * (3 * x / 2) :=
          mul_le_mul_of_nonneg_left hD (by linarith)
        nlinarith [h1, hx16]
      rw [h2x] at hstep
      nlinarith [hstep, hkey, show (0:ℝ) < (2:ℝ)^x from Real.rpow_pos_of_pos (by norm_num) _]
    have h4 : (l : ℝ) * ((iwD ρ : ℝ)) ^ 2 ≤ 2.25 * x ^ 4 := by
      have hD2 : ((iwD ρ : ℝ)) ^ 2 ≤ (3 * x / 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hD 2
      have h := mul_le_mul hl_le hD2 (by positivity) (by positivity)
      nlinarith [h]
    have hcore := lp_numeric_core hx16
    rw [h4x] at hcore
    rw [hK]
    linarith
  exact lp_sq_le (by positivity) hTle hKbound

end

end Work.KMTAreas.A7
