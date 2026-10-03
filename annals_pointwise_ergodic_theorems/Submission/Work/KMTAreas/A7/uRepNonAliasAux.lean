/-
# Auxiliary estimates for `Work.KMTAreas.A7.uRep_nonAliasing`

Two elementary numerical facts used in the proof that the exact-height IW frequency set
`diffFreqs ρ l` is non-aliased at the arc scale `1 - 2·uRep ρ l₁ l₂ k₁ k₂`:

* `lp_numeric_core2` — the strengthened numeric core `6x²2^x + 2.25x⁴ + 2 ≤ 2^{4x}` for
  `x ≥ 16` (the sibling `lp_numeric_core` has the constant `1` on the left; the sharper form
  below is what the exponent `2^{2ρl} - 2` requires);
* `lp_iwC0_ge_sharp` — the sharpened lower bound `4/ρ² + 2/ρ ≤ iwC0 ρ` (the sibling
  `lp_iwC0_ge` has only `4/ρ²`), which produces the bound `x = ρl/2 ≥ 16` in the second
  regime `iwC0 ρ < l`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LpNonAliasNum

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

open scoped BigOperators
open Work.Analysis.IonescuWainger

noncomputable section

/-- **Strengthened elementary numeric core.**  For `x ≥ 16`,
`6x²2^x + 2.25x⁴ + 2 ≤ 2^{4x}`. -/
lemma lp_numeric_core2 {x : ℝ} (hx : 16 ≤ x) :
    6 * x ^ 2 * (2 : ℝ) ^ x + 2.25 * x ^ 4 + 2 ≤ (2 : ℝ) ^ (4 * x) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx1sq : (1 : ℝ) ≤ x ^ 2 := one_le_pow₀ hx1
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
  -- `2.25 x⁴ + 2 ≤ (2/3) 2^{4x}`
  have hB : 2.25 * x ^ 4 + 2 ≤ 2 * (2 : ℝ) ^ (4 * x) / 3 := by
    have h128 : (128 : ℝ) * x ^ 4 = (4 * x) ^ 4 / 2 := by ring
    have key : 128 * x ^ 4 ≤ (2 : ℝ) ^ (4 * x) := by linarith [h4, h128]
    have hbig : (8 : ℝ) ≤ (2 : ℝ) ^ (4 * x) := by
      have h2' : (2 : ℝ) ^ ((64 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (4 * x) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
      have h3' : (8 : ℝ) ≤ (2 : ℝ) ^ ((64 : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]; norm_num
      linarith
    have hx4 : 2.25 * x ^ 4 ≤ (2.25 / 128) * (2 : ℝ) ^ (4 * x) := by
      have hm := mul_le_mul_of_nonneg_left key (by norm_num : (0 : ℝ) ≤ 2.25 / 128)
      linarith
    have htwo : (2 : ℝ) ≤ (1 / 4) * (2 : ℝ) ^ (4 * x) := by linarith
    have hsum : 2.25 * x ^ 4 + 2 ≤ (2.25 / 128 + 1 / 4) * (2 : ℝ) ^ (4 * x) := by
      linarith [hx4, htwo]
    have hcoef : (2.25 / 128 + 1 / 4 : ℝ) ≤ 2 / 3 := by norm_num
    have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ (4 * x) := le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
    calc 2.25 * x ^ 4 + 2 ≤ (2.25 / 128 + 1 / 4) * (2 : ℝ) ^ (4 * x) := hsum
      _ ≤ (2 / 3) * (2 : ℝ) ^ (4 * x) := mul_le_mul_of_nonneg_right hcoef hpos
      _ = 2 * (2 : ℝ) ^ (4 * x) / 3 := by ring
  linarith [hA, hB]

/-- **Sharpened lower bound for `iwC0 ρ`**: `4/ρ² + 2/ρ ≤ iwC0 ρ`. -/
lemma lp_iwC0_ge_sharp {ρ : ℝ} (hρ : 0 < ρ) : 4 / ρ ^ 2 + 2 / ρ ≤ (iwC0 ρ : ℝ) := by
  have hε := lp_iwEps_pos hρ
  have hεle := lp_iwEps_le hρ
  have h1 : (2 / ρ) * ((1 + iwEps ρ) / iwEps ρ) ≤ (iwC0 ρ : ℝ) := by
    rw [iwC0]
    have h := Nat.le_ceil ((2 / ρ) * ((1 + iwEps ρ) / iwEps ρ))
    push_cast
    linarith
  have h2 : (2 / ρ) * ((1 + iwEps ρ) / iwEps ρ) = (2 / ρ) * (1 / iwEps ρ + 1) := by
    rw [add_div, div_self (ne_of_gt hε)]
  have hinv : 2 / ρ ≤ 1 / iwEps ρ := by
    rw [le_div_iff₀ hε]
    rw [div_mul_eq_mul_div, div_le_iff₀ hρ]
    nlinarith
  rw [h2] at h1
  have h3 : (2 / ρ) * (2 / ρ + 1) ≤ (2 / ρ) * (1 / iwEps ρ + 1) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  have h4 : 4 / ρ ^ 2 + 2 / ρ = (2 / ρ) * (2 / ρ + 1) := by ring
  rw [h4]
  linarith

/-- `10/ρ + 100 ≤ iwC0 ρ`. -/
lemma lp_iwC0_ge_lin {ρ : ℝ} (hρ : 0 < ρ) : 10 / ρ + 100 ≤ (iwC0 ρ : ℝ) := by
  rw [iwC0]
  have h := Nat.le_ceil (10 / ρ)
  push_cast
  linarith

end

end Work.KMTAreas.A7
