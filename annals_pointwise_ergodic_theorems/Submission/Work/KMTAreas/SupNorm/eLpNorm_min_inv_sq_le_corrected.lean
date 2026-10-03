import Mathlib
import Submission.Work.KMTAreas.SupNorm.integral_Ioi_min_inv_sq_rpow
import Submission.Work.KMTAreas.SupNorm.integrable_min_inv_sq_rpow
import Submission.Work.KMTAreas.SupNorm.min_inv_sq_rpow_algebra_real
import Submission.Port.Aesm

/-!
# `L^p` bound for a function bounded by `min A (B / x ^ 2)` — corrected statement

The sibling file `eLpNorm_min_inv_sq_le.lean` asks for

`eLpNorm E p volume ≤ ofReal (2 * A ^ (p.toReal - 1/2) * B ^ (1/2) * (2 * p.toReal / (2 * p.toReal - 1))) ^ (1/p).toReal`

under the hypothesis `∀ x, ‖E x‖ ≤ min A (B / x ^ 2)`.  **That statement is false as written**,
because the occurrence `B ^ (1 / 2)` is elaborated with a *natural-number* exponent: with no type
ascription the numeral `1 / 2` is a `Nat` (hence `0`) and Lean picks `HPow ℝ ℕ ℝ`, so the factor is
`B ^ 0 = 1`.  The statement therefore asks for the sharp constant with `√B` deleted.

For `A = 1`, `B = 9`, `p = 2` and `E x = min 1 (9 / x ^ 2)` (which satisfies the hypothesis with
equality) one has `eLpNorm E 2 volume = ofReal (√8)` while the right-hand side is
`ofReal (√(8/3))`, so the claimed inequality fails.

This file records the statement with the intended *real* power `B ^ (1 / 2 : ℝ)` and proves it, so
that repairing the original is a one-character change (`1 / 2` ⟶ `1 / 2 : ℝ`).

The proof is the sharp computation: the envelope has `∫ (min A (B/x²))^q dx
= 2 A^{q-1/2} B^{1/2} (2q/(2q-1))` for `q > 1/2`, obtained by integrating over `(0, ∞)` (split at
`√(B/A)`) and doubling; the pieces are the three lemmas imported above.
-/

namespace Work.KMTAreas.SupNorm

open MeasureTheory

theorem eLpNorm_min_inv_sq_le_corrected {E : ℝ → ℂ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    {p : ENNReal} (hp1 : 1 ≤ p) (hpt : p ≠ ⊤)
    (hE : ∀ x, ‖E x‖ ≤ min A (B / x ^ 2))
    (hEm : MeasureTheory.AEStronglyMeasurable E MeasureTheory.volume := by pw_aesm) :
    MeasureTheory.eLpNorm E p MeasureTheory.volume
      ≤ ENNReal.ofReal (2 * A ^ (p.toReal - 1 / 2) * B ^ (1 / 2 : ℝ)
          * (2 * p.toReal / (2 * p.toReal - 1))) ^ (1 / p).toReal := by
  have hp0 : p ≠ 0 := by
    intro h; rw [h] at hp1; exact absurd hp1 (by norm_num)
  have hq1 : 1 ≤ p.toReal := ENNReal.toReal_mono hpt hp1
  set q : ℝ := p.toReal with hqdef
  have hq_half : 1 / 2 < q := by rw [hqdef]; linarith
  have hqpos : 0 < q := by linarith
  have hqnn : 0 ≤ q := le_of_lt hqpos
  -- The value of the integral of the envelope over `ℝ`.
  have hInt : ∫ x : ℝ, (min A (B / x ^ 2)) ^ q
      = 2 * A ^ (q - 1 / 2) * B ^ (1 / 2 : ℝ) * (2 * q / (2 * q - 1)) := by
    rcases eq_or_lt_of_le hA with hA0 | hApos
    · -- `A = 0`: the envelope vanishes identically.
      have hz : (fun x : ℝ => (min A (B / x ^ 2)) ^ q) = fun _ => 0 := by
        funext x
        rw [← hA0, min_eq_left (div_nonneg hB (sq_nonneg x)), Real.zero_rpow (ne_of_gt hqpos)]
      rw [hz, MeasureTheory.integral_zero, ← hA0,
        Real.zero_rpow (x := q - 1 / 2) (by linarith)]
      ring
    · rcases eq_or_lt_of_le hB with hB0 | hBpos
      · -- `B = 0`: same.
        have hz : (fun x : ℝ => (min A (B / x ^ 2)) ^ q) = fun _ => 0 := by
          funext x
          rw [← hB0, zero_div, min_eq_right hA, Real.zero_rpow (ne_of_gt hqpos)]
        rw [hz, MeasureTheory.integral_zero, ← hB0,
          Real.zero_rpow (x := (1 / 2 : ℝ)) (by norm_num)]
        ring
      · -- `A, B > 0`: the integrand is even, so the integral is twice that over `(0, ∞)`.
        have hcomp := integral_comp_abs (f := fun y : ℝ => (min A (B / y ^ 2)) ^ q)
        rw [show (fun x : ℝ => (min A (B / |x| ^ 2)) ^ q)
              = (fun x : ℝ => (min A (B / x ^ 2)) ^ q) from by funext x; rw [sq_abs]] at hcomp
        calc ∫ x : ℝ, (min A (B / x ^ 2)) ^ q
            = 2 * ∫ x in Set.Ioi (0 : ℝ), (min A (B / x ^ 2)) ^ q := hcomp
          _ = 2 * (A ^ q * Real.sqrt (B / A)
                + B ^ q * (Real.sqrt (B / A)) ^ (1 - 2 * q) / (2 * q - 1)) := by
                rw [integral_Ioi_min_inv_sq_rpow hApos hBpos hq_half]
          _ = 2 * A ^ (q - 1 / 2) * B ^ (1 / 2 : ℝ) * (2 * q / (2 * q - 1)) :=
                min_inv_sq_rpow_algebra_real hApos hBpos hq_half
  have hIntble : MeasureTheory.Integrable (fun x : ℝ => (min A (B / x ^ 2)) ^ q)
      MeasureTheory.volume :=
    integrable_min_inv_sq_rpow hA hB hq_half
  have hlin : (∫⁻ x, ENNReal.ofReal ((min A (B / x ^ 2)) ^ q))
      = ENNReal.ofReal (2 * A ^ (q - 1 / 2) * B ^ (1 / 2 : ℝ) * (2 * q / (2 * q - 1))) := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntble
      (Filter.Eventually.of_forall
        (fun x => Real.rpow_nonneg (le_min hA (div_nonneg hB (sq_nonneg x))) q))]
    exact congrArg ENNReal.ofReal hInt
  have hmono : MeasureTheory.eLpNorm E p MeasureTheory.volume
      ≤ (∫⁻ x, ENNReal.ofReal ((min A (B / x ^ 2)) ^ q)) ^ (1 / q) := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := hEm) hp0 hpt, ← hqdef]
    apply ENNReal.rpow_le_rpow _ (by positivity)
    apply MeasureTheory.lintegral_mono
    intro x
    calc ‖E x‖ₑ ^ q
        ≤ (ENNReal.ofReal (min A (B / x ^ 2))) ^ q := by
          apply ENNReal.rpow_le_rpow _ hqnn
          rw [← ofReal_norm (E x)]
          exact ENNReal.ofReal_le_ofReal (hE x)
      _ = ENNReal.ofReal ((min A (B / x ^ 2)) ^ q) :=
          ENNReal.ofReal_rpow_of_nonneg (le_min hA (div_nonneg hB (sq_nonneg x))) hqnn
  have key : MeasureTheory.eLpNorm E p MeasureTheory.volume
      ≤ ENNReal.ofReal (2 * A ^ (q - 1 / 2) * B ^ (1 / 2 : ℝ)
          * (2 * q / (2 * q - 1))) ^ (1 / q) := by
    calc MeasureTheory.eLpNorm E p MeasureTheory.volume
        ≤ (∫⁻ x, ENNReal.ofReal ((min A (B / x ^ 2)) ^ q)) ^ (1 / q) := hmono
      _ = ENNReal.ofReal (2 * A ^ (q - 1 / 2) * B ^ (1 / 2 : ℝ)
            * (2 * q / (2 * q - 1))) ^ (1 / q) := by rw [hlin]
  rw [hqdef] at key
  rw [show (1 / p : ENNReal).toReal = 1 / p.toReal by
        rw [ENNReal.toReal_div, ENNReal.toReal_one]]
  exact key

end Work.KMTAreas.SupNorm
