import Mathlib
import Submission.Work.Parab.inversion.exists_mul_log_lt

namespace Work.Parab.inversion

/-- `log x ≤ 2 √x` for `x ≥ 1`. -/
lemma log_le_two_sqrt {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have h1 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt hx0.le]; ring
  have h2 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hx0)
  have h3 : (1 : ℝ) ≤ Real.sqrt x := Real.one_le_sqrt.2 hx
  rw [h1]; linarith

/-- `‖log z‖ ≤ log ‖z‖ + π` for `1 ≤ ‖z‖`. -/
lemma norm_log_le_of_one_le (z : ℂ) (hz : 1 ≤ ‖z‖) :
    ‖Complex.log z‖ ≤ Real.log ‖z‖ + Real.pi := by
  have h : ‖Complex.log z‖ ≤ |(Complex.log z).re| + |(Complex.log z).im| :=
    Complex.norm_le_abs_re_add_abs_im _
  rw [Complex.log_re, Complex.log_im, abs_of_nonneg (Real.log_nonneg hz)] at h
  linarith [Complex.abs_arg_le_pi z]

/-- **Preimages of far values under `ζ - a log(-ζ) - b` are far and cannot be much farther
than the value.**  If `ζ` satisfies the asymptotic relation `ζ - w - a log(-ζ) - b = o(1)` at
the scale `δ`, then for all large `w` the displacement `‖ζ - w‖` is at most `‖w‖/8` (so `ζ` is
close to `w`) and `‖ζ‖ ≤ 2 ‖w‖`.

The proof is the elementary `log = o(‖·‖)`: `‖ζ - w‖ ≤ ‖a‖ log ‖ζ‖ + O(1)` forces
`‖ζ‖ ≤ 2‖w‖` for large `‖w‖`, and then `‖ζ - w‖ = O(log ‖w‖) ≤ ‖w‖/8`. -/
theorem exists_norm_sub_le_of_asymptotic {a b : ℂ} {δ : ℝ} (hδ : 0 < δ) :
    ∃ W : ℝ, 1 ≤ W ∧ ∀ w ζ : ℂ, 1 ≤ ‖ζ‖ →
      ‖ζ - w - a * Complex.log (-ζ) - b‖ < δ → W ≤ ‖w‖ →
      ‖ζ - w‖ ≤ ‖w‖ / 8 ∧ ‖ζ‖ ≤ 2 * ‖w‖ := by
  set A : ℝ := ‖a‖ with hAdef
  set C : ℝ := ‖a‖ * Real.pi + ‖b‖ + δ with hCdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hC0 : 0 < C := by rw [hCdef]; positivity
  -- displacement bound
  have disp : ∀ w ζ : ℂ, 1 ≤ ‖ζ‖ → ‖ζ - w - a * Complex.log (-ζ) - b‖ < δ →
      ‖ζ - w‖ ≤ A * Real.log ‖ζ‖ + C := by
    intro w ζ hζ1 hd
    have hlog := norm_log_le_of_one_le (-ζ) (by simpa using hζ1)
    rw [norm_neg] at hlog
    have hb : ‖a * Complex.log (-ζ) + b‖ ≤ A * (Real.log ‖ζ‖ + Real.pi) + ‖b‖ := by
      have h1 := norm_add_le (a * Complex.log (-ζ)) b
      rw [norm_mul] at h1
      have h2 : ‖a‖ * ‖Complex.log (-ζ)‖ ≤ A * (Real.log ‖ζ‖ + Real.pi) := by
        rw [hAdef]
        exact mul_le_mul_of_nonneg_left hlog (norm_nonneg a)
      linarith
    have h4 : ζ - w = (ζ - w - a * Complex.log (-ζ) - b) + (a * Complex.log (-ζ) + b) := by
      ring
    calc ‖ζ - w‖
        = ‖(ζ - w - a * Complex.log (-ζ) - b) + (a * Complex.log (-ζ) + b)‖ := by rw [← h4]
      _ ≤ ‖ζ - w - a * Complex.log (-ζ) - b‖ + ‖a * Complex.log (-ζ) + b‖ := norm_add_le _ _
      _ ≤ δ + (A * (Real.log ‖ζ‖ + Real.pi) + ‖b‖) := by linarith
      _ = A * Real.log ‖ζ‖ + C := by rw [hCdef]; ring
  -- a priori bound on `‖ζ‖`
  have key : ∀ w ζ : ℂ, 1 ≤ ‖ζ‖ → ‖ζ - w - a * Complex.log (-ζ) - b‖ < δ →
      ‖ζ‖ ≤ ‖w‖ + A * Real.log ‖ζ‖ + C := by
    intro w ζ hζ1 hd
    have h := disp w ζ hζ1 hd
    have h2 : w + (ζ - w) = ζ := by ring
    calc ‖ζ‖ = ‖w + (ζ - w)‖ := by rw [h2]
      _ ≤ ‖w‖ + ‖ζ - w‖ := norm_add_le _ _
      _ ≤ ‖w‖ + (A * Real.log ‖ζ‖ + C) := by linarith
      _ = ‖w‖ + A * Real.log ‖ζ‖ + C := by ring
  -- if the preimage were more than twice as far as the image, it would be bounded
  set Y : ℝ := (2 * A + Real.sqrt (4 * A ^ 2 + 2 * C)) ^ 2 + 1 with hYdef
  have hYbound : ∀ w ζ : ℂ, 1 ≤ ‖ζ‖ → ‖ζ - w - a * Complex.log (-ζ) - b‖ < δ →
      2 * ‖w‖ < ‖ζ‖ → ‖ζ‖ < Y := by
    intro w ζ hζ1 hd hlt
    have h1 : ‖ζ‖ / 2 < A * Real.log ‖ζ‖ + C := by
      have := key w ζ hζ1 hd
      linarith
    set y : ℝ := Real.sqrt ‖ζ‖ with hydef
    have hy2 : y ^ 2 = ‖ζ‖ := by rw [hydef]; exact Real.sq_sqrt (by positivity)
    have hlogy : Real.log ‖ζ‖ ≤ 2 * y := by
      have h := log_le_two_sqrt hζ1
      rw [← hydef] at h
      exact h
    have hquad : y ^ 2 - 4 * A * y - 2 * C < 0 := by
      have h5 : A * Real.log ‖ζ‖ ≤ A * (2 * y) := mul_le_mul_of_nonneg_left hlogy hA0
      nlinarith [h1, h5, hy2]
    have hD : (0 : ℝ) ≤ 4 * A ^ 2 + 2 * C := by positivity
    have hs : Real.sqrt (4 * A ^ 2 + 2 * C) ^ 2 = 4 * A ^ 2 + 2 * C := Real.sq_sqrt hD
    have hsnn : (0 : ℝ) ≤ Real.sqrt (4 * A ^ 2 + 2 * C) := Real.sqrt_nonneg _
    have habs : |y - 2 * A| < Real.sqrt (4 * A ^ 2 + 2 * C) := by
      have h6 : (y - 2 * A) ^ 2 < (Real.sqrt (4 * A ^ 2 + 2 * C)) ^ 2 := by
        nlinarith [hquad, hs]
      have h7 := sq_lt_sq.mp h6
      rwa [abs_of_nonneg hsnn] at h7
    have hylt : y < 2 * A + Real.sqrt (4 * A ^ 2 + 2 * C) := by
      have := (abs_lt.mp habs).2
      linarith
    have hy0 : 0 ≤ y := by rw [hydef]; exact Real.sqrt_nonneg _
    have hY' : ‖ζ‖ < (2 * A + Real.sqrt (4 * A ^ 2 + 2 * C)) ^ 2 := by
      rw [← hy2]
      exact pow_lt_pow_left₀ hylt hy0 (by norm_num)
    rw [hYdef]
    linarith
  obtain ⟨R₃, _hR₃pos, hR₃⟩ :=
    exists_mul_log_lt (A := A) (K := C) (ε := 1) hA0 hC0.le one_pos
  refine ⟨max 1 (max (Y / 2) R₃), le_max_left _ _, ?_⟩
  intro w ζ hζ1 hd hW
  have hWY : Y / 2 ≤ ‖w‖ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hWR : R₃ ≤ ‖w‖ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  have hζw2 : ‖ζ‖ ≤ 2 * ‖w‖ := by
    by_contra hcon
    push Not at hcon
    have hlt := hYbound w ζ hζ1 hd hcon
    linarith
  constructor
  · have h1 := disp w ζ hζ1 hd
    have h2 : Real.log ‖ζ‖ ≤ Real.log (2 * ‖w‖) :=
      Real.log_le_log (lt_of_lt_of_le zero_lt_one hζ1) hζw2
    have h3 : A * Real.log (2 * ‖w‖) + C < ‖w‖ / 16 := (hR₃ ‖w‖ hWR).2
    have h4 : A * Real.log ‖ζ‖ ≤ A * Real.log (2 * ‖w‖) := mul_le_mul_of_nonneg_left h2 hA0
    linarith [norm_nonneg w]
  · exact hζw2

end Work.Parab.inversion
