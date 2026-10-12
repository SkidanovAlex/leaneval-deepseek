import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB6Est.GFun
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.gFun_beta_le` — sign-corrected Taylor bounds for `gFun` on the far region

`gFun τ b r = τ + b − √(τ²+2τb) − b²/(2r²)`, and for `b ≥ 0`
`τ + b − √(τ²+2τb) = b²/(τ+b+√(τ²+2τb))` (`Work.BoseB6Est.sq_sub_sqrt_eq_div`).  Hence

* `b ≥ 0` (`gFun_beta_le`): `τ+b+σ ≥ 2τ` gives `gFun τ b r ≤ b²(r²−τ)/(2τr²)`;
* `b ≤ 0` with `τ+2b > 0` (`gFun_beta_le_neg`): `σ ≤ τ` gives
  `gFun τ b r ≤ b²(1/(τ+2b) − 1/(2r²))`.

Both bound the FS-cutoff region `‖t‖ > T` of `Work.BoseBogFS.integral_cleanFun_le`, where
the honest `β(t) = a⁻¹Ŵ₁(√(ρa)t)` has no sign restriction.

Also recorded: `gFun` is **antitone** in its first argument (`gFun_tau_anti`), which is the
direction needed because FS's `τ̃` dominates the honest `tauSc`.
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseBogFS

open Work.BoseB6Est

private lemma gFun_unfold (x b r : ℝ) :
    gFun x b r = x + b - Real.sqrt ((x + b) ^ 2 - b ^ 2) - b ^ 2 / (2 * r ^ 2) := rfl

/-- `gFun τ 0 r = 0` for `τ ≥ 0`. -/
theorem gFun_beta_zero {τ r : ℝ} (hτ : 0 ≤ τ) : gFun τ 0 r = 0 := by
  rw [gFun_unfold]
  have h : (τ + 0) ^ 2 - 0 ^ 2 = τ ^ 2 := by ring
  rw [h, Real.sqrt_sq hτ]
  ring

/-- The `b ≥ 0` denominator form: `gFun τ b r = b²/(τ+b+√(τ²+2τb)) − b²/(2r²)`. -/
theorem gFun_eq_div {τ b r : ℝ} (hτ : 0 ≤ τ) (hb : 0 ≤ b) :
    gFun τ b r = b ^ 2 / (τ + b + Real.sqrt (τ ^ 2 + 2 * τ * b)) - b ^ 2 / (2 * r ^ 2) := by
  have h := sq_sub_sqrt_eq_div hb (show b ≤ τ + b by linarith)
  rw [gFun_unfold, h]
  rw [show (τ + b) ^ 2 - b ^ 2 = τ ^ 2 + 2 * τ * b from by ring]

/-- **`gFun` is antitone in `τ`** on `τ ≥ 0`, for `b ≥ 0`. -/
theorem gFun_tau_anti {τ τ' b r : ℝ} (hτ : 0 ≤ τ) (hττ : τ ≤ τ') (hb : 0 ≤ b) :
    gFun τ' b r ≤ gFun τ b r := by
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · rw [← hb0, gFun_beta_zero (le_trans hτ hττ), gFun_beta_zero hτ]
  have hτ' : 0 ≤ τ' := le_trans hτ hττ
  rw [gFun_eq_div hτ' hb, gFun_eq_div hτ hb]
  have hmono : τ + b + Real.sqrt (τ ^ 2 + 2 * τ * b)
      ≤ τ' + b + Real.sqrt (τ' ^ 2 + 2 * τ' * b) := by
    have hsq : τ ^ 2 + 2 * τ * b ≤ τ' ^ 2 + 2 * τ' * b := by nlinarith
    linarith [Real.sqrt_le_sqrt hsq]
  have hpos : 0 < τ + b + Real.sqrt (τ ^ 2 + 2 * τ * b) := by
    have := Real.sqrt_nonneg (τ ^ 2 + 2 * τ * b); linarith
  linarith [div_le_div_of_nonneg_left (sq_nonneg b) hpos hmono]

/-- **Far-region bound for `b ≥ 0`**: `gFun τ b r ≤ b²(r²−τ)/(2τr²)`. -/
theorem gFun_beta_le {τ b r : ℝ} (hτ : 0 < τ) (hτr : τ ≤ r ^ 2) (hb : 0 ≤ b) :
    gFun τ b r ≤ b ^ 2 * (r ^ 2 - τ) / (2 * τ * r ^ 2) := by
  rw [gFun_eq_div hτ.le hb]
  have h3 : τ ≤ Real.sqrt (τ ^ 2 + 2 * τ * b) := by
    exact Real.le_sqrt_of_sq_le (by nlinarith)
  have h4 : b ^ 2 / (τ + b + Real.sqrt (τ ^ 2 + 2 * τ * b)) ≤ b ^ 2 / (2 * τ) :=
    div_le_div_of_nonneg_left (sq_nonneg b) (by linarith) (by linarith)
  have h5 : b ^ 2 / (2 * τ) - b ^ 2 / (2 * r ^ 2)
      = b ^ 2 * (r ^ 2 - τ) / (2 * τ * r ^ 2) := by
    have hr : r ≠ 0 := by
      intro h0; rw [h0] at hτr; simp at hτr; linarith
    have hτne : τ ≠ 0 := ne_of_gt hτ
    field_simp
  linarith [h4, h5.le, h5.ge]

/-- **Far-region bound for `b ≤ 0`** (honest square root, i.e. `0 < τ + 2b`). -/
theorem gFun_beta_le_neg {τ b r : ℝ} (hb : b ≤ 0) (hτb : 0 < τ + 2 * b) :
    gFun τ b r ≤ b ^ 2 * (1 / (τ + 2 * b) - 1 / (2 * r ^ 2)) := by
  have hτ : 0 < τ := by linarith
  have h1 : τ + b - Real.sqrt ((τ + b) ^ 2 - b ^ 2)
      = b ^ 2 / (τ + b + Real.sqrt ((τ + b) ^ 2 - b ^ 2)) := by
    have hthis := sq_sub_sqrt_eq_div (α := τ + b) (b := -b)
      (show (0:ℝ) ≤ -b by linarith) (show -b ≤ τ + b by linarith)
    simpa using hthis
  have h2 : (τ + b) ^ 2 - b ^ 2 = τ ^ 2 + 2 * τ * b := by ring
  have h3 : Real.sqrt (τ ^ 2 + 2 * τ * b) ≤ τ := by
    rw [← h2]
    exact (Real.sqrt_le_left (by nlinarith)).mpr (by nlinarith)
  have h4 : b ^ 2 / (τ + b + Real.sqrt ((τ + b) ^ 2 - b ^ 2)) ≤ b ^ 2 / (τ + 2 * b) :=
    div_le_div_of_nonneg_left (sq_nonneg b) hτb
      (by have := Real.sqrt_nonneg ((τ + b) ^ 2 - b ^ 2); linarith)
  have h5 : b ^ 2 / (τ + 2 * b) - b ^ 2 / (2 * r ^ 2)
      = b ^ 2 * (1 / (τ + 2 * b) - 1 / (2 * r ^ 2)) := by ring
  rw [gFun_unfold, h1]
  linarith [h4, h5.le, h5.ge]

end Work.BoseBogFS
