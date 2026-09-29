import Mathlib
import Submission.Work.C17.Bsubst_deps

/-!
# `B7_deriv`: the pullback of `B₇ = ∫ B₄/y`

The pure function `B₇` is the formal primitive `∫ B₄/y`, i.e. its coefficients are
`[yⁿ]B₇ = [yⁿ]B₄ / n` (`n ≥ 1`).  Equivalently `X · B₇' = B₄` as power series.

Since `g 6 = B₇ ∘ y`, `g 3 = B₄ ∘ y` and `y = x²/(x-1)`, the chain rule gives

  `y · (B₇ ∘ y)' = y · (B₇' ∘ y) · y' = ((X · B₇') ∘ y) · y' = (B₄ ∘ y) · y'`,

which is the requested identity.
-/

namespace Work.C17

open PowerSeries

/-- Coefficients of `B₇ = ∫ B₄/X`: `[yⁿ]B₇ = [yⁿ]B₄ / n` for `n ≥ 1`, and `0` at `n = 0`. -/
private lemma coeff_B7 (n : ℕ) : PowerSeries.coeff n Submission.CDTPlan.B7 =
    if n = 0 then 0 else PowerSeries.coeff n Submission.CDTPlan.B4 / n := by
  rw [Submission.CDTPlan.B7, PowerSeries.coeff_mk]

/-- The pure identity `X · B₇' = B₄`, i.e. `B₇ = ∫ B₄/X`. -/
private lemma X_mul_deriv_B7 :
    (PowerSeries.X : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) Submission.CDTPlan.B7
      = Submission.CDTPlan.B4 := by
  apply PowerSeries.ext
  intro n
  rcases n with _ | m
  · rw [PowerSeries.coeff_zero_X_mul]
    rw [Submission.CDTPlan.B4, PowerSeries.coeff_mk]
    simp
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
      coeff_B7, if_neg (by omega : ¬ (m + 1 = 0))]
    rw [Submission.CDTPlan.B4, PowerSeries.coeff_mk]
    push_cast
    field_simp

theorem B7_deriv : Work.C7.yps * PowerSeries.derivative (R := ℚ) (Work.C7.g 6)
    = (Work.C7.g 3) * PowerSeries.derivative (R := ℚ) Work.C7.yps := by
  have hY : PowerSeries.HasSubst Submission.CDT.sympY := Submission.CDT.sympY_hasSubst
  have hg6 : Work.C7.g 6 = PowerSeries.subst Submission.CDT.sympY Submission.CDTPlan.B7 := by
    show (Submission.CDTPlan.pureB 6).subst Submission.CDT.sympY = _
    rw [show Submission.CDTPlan.pureB 6 = Submission.CDTPlan.B7 from by
      simp [Submission.CDTPlan.pureB]]
  have hg3 : Work.C7.g 3 = PowerSeries.subst Submission.CDT.sympY Submission.CDTPlan.B4 := by
    show (Submission.CDTPlan.pureB 3).subst Submission.CDT.sympY = _
    rw [show Submission.CDTPlan.pureB 3 = Submission.CDTPlan.B4 from by
      simp [Submission.CDTPlan.pureB]]
  have hchain : PowerSeries.derivative (R := ℚ) (Work.C7.g 6)
      = PowerSeries.subst Submission.CDT.sympY (PowerSeries.derivative (R := ℚ) Submission.CDTPlan.B7)
        * PowerSeries.derivative (R := ℚ) Submission.CDT.sympY := by
    rw [hg6, PowerSeries.derivative_subst hY]
  rw [hchain, hg3, show Work.C7.yps = Submission.CDT.sympY from rfl, ← mul_assoc]
  congr 1
  nth_rewrite 1 [← PowerSeries.subst_X (R := ℚ) hY]
  rw [← PowerSeries.subst_mul (R := ℚ) hY (f := (PowerSeries.X : PowerSeries ℚ))
      (g := PowerSeries.derivative (R := ℚ) Submission.CDTPlan.B7)]
  rw [X_mul_deriv_B7]

end Work.C17
