import Mathlib
import Submission.Work.C17.Bsubst_deps

/-!
# Area C17 — Lemma `seven` (6): `y·(B₆∘y)' = (B₃∘y)·y'`

The pure functions `Bᵢ` (`Submission.CDTPlan.pureB`, `g i = Bᵢ ∘ yps` with `yps = x²/(x-1)`,
`Work.C7.g`) satisfy the differential identity `X·B₆' = B₃` (in the variable of the `B`'s), whose
pull-back along `y = x²/(x-1)` is the requested identity:

  `yps * derivative (g 5) = (g 2) * derivative yps`.

Indeed `g 5 = B₆ ∘ yps`, `g 2 = B₃ ∘ yps`, and by the chain rule for formal power-series
substitution `derivative (B₆ ∘ yps) = (B₆' ∘ yps) · yps'`, so the claim reduces to
`yps · (B₆'∘yps) = B₃∘yps`, which is `X·B₆' = B₃` transported through `subst yps`.
-/

namespace Work.C17

open PowerSeries

/-! ## The pure-function identity `X·B₆' = B₃` -/

private lemma coeff_B3_def (n : ℕ) :
    PowerSeries.coeff n Submission.CDTPlan.B3 =
      if n = 0 then 0 else (((n - 1).factorial : ℚ)) ^ 2 / (((2 * n).factorial : ℕ) : ℚ) := by
  rw [Submission.CDTPlan.B3, PowerSeries.coeff_mk]

private lemma coeff_B6_def (n : ℕ) :
    PowerSeries.coeff n Submission.CDTPlan.B6 =
      if n = 0 then 0
      else (((n - 1).factorial : ℚ)) ^ 2 / ((n : ℚ) * (((2 * n).factorial : ℕ) : ℚ)) := by
  rw [Submission.CDTPlan.B6, PowerSeries.coeff_mk]

/-- `m·[y^m]B₆ = [y^m]B₃`. -/
private lemma b6_coeff_mul (m : ℕ) :
    (m : ℚ) * PowerSeries.coeff m Submission.CDTPlan.B6
      = PowerSeries.coeff m Submission.CDTPlan.B3 := by
  rw [coeff_B6_def, coeff_B3_def]
  by_cases h : m = 0
  · subst h; simp
  · rw [if_neg h, if_neg h]
    have hf : (((2 * m).factorial : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * m)
    field_simp

private lemma coeff_X_mul_aux (m : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff m ((X : PowerSeries ℚ) * f)
      = if 1 ≤ m then PowerSeries.coeff (m - 1) f else 0 := by
  simpa using PowerSeries.coeff_X_pow_mul' f 1 m

/-- `X·B₆' = B₃`, coefficient by coefficient. -/
private lemma x_mul_deriv_B6 :
    (X : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) Submission.CDTPlan.B6
      = Submission.CDTPlan.B3 := by
  apply PowerSeries.ext
  intro m
  rw [coeff_X_mul_aux]
  by_cases hm : 1 ≤ m
  · rw [if_pos hm, PowerSeries.coeff_derivative, show m - 1 + 1 = m from by omega]
    have hc : (((m - 1 : ℕ)) : ℚ) + 1 = (m : ℚ) := by rw [Nat.cast_sub hm]; ring
    rw [hc]
    simpa [mul_comm] using b6_coeff_mul m
  · rw [if_neg hm, coeff_B3_def]
    have hm0 : m = 0 := by omega
    subst hm0
    simp

private lemma pureB_two : Submission.CDTPlan.pureB (2 : Fin 7) = Submission.CDTPlan.B3 := rfl
private lemma pureB_five : Submission.CDTPlan.pureB (5 : Fin 7) = Submission.CDTPlan.B6 := rfl

/-! ## The pull-back identity -/

theorem B6_deriv : Work.C7.yps * PowerSeries.derivative (R := ℚ) (Work.C7.g 5)
    = (Work.C7.g 2) * PowerSeries.derivative (R := ℚ) Work.C7.yps := by
  have hh : HasSubst Work.C7.yps := Submission.CDT.sympY_hasSubst
  -- `X·B₆' = B₃` transported through the substitution `yps`
  have hsub : Work.C7.yps * (PowerSeries.derivative (R := ℚ) Submission.CDTPlan.B6).subst Work.C7.yps
      = Submission.CDTPlan.B3.subst Work.C7.yps := by
    have h := congrArg (fun f : PowerSeries ℚ => f.subst Work.C7.yps) x_mul_deriv_B6
    rw [PowerSeries.subst_mul hh, PowerSeries.subst_X hh] at h
    exact h
  -- chain rule
  have hchain : PowerSeries.derivative (R := ℚ) (Work.C7.g 5)
      = (PowerSeries.derivative (R := ℚ) Submission.CDTPlan.B6).subst Work.C7.yps
        * PowerSeries.derivative (R := ℚ) Work.C7.yps := by
    have h1 : Work.C7.g 5 = (Submission.CDTPlan.pureB (5 : Fin 7)).subst Work.C7.yps := rfl
    rw [h1, pureB_five]
    exact PowerSeries.derivative_subst hh
  have hg2 : Work.C7.g 2 = Submission.CDTPlan.B3.subst Work.C7.yps := by
    have h1 : Work.C7.g 2 = (Submission.CDTPlan.pureB (2 : Fin 7)).subst Work.C7.yps := rfl
    rw [h1, pureB_two]
  calc Work.C7.yps * PowerSeries.derivative (R := ℚ) (Work.C7.g 5)
      = Work.C7.yps * ((PowerSeries.derivative (R := ℚ) Submission.CDTPlan.B6).subst Work.C7.yps
          * PowerSeries.derivative (R := ℚ) Work.C7.yps) := by rw [hchain]
    _ = (Work.C7.yps * (PowerSeries.derivative (R := ℚ) Submission.CDTPlan.B6).subst Work.C7.yps)
          * PowerSeries.derivative (R := ℚ) Work.C7.yps := by rw [mul_assoc]
    _ = (Submission.CDTPlan.B3.subst Work.C7.yps) * PowerSeries.derivative (R := ℚ) Work.C7.yps := by
          rw [hsub]
    _ = (Work.C7.g 2) * PowerSeries.derivative (R := ℚ) Work.C7.yps := by rw [hg2]

end Work.C17
