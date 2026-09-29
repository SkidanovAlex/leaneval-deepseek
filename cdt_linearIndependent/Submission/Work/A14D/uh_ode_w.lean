import Mathlib
import Submission.Work.A14D.uh_defs
import Submission.Work.A14D.uh_formal_ode
import Submission.Work.A14D.uh_series_basic
import Submission.Work.C17f.Pfun_solves_M
import Submission.Work.CLift.defs

/-!
# A14D — the operator identity for the coefficient series `G0`

The formal identity `Ap · Puh'' + Bp · Puh' + Cp · Puh = 0`
(`Submission.Work.A14D.uh_formal_ode`) is transported to the analytic function
`G0 w = Σₙ aₙ wⁿ` on the disc `‖w‖ < 8/9` by evaluating the power series:
the evaluation `Work.CLift.evA` is additive and multiplicative on absolutely
summable series (`Work.CLift.evA_add`, `Work.CLift.evA_mul`), and on the disc
`G0`, `deriv G0`, `deriv (deriv G0)` are the evaluations of `Puh`, `Puh'`,
`Puh''` respectively (`Submission.Work.A14D.uh_series_basic`).
-/

namespace Work.A14D

open PowerSeries

noncomputable section

/-- Evaluation of the polynomial `Ap = -8X + 17X² - 9X³` at the point `z`. -/
private lemma evA_Ap (z : ℂ) :
    Work.CLift.evA (Ap : PowerSeries ℚ) z = (-8 : ℂ) * z + 17 * z ^ 2 - 9 * z ^ 3 := by
  rw [Work.CLift.evA_coe_poly]
  simp only [Ap, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X, Polynomial.eval₂_pow]
  push_cast
  norm_num
  ring

/-- Evaluation of the polynomial `Bp = -8 + 34X - 27X²` at the point `z`. -/
private lemma evA_Bp (z : ℂ) :
    Work.CLift.evA (Bp : PowerSeries ℚ) z = (-8 : ℂ) + 34 * z - 27 * z ^ 2 := by
  rw [Work.CLift.evA_coe_poly]
  simp only [Bp, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X]
  push_cast
  norm_num
  ring

/-- Evaluation of the polynomial `Cp = 6 - 9X` at the point `z`. -/
private lemma evA_Cp (z : ℂ) :
    Work.CLift.evA (Cp : PowerSeries ℚ) z = (6 : ℂ) - 9 * z := by
  rw [Work.CLift.evA_coe_poly]
  simp only [Cp, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X]
  push_cast
  norm_num
  ring

theorem uh_ode_w : ∀ w : ℂ, ‖w‖ < 8 / 9 → ((-8 : ℂ) * w + 17 * w ^ 2 - 9 * w ^ 3) * deriv (deriv G0) w + ((-8 : ℂ) + 34 * w - 27 * w ^ 2) * deriv G0 w + (6 - 9 * w) * G0 w = 0 := by
  intro z hz
  obtain ⟨hcv0, -, -, hcv1, hcv2, ha0, ha1, ha2⟩ := uh_series_basic
  -- the coefficients of the first two derived series
  have e1 (k : ℕ) : ((PowerSeries.coeff k (PowerSeries.derivative (R := ℚ) Puh) : ℚ) : ℂ) * z ^ k
      = ((k : ℂ) + 1) * (uhCoeff (k + 1) : ℂ) * z ^ k := by
    rw [PowerSeries.coeff_derivative, coeff_Puh]
    push_cast
    ring
  have e2 (k : ℕ) :
      ((PowerSeries.coeff k (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) Puh)
          : PowerSeries ℚ) : ℚ) : ℂ) * z ^ k
        = ((k : ℂ) + 1) * ((k : ℂ) + 2) * (uhCoeff (k + 2) : ℂ) * z ^ k := by
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative, coeff_Puh]
    push_cast
    ring
  -- the evaluations of `Puh`, `Puh'`, `Puh''` are `G0`, `deriv G0`, `deriv (deriv G0)`
  have hfz : Work.CLift.evA (Puh : PowerSeries ℚ) z = G0 z := by
    rw [Work.CLift.evA, ← (hcv0 z hz).tsum_eq]
    refine tsum_congr fun n => ?_
    rw [coeff_Puh]
  have hdz : Work.CLift.evA (PowerSeries.derivative (R := ℚ) Puh) z = deriv G0 z := by
    rw [Work.CLift.evA, ← (hcv1 z hz).tsum_eq]
    exact tsum_congr fun n => e1 n
  have hddz : Work.CLift.evA (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) Puh)) z
      = deriv (deriv G0) z := by
    rw [Work.CLift.evA, ← (hcv2 z hz).tsum_eq]
    exact tsum_congr fun n => e2 n
  -- absolute summability of the three coefficient series
  have hn0 : Summable fun k : ℕ => ‖((PowerSeries.coeff k Puh : ℚ) : ℂ) * z ^ k‖ :=
    (ha0 z hz).congr fun k => by rw [coeff_Puh]
  have hn1 : Summable fun k : ℕ =>
      ‖((PowerSeries.coeff k (PowerSeries.derivative (R := ℚ) Puh) : ℚ) : ℂ) * z ^ k‖ :=
    (ha1 z hz).congr fun k => by rw [e1 k]
  have hn2 : Summable fun k : ℕ =>
      ‖((PowerSeries.coeff k (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) Puh))
        : ℚ) : ℂ) * z ^ k‖ :=
    (ha2 z hz).congr fun k => by rw [e2 k]
  have hApn : Summable fun k : ℕ =>
      ‖((PowerSeries.coeff k (Ap : PowerSeries ℚ) : ℚ) : ℂ) * z ^ k‖ :=
    Work.C17f.summable_norm_coe_poly Ap z
  have hBpn : Summable fun k : ℕ =>
      ‖((PowerSeries.coeff k (Bp : PowerSeries ℚ) : ℚ) : ℂ) * z ^ k‖ :=
    Work.C17f.summable_norm_coe_poly Bp z
  have hCpn : Summable fun k : ℕ =>
      ‖((PowerSeries.coeff k (Cp : PowerSeries ℚ) : ℚ) : ℂ) * z ^ k‖ :=
    Work.C17f.summable_norm_coe_poly Cp z
  have hAn : Summable fun k : ℕ =>
      ((PowerSeries.coeff k ((Ap : PowerSeries ℚ)
        * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) Puh)) : ℚ) : ℂ) * z ^ k :=
    (Work.C17f.summable_norm_coeff_mul _ _ z hApn hn2).of_norm
  have hBn : Summable fun k : ℕ =>
      ((PowerSeries.coeff k ((Bp : PowerSeries ℚ)
        * PowerSeries.derivative (R := ℚ) Puh) : ℚ) : ℂ) * z ^ k :=
    (Work.C17f.summable_norm_coeff_mul _ _ z hBpn hn1).of_norm
  have hCn : Summable fun k : ℕ =>
      ((PowerSeries.coeff k ((Cp : PowerSeries ℚ) * Puh) : ℚ) : ℂ) * z ^ k :=
    (Work.C17f.summable_norm_coeff_mul _ _ z hCpn hn0).of_norm
  -- evaluation of the three products
  have hAev : Work.CLift.evA ((Ap : PowerSeries ℚ)
        * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) Puh)) z
      = ((-8 : ℂ) * z + 17 * z ^ 2 - 9 * z ^ 3) * deriv (deriv G0) z := by
    rw [Work.CLift.evA_mul _ _ _ hApn hn2, evA_Ap z, hddz]
  have hBev : Work.CLift.evA ((Bp : PowerSeries ℚ)
        * PowerSeries.derivative (R := ℚ) Puh) z
      = ((-8 : ℂ) + 34 * z - 27 * z ^ 2) * deriv G0 z := by
    rw [Work.CLift.evA_mul _ _ _ hBpn hn1, evA_Bp z, hdz]
  have hCev : Work.CLift.evA ((Cp : PowerSeries ℚ) * Puh) z
      = (6 - 9 * z) * G0 z := by
    rw [Work.CLift.evA_mul _ _ _ hCpn hn0, evA_Cp z, hfz]
  have hABn : Summable fun k : ℕ =>
      ((PowerSeries.coeff k ((Ap : PowerSeries ℚ)
          * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) Puh)
        + (Bp : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) Puh) : ℚ) : ℂ) * z ^ k :=
    Work.C17f.summable_coeff_add _ _ z hAn hBn
  have hLHS : Work.CLift.evA ((Ap : PowerSeries ℚ)
          * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) Puh)
        + (Bp : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) Puh
        + (Cp : PowerSeries ℚ) * Puh) z
      = ((-8 : ℂ) * z + 17 * z ^ 2 - 9 * z ^ 3) * deriv (deriv G0) z
        + ((-8 : ℂ) + 34 * z - 27 * z ^ 2) * deriv G0 z + (6 - 9 * z) * G0 z := by
    rw [Work.CLift.evA_add _ _ _ hABn hCn, Work.CLift.evA_add _ _ _ hAn hBn,
      hAev, hBev, hCev]
  calc ((-8 : ℂ) * z + 17 * z ^ 2 - 9 * z ^ 3) * deriv (deriv G0) z
        + ((-8 : ℂ) + 34 * z - 27 * z ^ 2) * deriv G0 z + (6 - 9 * z) * G0 z
      = Work.CLift.evA ((Ap : PowerSeries ℚ)
            * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) Puh)
          + (Bp : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) Puh
          + (Cp : PowerSeries ℚ) * Puh) z := hLHS.symm
    _ = Work.CLift.evA (0 : PowerSeries ℚ) z := by rw [uh_formal_ode]
    _ = 0 := Work.CLift.evA_zero z

end

end Work.A14D
