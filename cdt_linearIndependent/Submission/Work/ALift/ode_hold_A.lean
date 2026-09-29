import Mathlib
import Submission.Work.ALift.ode_A
import Submission.Work.CLift.ode_holds
import Submission.Work.ALift.summable_norm_HU

/-!
# Area ALift — the ODE satisfied by `U₀, U₁, U₂`

Evaluating the formal identity `HA_odeLHS (HZ a b c) = C b + C c·(1-X)⁻¹` (`HZ_odeLHS`) at a point
`q` with `‖q‖ ≤ 9/10` (the region where `H`'s coefficient series converges absolutely, by the
overconvergence `coef_bound_A`), one obtains

`P(q)·U₂(q) + Q(q)·U₁(q) + R(q)·U₀(q) = b + c/(1-q)`,

the analytic form of Zagier's order-2 operator applied to `H`.  The proof is the same shape as
`Work.CLift.ode_holds`: the Cauchy product (`evA_mul_hasSum`) evaluates each of the three products
`P·H''`, `Q·H'`, `R·H`, and the sum is identified with the evaluation of `HA_odeLHS H` by
comparing coefficients.
-/

open PowerSeries
open scoped BigOperators

namespace Work.ALift

open Submission.CDTPlan

noncomputable section

lemma evA_deriv_H (a b c : ℤ) (q : ℂ) :
    Work.CLift.evA (PowerSeries.derivative (R := ℚ) (HZ a b c)) q = HU1 a b c q := by
  rw [Work.CLift.evA, HU1]
  apply tsum_congr
  intro k
  rw [PowerSeries.coeff_derivative]
  unfold hcoef
  push_cast
  ring

lemma evA_deriv2_H (a b c : ℤ) (q : ℂ) :
    Work.CLift.evA (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (HZ a b c))) q
      = HU2 a b c q := by
  rw [Work.CLift.evA, HU2]
  apply tsum_congr
  intro k
  rw [Commons.RingTheory.PowerSeries.coeff_der2]
  unfold hcoef
  push_cast
  ring

lemma evA_H (a b c : ℤ) (q : ℂ) : Work.CLift.evA (HZ a b c) q = HU0 a b c q := by
  rw [Work.CLift.evA, HU0]
  rfl

theorem HU_ode (a b c : ℤ) (hRel : ARel a b c) (q : ℂ) (hq : ‖q‖ ≤ 9 / 10) :
    Pd q * HU2 a b c q + Qd q * HU1 a b c q + Rd q * HU0 a b c q = rhsA b c q := by
  have hq1 : ‖q‖ < 1 := by linarith
  obtain ⟨hsu0, hsu1, hsu2⟩ := summable_norm_HU a b c hRel q hq
  -- summability of the coefficient series of the two formal derivatives
  have sd1 : Summable (fun k : ℕ => ‖((PowerSeries.coeff k
      (PowerSeries.derivative (R := ℚ) (HZ a b c)) : ℚ) : ℂ) * q ^ k‖) := by
    refine hsu1.congr (fun k => ?_)
    rw [PowerSeries.coeff_derivative]
    unfold hcoef
    push_cast
    ring
  have sd2 : Summable (fun k : ℕ => ‖((PowerSeries.coeff k
      (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (HZ a b c))) : ℚ) : ℂ) * q ^ k‖) := by
    refine hsu2.congr (fun k => ?_)
    rw [Commons.RingTheory.PowerSeries.coeff_der2]
    unfold hcoef
    push_cast
    ring
  have sd0 : Summable (fun k : ℕ => ‖((PowerSeries.coeff k (HZ a b c) : ℚ) : ℂ) * q ^ k‖) := by
    refine hsu0.congr (fun k => ?_)
    rfl
  -- summability of the polynomial coefficient series
  have sP : Summable (fun k : ℕ => ‖((PowerSeries.coeff k (Pdpoly : PowerSeries ℚ) : ℚ) : ℂ)
      * q ^ k‖) := Work.CLift.summable_norm_poly Pdpoly q
  have sQ : Summable (fun k : ℕ => ‖((PowerSeries.coeff k (Qdpoly : PowerSeries ℚ) : ℚ) : ℂ)
      * q ^ k‖) := Work.CLift.summable_norm_poly Qdpoly q
  have sR : Summable (fun k : ℕ => ‖((PowerSeries.coeff k (Rdpoly : PowerSeries ℚ) : ℚ) : ℂ)
      * q ^ k‖) := Work.CLift.summable_norm_poly Rdpoly q
  -- the three Cauchy products
  have hsP := Work.CLift.evA_mul_hasSum (Pdpoly : PowerSeries ℚ)
    (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (HZ a b c))) q sP sd2
  have hsQ := Work.CLift.evA_mul_hasSum (Qdpoly : PowerSeries ℚ)
    (PowerSeries.derivative (R := ℚ) (HZ a b c)) q sQ sd1
  have hsR := Work.CLift.evA_mul_hasSum (Rdpoly : PowerSeries ℚ) (HZ a b c) q sR sd0
  rw [evA_Pd, evA_deriv2_H] at hsP
  rw [evA_Qd, evA_deriv_H] at hsQ
  rw [evA_Rd, evA_H] at hsR
  have hcomb := (hsP.add hsQ).add hsR
  -- identify the combined summand with the coefficients of the operator applied to `H`
  have hevL : Work.CLift.evA (Submission.CDT.HA_odeLHS (HZ a b c)) q
      = Pd q * HU2 a b c q + Qd q * HU1 a b c q + Rd q * HU0 a b c q := by
    rw [Work.CLift.evA]
    refine (hcomb.congr_fun (fun k => ?_)).tsum_eq
    have hc : PowerSeries.coeff k (Submission.CDT.HA_odeLHS (HZ a b c))
        = PowerSeries.coeff k ((Pdpoly : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ)
              (PowerSeries.derivative (R := ℚ) (HZ a b c))))
          + PowerSeries.coeff k ((Qdpoly : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) (HZ a b c))
          + PowerSeries.coeff k ((Rdpoly : PowerSeries ℚ) * HZ a b c) := by
      rw [HA_odeLHS_eq, ← Pdpoly_coe, ← Qdpoly_coe, ← Rdpoly_coe, map_add, map_add]
    rw [hc]
    push_cast
    ring
  rw [← hevL, HZ_odeLHS a b c, evA_rhs b c q hq1]

end

end Work.ALift
