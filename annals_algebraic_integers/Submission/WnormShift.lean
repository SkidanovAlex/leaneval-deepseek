import Submission.Contracts
import Submission.SerrePotentialIcc
import Submission.WnormToolkit
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Weighted norms at adjacent exponents are comparable

Since `|log w_μ(x)| ≤ K` on `[aSerre,bSerre]` (explicit potential:
`w(x) = e^{serreConstant}·x^{−γ}`, `Submission.SerrePotentialIcc`), the
`k`- and `(k+1)`-norms of a real polynomial differ by at most `e^K`:

    wnorm k P ≤ e^K · wnorm (k+1) P      and      wnorm (k+1) P ≤ e^K · wnorm k P

(used to move norm exponents by O(1) in Hilbert / PVer1 / three_pages).
-/

noncomputable section

open scoped Real
open MeasureTheory

namespace Submission.WnormShift

open Submission.Contracts
open Submission.WnormToolkit
open Submission.SerreExample
open Submission.Serre
open Submission.PotentialDefs
open Submission.SerrePotentialIcc
open Submission.WeightedNorm

/-- A bound `K ≥ 0` on `|log w|` on the interval (from the explicit
potential). -/
def Kbound : ℝ := |serreConstant| + gSerre * (max |Real.log aSerre| |Real.log bSerre|)

lemma Kbound_nonneg : 0 ≤ Kbound := by
  have h1 : 0 ≤ |serreConstant| := abs_nonneg _
  have h2 : 0 ≤ max |Real.log aSerre| |Real.log bSerre| :=
    le_trans (abs_nonneg (Real.log aSerre)) (le_max_left _ _)
  exact add_nonneg h1 (mul_nonneg gSerre_pos.le h2)

/-- `|log w| ≤ Kbound` for `x` in the interval. -/
lemma log_weight_bound_serre {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre) :
    |Real.log (weight muSerre x)| ≤ Kbound := by
  unfold Kbound muSerre
  exact log_weight_bound (x := x) (by simpa using hx)

/-- The weight is bounded above by `e^K` on the interval. -/
lemma weight_le_expK {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre) :
    weight muSerre x ≤ Real.exp Kbound := by
  have hlog := log_weight_bound_serre hx
  have h : Real.log (weight muSerre x) ≤ Kbound := (abs_le.mp hlog).2
  have hlogP : logPotential muSerre (x : ℂ) ≤ Kbound := by
    unfold weight at h
    simpa using (by simpa [Real.log_exp] using h : Real.log (Real.exp (logPotential muSerre (x:ℂ))) ≤ Kbound)
  unfold weight
  exact (Real.exp_le_exp.mpr hlogP)

/-- The weight is bounded below by `e^{−K}` on the interval. -/
lemma exp_negK_le_weight {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre) :
    Real.exp (-Kbound) ≤ weight muSerre x := by
  have hlog := log_weight_bound_serre hx
  have h : -Kbound ≤ Real.log (weight muSerre x) := (abs_le.mp hlog).1
  have hlogP : -Kbound ≤ logPotential muSerre (x : ℂ) := by
    unfold weight at h
    simpa using (by simpa [Real.log_exp] using h : -Kbound ≤ Real.log (Real.exp (logPotential muSerre (x:ℂ))))
  unfold weight
  exact (Real.exp_le_exp.mpr hlogP)

/-- Raising the exponent by one costs at most `e^K`:
`wnorm (k+1) P ≤ e^K · wnorm k P`. -/
theorem wnorm_succ_le (k : ℕ) (P : Polynomial ℝ) :
    wnorm (k + 1) P ≤ Real.exp Kbound * wnorm k P := by
  refine wnorm_sSup_le (k + 1) P ?_
  intro x hx
  have hpt : (weight muSerre x) ^ k * |P.eval x| ≤ wnorm k P := wnorm_ge_pointwise k P hx
  have hwle : weight muSerre x ≤ Real.exp Kbound := weight_le_expK hx
  have hw0 : 0 ≤ weight muSerre x := le_of_lt (weight_pos muSerre x)
  have hn0 : 0 ≤ wnorm k P := wnorm_nonneg k P
  calc
    (weight muSerre x) ^ (k + 1) * |P.eval x|
        = (weight muSerre x) ^ k * |P.eval x| * weight muSerre x := by
          rw [pow_succ]
          ring
    _ ≤ wnorm k P * weight muSerre x := by
      exact mul_le_mul_of_nonneg_right hpt hw0
    _ ≤ Real.exp Kbound * wnorm k P := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (mul_le_mul_of_nonneg_right hwle hn0)

/-- Lowering the exponent by one costs at most `e^K`:
`wnorm k P ≤ e^K · wnorm (k+1) P`. -/
theorem wnorm_le_succ (k : ℕ) (P : Polynomial ℝ) :
    wnorm k P ≤ Real.exp Kbound * wnorm (k + 1) P := by
  refine wnorm_sSup_le k P ?_
  intro x hx
  have hpt : (weight muSerre x) ^ (k + 1) * |P.eval x| ≤ wnorm (k + 1) P :=
    wnorm_ge_pointwise (k + 1) P hx
  have hlow : Real.exp (-Kbound) ≤ weight muSerre x := exp_negK_le_weight hx
  have hwp : 0 < weight muSerre x := weight_pos muSerre x
  have hw0 : 0 ≤ weight muSerre x := le_of_lt hwp
  have hn0 : 0 ≤ wnorm (k + 1) P := wnorm_nonneg (k + 1) P
  have hrec : (weight muSerre x)⁻¹ ≤ Real.exp Kbound := by
    -- from e^{-K} ≤ w,  w^{-1} ≤ e^{K}
    have hpos : 0 < Real.exp (-Kbound) := Real.exp_pos (-Kbound)
    calc
      (weight muSerre x)⁻¹ ≤ (Real.exp (-Kbound))⁻¹ := by
        exact (inv_le_inv₀ hwp hpos).mpr hlow
      _ = Real.exp Kbound := by simpa using (Real.exp_neg (-Kbound)).symm
  calc
    (weight muSerre x) ^ k * |P.eval x|
        = (weight muSerre x) ^ (k + 1) * |P.eval x| * (weight muSerre x)⁻¹ := by
          rw [pow_succ]
          field_simp [ne_of_gt hwp]
    _ ≤ wnorm (k + 1) P * (weight muSerre x)⁻¹ := by
      exact mul_le_mul_of_nonneg_right hpt (inv_nonneg.mpr hw0)
    _ ≤ wnorm (k + 1) P * Real.exp Kbound := by
      exact mul_le_mul_of_nonneg_left hrec hn0
    _ = Real.exp Kbound * wnorm (k + 1) P := by rw [mul_comm]

end Submission.WnormShift
