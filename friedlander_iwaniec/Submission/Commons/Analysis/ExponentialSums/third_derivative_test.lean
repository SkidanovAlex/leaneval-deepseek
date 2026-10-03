import Mathlib
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Int.Star
import Mathlib.Data.Int.SuccPred
import Mathlib.Algebra.Group.Ext
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum.RealSqrt

open Complex
open scoped BigOperators ComplexConjugate
set_option autoImplicit false

namespace Commons.Analysis.ExponentialSums

scoped notation "exp" => Complex.exp

/-- additive character e(x) = exp(2π i x) -/
noncomputable def ch (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

lemma norm_ch_le_one (x : ℝ) : ‖ch x‖ ≤ 1 := by
  unfold ch
  rw [Complex.norm_exp_ofReal_mul_I]

noncomputable def Ssum (f : ℝ → ℝ) (n : ℤ) : ℂ := ch (f (n : ℝ))

lemma norm_Ssum (f : ℝ → ℝ) (n : ℤ) : ‖Ssum f n‖ ≤ 1 := norm_ch_le_one (f (n : ℝ))

lemma le_mul_rpow_sixth {M : ℕ} {l : ℝ} (hl1 : 1 ≤ l) :
    (M : ℝ) ≤ (M : ℝ) * l ^ (1 / 6 : ℝ) := by
  by_cases hM0 : M = 0
  · subst hM0
    simp
  · have hlr : 1 ≤ l ^ (1 / 6 : ℝ) := Real.one_le_rpow hl1 (by norm_num)
    have hM0' : 0 ≤ (M : ℝ) := by positivity
    calc
      (M : ℝ) = (M : ℝ) * 1 := by ring
      _ ≤ (M : ℝ) * l ^ (1 / 6 : ℝ) := mul_le_mul_of_nonneg_left hlr hM0'

end Commons.Analysis.ExponentialSums
