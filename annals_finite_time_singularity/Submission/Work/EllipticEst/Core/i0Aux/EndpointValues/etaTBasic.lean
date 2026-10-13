/-
Copyright: work module for the Elgindi finite-time singularity project.

# Elementary facts about the endpoint test function `etaT`

`etaT t x = x (1 - x/t)^3` with `etaT'` and `etaT''` its first two derivatives.
This file records, for the two-integration-by-parts endpoint reproducing formula
(`Work.EllipticEst.Core.i0Aux.EndpointValues.twoIbpEtaT`):

* the two `HasDerivAt` statements (valid for every `t : ℝ`),
* the endpoint values `η(0) = 0`, `η'(0) = 1`, `η(t) = 0`, `η'(t) = 0`,
* global continuity of `η`, `η'`, `η''`,
* the two `L^∞(0,t)` bounds `|η| ≤ t`, `|η''| ≤ 6/t`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.EllipticEst.Core.i0Aux.EndpointDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.EndpointValues

open scoped Topology
open Filter Set MeasureTheory

set_option autoImplicit false

theorem etaT_hasDerivAt (t x : ℝ) :
    HasDerivAt (Work.EllipticEst.Core.i0Aux.etaT t)
      (Work.EllipticEst.Core.i0Aux.etaT' t x) x := by
  have h := (hasDerivAt_id x).mul (((hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
      ((hasDerivAt_id x).div_const t)).pow 3)
  have hder : 1 * (1 - x / t) ^ 3 + x * (3 * (1 - x / t) ^ (3 - 1) * (0 - 1 / t))
      = Work.EllipticEst.Core.i0Aux.etaT' t x := by
    unfold Work.EllipticEst.Core.i0Aux.etaT'
    ring_nf
  have h' : HasDerivAt (fun y : ℝ => y * (1 - y / t) ^ 3)
      (1 * (1 - x / t) ^ 3 + x * (3 * (1 - x / t) ^ (3 - 1) * (0 - 1 / t))) x := h
  rw [hder] at h'
  exact h'

theorem etaT'_hasDerivAt (t x : ℝ) :
    HasDerivAt (Work.EllipticEst.Core.i0Aux.etaT' t)
      (Work.EllipticEst.Core.i0Aux.etaT'' t x) x := by
  have h1 := ((hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
    ((hasDerivAt_id x).div_const t)).pow 2
  have h3 := (hasDerivAt_id x).const_mul (4 : ℝ) |>.div_const t
  have h2 := (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub h3
  have h := h1.mul h2
  unfold Work.EllipticEst.Core.i0Aux.etaT' Work.EllipticEst.Core.i0Aux.etaT''
  convert h using 1
  · funext y
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, id_eq]
    try ring_nf
  · simp only [Pi.pow_apply, Pi.sub_apply, id_eq]
    try ring_nf

theorem continuous_etaT (t : ℝ) : Continuous (Work.EllipticEst.Core.i0Aux.etaT t) :=
  continuous_iff_continuousAt.mpr fun x => (etaT_hasDerivAt t x).continuousAt

theorem continuous_etaT' (t : ℝ) : Continuous (Work.EllipticEst.Core.i0Aux.etaT' t) :=
  continuous_iff_continuousAt.mpr fun x => (etaT'_hasDerivAt t x).continuousAt

theorem continuous_etaT'' (t : ℝ) : Continuous (Work.EllipticEst.Core.i0Aux.etaT'' t) := by
  rw [show Work.EllipticEst.Core.i0Aux.etaT'' t
      = fun x => (6 / t) * (1 - x / t) * (2 * x / t - 1) from rfl]
  fun_prop

theorem etaT_zero (t : ℝ) : Work.EllipticEst.Core.i0Aux.etaT t 0 = 0 := by
  simp [Work.EllipticEst.Core.i0Aux.etaT]

theorem etaT'_zero (t : ℝ) : Work.EllipticEst.Core.i0Aux.etaT' t 0 = 1 := by
  simp [Work.EllipticEst.Core.i0Aux.etaT']

theorem etaT_at_t (t : ℝ) (ht : t ≠ 0) : Work.EllipticEst.Core.i0Aux.etaT t t = 0 := by
  have h : 1 - t / t = 0 := by rw [div_self ht]; ring
  rw [Work.EllipticEst.Core.i0Aux.etaT, h]
  ring

theorem etaT'_at_t (t : ℝ) (ht : t ≠ 0) : Work.EllipticEst.Core.i0Aux.etaT' t t = 0 := by
  have h : 1 - t / t = 0 := by rw [div_self ht]; ring
  rw [Work.EllipticEst.Core.i0Aux.etaT', h]
  ring

theorem abs_etaT_le (t x : ℝ) (ht : 0 < t) (hx : x ∈ Ioo 0 t) :
    |Work.EllipticEst.Core.i0Aux.etaT t x| ≤ t := by
  have hx0 : 0 < x := hx.1
  have hxt : x < t := hx.2
  have h1 : |x| ≤ t := by rw [abs_of_pos hx0]; exact le_of_lt hxt
  have h2 : |1 - x / t| ≤ 1 := by
    rw [abs_le]
    constructor
    · have : x / t ≤ 1 := (div_le_one ht).2 (le_of_lt hxt)
      linarith
    · have : 0 ≤ x / t := div_nonneg (le_of_lt hx0) (le_of_lt ht)
      linarith
  have h2' : |1 - x / t| ^ 3 ≤ 1 := by
    have h0 : 0 ≤ |1 - x / t| := abs_nonneg _
    nlinarith [sq_nonneg |1 - x / t|]
  calc |Work.EllipticEst.Core.i0Aux.etaT t x| = |x| * |1 - x / t| ^ 3 := by
        rw [Work.EllipticEst.Core.i0Aux.etaT, abs_mul, abs_pow]
    _ ≤ t * 1 := mul_le_mul h1 h2' (by positivity) (le_of_lt ht)
    _ = t := by ring

theorem abs_etaT''_le (t x : ℝ) (ht : 0 < t) (hx : x ∈ Ioo 0 t) :
    |Work.EllipticEst.Core.i0Aux.etaT'' t x| ≤ 6 / t := by
  have hx0 : 0 < x := hx.1
  have hxt : x < t := hx.2
  have h2 : |1 - x / t| ≤ 1 := by
    rw [abs_le]
    constructor
    · have : x / t ≤ 1 := (div_le_one ht).2 (le_of_lt hxt)
      linarith
    · have : 0 ≤ x / t := div_nonneg (le_of_lt hx0) (le_of_lt ht)
      linarith
  have h3 : |2 * x / t - 1| ≤ 1 := by
    rw [mul_div_assoc, abs_le]
    constructor
    · have : 0 ≤ x / t := div_nonneg (le_of_lt hx0) (le_of_lt ht)
      linarith
    · have : x / t ≤ 1 := (div_le_one ht).2 (le_of_lt hxt)
      linarith
  have h6 : (0:ℝ) ≤ 6 / t := by positivity
  have hAB : |1 - x / t| * |2 * x / t - 1| ≤ 1 := by
    nlinarith [abs_nonneg (1 - x / t), abs_nonneg (2 * x / t - 1)]
  calc |Work.EllipticEst.Core.i0Aux.etaT'' t x|
      = |6 / t| * (|1 - x / t| * |2 * x / t - 1|) := by
        rw [Work.EllipticEst.Core.i0Aux.etaT'', abs_mul, abs_mul]
        ring
    _ ≤ (6 / t) * 1 := by
        refine mul_le_mul ?_ hAB (by positivity) h6
        rw [abs_of_nonneg h6]
    _ = 6 / t := by ring

end Work.EllipticEst.Core.i0Aux.EndpointValues
