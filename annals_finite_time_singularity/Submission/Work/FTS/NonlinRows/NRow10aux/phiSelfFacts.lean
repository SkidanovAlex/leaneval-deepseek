/-
# The boundedness of the iterated radial derivatives of `φ(z) = z/(1+z)`

`Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk` needs the single quantitative fact that the radial
factor `φ(z) = z/(1+z)` has all its iterated `z∂_z`-derivatives of order `≤ 4` bounded by `1`
on `[0,∞)` (plus `SmoothOpen`).  This module proves it from scratch, so that the main file does
not have to rely on any other module of the `NRow10aux` chain.

Route.  `DzdIter b φ` is a rational function of `z` with denominator a power of `1+z`; for
`b ≤ 4` the explicit values are

```
b = 0 :  z/(1+z)                       b = 3 :  z(1-4z+z²) / (1+z)^4
b = 1 :  z/(1+z)²                      b = 4 :  z(1-11z+11z²-z³) / (1+z)^5
b = 2 :  z(1-z)/(1+z)³
```

(denominators written as iterated products, which is what the `deriv`-computations produce).
The recursion `DzdIter (b+1) φ = z ∂_z (DzdIter b φ)` is then an explicit `deriv`-computation
for each step (`phiQ_step*`), and each explicit value is bounded by `1` on `z ≥ 0`
(`phiQ_bound*`: the numerator is bounded by the sum of the absolute values of its
coefficients, and the denominator by `(1+z)^b`; the only case needing any care is `b = 4`,
where the crude coefficient bound is split over `z ≤ 1` and `z ≥ 1`).

The induction transferring the explicit values to `DzdIter` uses `EventuallyEq.deriv`
(the recursion only holds where the expression is differentiable, i.e. on `z > -1`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.NonlinRows.NRow10aux.PhiDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows.NRow10aux

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Smoothness of `φ` on the open quadrant -/

theorem phiSelf_smoothOpen :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => Work.FTS.NonlinRows.NRow10aux.phiF z) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 / (1 + p.1))
    Work.FTS.EllipticEst.Q0
  refine contDiffOn_fst.div (contDiffOn_const.add contDiffOn_fst) ?_
  intro p hp
  have hp1 : (0 : ℝ) < 1 + p.1 := by
    have := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
    linarith
  positivity

/-! ## The explicit values of the iterated derivatives

The denominators are written as iterated products (never as powers) so that the
`deriv`-computations match the stated function forms syntactically. -/

/-- The explicit rational forms of `DzdIter b φ`, `b ≤ 4`.  (The last arm is the `b = 4`
form, which is also what the default arm of the pattern match returns for `b > 4`; only
`b ≤ 4` is ever used.) -/
def phiQ : ℕ → ℝ → ℝ
  | 0 => fun z => z / (1 + z)
  | 1 => fun z => z / ((1 + z) * (1 + z))
  | 2 => fun z => z * (1 - z) / (((1 + z) * (1 + z)) * (1 + z))
  | 3 => fun z => z * (1 - 4 * z + z * z) / ((((1 + z) * (1 + z)) * (1 + z)) * (1 + z))
  | _ => fun z => z * (1 - 11 * z + 11 * (z * z) - z * z * z)
      / (((((1 + z) * (1 + z)) * (1 + z)) * (1 + z)) * (1 + z))

/-! ### The one-variable derivative facts -/

private theorem dPhi_id (z : ℝ) : deriv (fun z : ℝ => z) z = 1 := by
  simpa using congrFun deriv_id'' z

private theorem dPhi_1add (z : ℝ) : deriv (fun z : ℝ => 1 + z) z = 1 := by
  have h : deriv (fun z : ℝ => 1 + z) z = deriv (fun z : ℝ => z) z :=
    deriv_const_add (x := z) (f := fun z : ℝ => z) (1 : ℝ)
  rw [h]; exact dPhi_id z

private theorem dPhi_1sub (z : ℝ) : deriv (fun z : ℝ => 1 - z) z = -1 := by
  have h : deriv (fun z : ℝ => 1 - z) z = - deriv (fun z : ℝ => z) z :=
    deriv_const_sub (x := z) (f := fun z : ℝ => z) (1 : ℝ)
  rw [h, dPhi_id]

private theorem dPhi_4z (z : ℝ) : deriv (fun z : ℝ => 4 * z) z = 4 := by
  have h : deriv (fun z : ℝ => 4 * z) z = 4 * deriv (fun z : ℝ => z) z :=
    deriv_const_mul (x := z) (d := fun z : ℝ => z) (4 : ℝ) (by fun_prop)
  rw [h, dPhi_id]; ring

private theorem dPhi_1sub4z (z : ℝ) : deriv (fun z : ℝ => 1 - 4 * z) z = -4 := by
  have h : deriv (fun z : ℝ => 1 - 4 * z) z = - deriv (fun z : ℝ => 4 * z) z :=
    deriv_const_sub (x := z) (f := fun z : ℝ => 4 * z) (1 : ℝ)
  rw [h, dPhi_4z]

private theorem dPhi_zz (z : ℝ) : deriv (fun z : ℝ => z * z) z = 2 * z := by
  have h : deriv (fun z : ℝ => z * z) z
      = deriv (fun z : ℝ => z) z * z + z * deriv (fun z : ℝ => z) z :=
    deriv_mul (x := z) (c := fun z : ℝ => z) (d := fun z : ℝ => z) (by fun_prop) (by fun_prop)
  rw [h, dPhi_id]; ring

private theorem dPhi_quad (z : ℝ) : deriv (fun z : ℝ => 1 - 4 * z + z * z) z = -4 + 2 * z := by
  have h : deriv (fun z : ℝ => 1 - 4 * z + z * z) z
      = deriv (fun z : ℝ => 1 - 4 * z) z + deriv (fun z : ℝ => z * z) z :=
    deriv_add (x := z) (f := fun z : ℝ => 1 - 4 * z) (g := fun z : ℝ => z * z)
      (by fun_prop) (by fun_prop)
  rw [h, dPhi_1sub4z, dPhi_zz]

private theorem dPhi_shift2 (z : ℝ) : deriv (fun z : ℝ => (1 + z) * (1 + z)) z = 2 * (1 + z) := by
  have h : deriv (fun z : ℝ => (1 + z) * (1 + z)) z
      = deriv (fun z : ℝ => 1 + z) z * (1 + z) + (1 + z) * deriv (fun z : ℝ => 1 + z) z :=
    deriv_mul (x := z) (c := fun z : ℝ => 1 + z) (d := fun z : ℝ => 1 + z)
      (by fun_prop) (by fun_prop)
  rw [h, dPhi_1add]; ring

private theorem dPhi_shift3 (z : ℝ) :
    deriv (fun z : ℝ => ((1 + z) * (1 + z)) * (1 + z)) z = 3 * ((1 + z) * (1 + z)) := by
  have h : deriv (fun z : ℝ => ((1 + z) * (1 + z)) * (1 + z)) z
      = deriv (fun z : ℝ => (1 + z) * (1 + z)) z * (1 + z)
        + ((1 + z) * (1 + z)) * deriv (fun z : ℝ => 1 + z) z :=
    deriv_mul (x := z) (c := fun z : ℝ => (1 + z) * (1 + z)) (d := fun z : ℝ => 1 + z)
      (by fun_prop) (by fun_prop)
  rw [h, dPhi_shift2, dPhi_1add]; ring

private theorem dPhi_shift4 (z : ℝ) :
    deriv (fun z : ℝ => (((1 + z) * (1 + z)) * (1 + z)) * (1 + z)) z
      = 4 * (((1 + z) * (1 + z)) * (1 + z)) := by
  have h : deriv (fun z : ℝ => (((1 + z) * (1 + z)) * (1 + z)) * (1 + z)) z
      = deriv (fun z : ℝ => ((1 + z) * (1 + z)) * (1 + z)) z * (1 + z)
        + (((1 + z) * (1 + z)) * (1 + z)) * deriv (fun z : ℝ => 1 + z) z :=
    deriv_mul (x := z) (c := fun z : ℝ => ((1 + z) * (1 + z)) * (1 + z))
      (d := fun z : ℝ => 1 + z) (by fun_prop) (by fun_prop)
  rw [h, dPhi_shift3, dPhi_1add]; ring

private theorem dPhi_z_1subz (z : ℝ) : deriv (fun z : ℝ => z * (1 - z)) z = 1 - 2 * z := by
  have h : deriv (fun z : ℝ => z * (1 - z)) z
      = deriv (fun z : ℝ => z) z * (1 - z) + z * deriv (fun z : ℝ => 1 - z) z :=
    deriv_mul (x := z) (c := fun z : ℝ => z) (d := fun z : ℝ => 1 - z)
      (by fun_prop) (by fun_prop)
  rw [h, dPhi_id, dPhi_1sub]; ring

private theorem dPhi_num3 (z : ℝ) :
    deriv (fun z : ℝ => z * (1 - 4 * z + z * z)) z = 1 - 8 * z + 3 * (z * z) := by
  have h : deriv (fun z : ℝ => z * (1 - 4 * z + z * z)) z
      = deriv (fun z : ℝ => z) z * (1 - 4 * z + z * z)
        + z * deriv (fun z : ℝ => 1 - 4 * z + z * z) z :=
    deriv_mul (x := z) (c := fun z : ℝ => z) (d := fun z : ℝ => 1 - 4 * z + z * z)
      (by fun_prop) (by fun_prop)
  rw [h, dPhi_id, dPhi_quad]; ring

private theorem dPhi_11z (z : ℝ) : deriv (fun z : ℝ => 11 * z) z = 11 := by
  have h : deriv (fun z : ℝ => 11 * z) z = 11 * deriv (fun z : ℝ => z) z :=
    deriv_const_mul (x := z) (d := fun z : ℝ => z) (11 : ℝ) (by fun_prop)
  rw [h, dPhi_id]; ring

private theorem dPhi_1sub11z (z : ℝ) : deriv (fun z : ℝ => 1 - 11 * z) z = -11 := by
  have h : deriv (fun z : ℝ => 1 - 11 * z) z = - deriv (fun z : ℝ => 11 * z) z :=
    deriv_const_sub (x := z) (f := fun z : ℝ => 11 * z) (1 : ℝ)
  rw [h, dPhi_11z]

private theorem dPhi_11zz (z : ℝ) : deriv (fun z : ℝ => 11 * (z * z)) z = 11 * (2 * z) := by
  have h : deriv (fun z : ℝ => 11 * (z * z)) z = 11 * deriv (fun z : ℝ => z * z) z :=
    deriv_const_mul (x := z) (d := fun z : ℝ => z * z) (11 : ℝ) (by fun_prop)
  rw [h, dPhi_zz]

private theorem dPhi_quad11 (z : ℝ) :
    deriv (fun z : ℝ => 1 - 11 * z + 11 * (z * z)) z = -11 + 11 * (2 * z) := by
  have h : deriv (fun z : ℝ => 1 - 11 * z + 11 * (z * z)) z
      = deriv (fun z : ℝ => 1 - 11 * z) z + deriv (fun z : ℝ => 11 * (z * z)) z :=
    deriv_add (x := z) (f := fun z : ℝ => 1 - 11 * z) (g := fun z : ℝ => 11 * (z * z))
      (by fun_prop) (by fun_prop)
  rw [h, dPhi_1sub11z, dPhi_11zz]

private theorem dPhi_zzz (z : ℝ) : deriv (fun z : ℝ => z * z * z) z = 3 * (z * z) := by
  have h : deriv (fun z : ℝ => z * z * z) z
      = deriv (fun z : ℝ => z * z) z * z + (z * z) * deriv (fun z : ℝ => z) z :=
    deriv_mul (x := z) (c := fun z : ℝ => z * z) (d := fun z : ℝ => z)
      (by fun_prop) (by fun_prop)
  rw [h, dPhi_zz, dPhi_id]; ring

private theorem dPhi_cubic (z : ℝ) :
    deriv (fun z : ℝ => 1 - 11 * z + 11 * (z * z) - z * z * z) z
      = -11 + 22 * z - 3 * (z * z) := by
  have h : deriv (fun z : ℝ => 1 - 11 * z + 11 * (z * z) - z * z * z) z
      = deriv (fun z : ℝ => 1 - 11 * z + 11 * (z * z)) z - deriv (fun z : ℝ => z * z * z) z :=
    deriv_sub (x := z) (f := fun z : ℝ => 1 - 11 * z + 11 * (z * z))
      (g := fun z : ℝ => z * z * z) (by fun_prop) (by fun_prop)
  rw [h, dPhi_quad11, dPhi_zzz]; ring

private theorem dPhi_num4 (z : ℝ) :
    deriv (fun z : ℝ => z * (1 - 11 * z + 11 * (z * z) - z * z * z)) z
      = 1 - 22 * z + 33 * (z * z) - 4 * (z * z * z) := by
  have h : deriv (fun z : ℝ => z * (1 - 11 * z + 11 * (z * z) - z * z * z)) z
      = deriv (fun z : ℝ => z) z * (1 - 11 * z + 11 * (z * z) - z * z * z)
        + z * deriv (fun z : ℝ => 1 - 11 * z + 11 * (z * z) - z * z * z) z :=
    deriv_mul (x := z) (c := fun z : ℝ => z)
      (d := fun z : ℝ => 1 - 11 * z + 11 * (z * z) - z * z * z) (by fun_prop) (by fun_prop)
  rw [h, dPhi_id, dPhi_cubic]; ring

/-! ### The recursion `z ∂_z (φQ b) = φQ (b+1)` -/

theorem phiQ_step0 (z : ℝ) (hz : (1 + z) ≠ 0) :
    z * deriv (fun z : ℝ => z / (1 + z)) z = z / ((1 + z) * (1 + z)) := by
  have h : deriv (fun z : ℝ => z / (1 + z)) z = 1 / ((1 + z) * (1 + z)) := by
    change deriv ((fun z : ℝ => z) / fun z : ℝ => 1 + z) z = 1 / ((1 + z) * (1 + z))
    have hdiv := deriv_div (x := z) (c := fun z : ℝ => z) (d := fun z : ℝ => 1 + z)
      (by fun_prop) (by fun_prop) hz
    rw [hdiv, dPhi_id, dPhi_1add]
    simp
    field_simp
  rw [h]; ring

theorem phiQ_step1 (z : ℝ) (hz : (1 + z) ≠ 0) :
    z * deriv (fun z : ℝ => z / ((1 + z) * (1 + z))) z
      = z * (1 - z) / (((1 + z) * (1 + z)) * (1 + z)) := by
  have h : deriv (fun z : ℝ => z / ((1 + z) * (1 + z))) z
      = (1 - z) / (((1 + z) * (1 + z)) * (1 + z)) := by
    change deriv ((fun z : ℝ => z) / fun z : ℝ => (1 + z) * (1 + z)) z
      = (1 - z) / (((1 + z) * (1 + z)) * (1 + z))
    have hdiv := deriv_div (x := z) (c := fun z : ℝ => z) (d := fun z : ℝ => (1 + z) * (1 + z))
      (by fun_prop) (by fun_prop) (by positivity)
    rw [hdiv, dPhi_id, dPhi_shift2]
    simp
    field_simp
    ring
  rw [h]; ring

theorem phiQ_step2 (z : ℝ) (hz : (1 + z) ≠ 0) :
    z * deriv (fun z : ℝ => z * (1 - z) / (((1 + z) * (1 + z)) * (1 + z))) z
      = z * (1 - 4 * z + z * z) / ((((1 + z) * (1 + z)) * (1 + z)) * (1 + z)) := by
  have h : deriv (fun z : ℝ => z * (1 - z) / (((1 + z) * (1 + z)) * (1 + z))) z
      = (1 - 4 * z + z * z) / ((((1 + z) * (1 + z)) * (1 + z)) * (1 + z)) := by
    change deriv ((fun z : ℝ => z * (1 - z)) / fun z : ℝ => ((1 + z) * (1 + z)) * (1 + z)) z
      = (1 - 4 * z + z * z) / ((((1 + z) * (1 + z)) * (1 + z)) * (1 + z))
    have hdiv := deriv_div (x := z) (c := fun z : ℝ => z * (1 - z))
      (d := fun z : ℝ => ((1 + z) * (1 + z)) * (1 + z))
      (by fun_prop) (by fun_prop) (by positivity)
    rw [hdiv, dPhi_z_1subz, dPhi_shift3]
    field_simp
    ring
  rw [h]; ring

theorem phiQ_step3 (z : ℝ) (hz : (1 + z) ≠ 0) :
    z * deriv (fun z : ℝ =>
        z * (1 - 4 * z + z * z) / ((((1 + z) * (1 + z)) * (1 + z)) * (1 + z))) z
      = z * (1 - 11 * z + 11 * (z * z) - z * z * z)
          / (((((1 + z) * (1 + z)) * (1 + z)) * (1 + z)) * (1 + z)) := by
  have h : deriv (fun z : ℝ =>
        z * (1 - 4 * z + z * z) / ((((1 + z) * (1 + z)) * (1 + z)) * (1 + z))) z
      = (1 - 11 * z + 11 * (z * z) - z * z * z)
          / (((((1 + z) * (1 + z)) * (1 + z)) * (1 + z)) * (1 + z)) := by
    change deriv ((fun z : ℝ => z * (1 - 4 * z + z * z))
        / fun z : ℝ => (((1 + z) * (1 + z)) * (1 + z)) * (1 + z)) z
      = (1 - 11 * z + 11 * (z * z) - z * z * z)
          / (((((1 + z) * (1 + z)) * (1 + z)) * (1 + z)) * (1 + z))
    have hdiv := deriv_div (x := z) (c := fun z : ℝ => z * (1 - 4 * z + z * z))
      (d := fun z : ℝ => (((1 + z) * (1 + z)) * (1 + z)) * (1 + z))
      (by fun_prop) (by fun_prop) (by positivity)
    rw [hdiv, dPhi_num3, dPhi_shift4]
    field_simp
    ring
  rw [h]; ring

/-! ### The bounds `|φQ b z| ≤ 1` on `z ≥ 0` -/

theorem phiQ_bound0 (z : ℝ) (hz : 0 ≤ z) : |z / (1 + z)| ≤ 1 := by
  rw [abs_div, abs_of_nonneg hz, abs_of_pos (by linarith : (0 : ℝ) < 1 + z)]
  rw [div_le_one (by linarith)]
  linarith

theorem phiQ_bound1 (z : ℝ) (hz : 0 ≤ z) : |z / ((1 + z) * (1 + z))| ≤ 1 := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  rw [abs_div, abs_of_nonneg hz, abs_of_pos (by positivity : (0 : ℝ) < (1 + z) * (1 + z))]
  rw [div_le_one (by positivity)]
  nlinarith [sq_nonneg z]

theorem phiQ_bound2 (z : ℝ) (hz : 0 ≤ z) :
    |z * (1 - z) / (((1 + z) * (1 + z)) * (1 + z))| ≤ 1 := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  rw [abs_div, abs_mul, abs_of_nonneg hz,
    abs_of_pos (by positivity : (0 : ℝ) < ((1 + z) * (1 + z)) * (1 + z))]
  rw [div_le_one (by positivity)]
  have h : |1 - z| ≤ 1 + z := by rw [abs_le]; constructor <;> linarith
  nlinarith [mul_le_mul_of_nonneg_left h hz, sq_nonneg (1 + z)]

theorem phiQ_bound3 (z : ℝ) (hz : 0 ≤ z) :
    |z * (1 - 4 * z + z * z) / ((((1 + z) * (1 + z)) * (1 + z)) * (1 + z))| ≤ 1 := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  rw [abs_div, abs_mul, abs_of_nonneg hz,
    abs_of_pos (by positivity : (0 : ℝ) < (((1 + z) * (1 + z)) * (1 + z)) * (1 + z))]
  rw [div_le_one (by positivity)]
  have h : |1 - 4 * z + z * z| ≤ 1 + 4 * z + z * z := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg z, hz]
  nlinarith [mul_le_mul_of_nonneg_left h hz, sq_nonneg (1 + z), hz]

theorem phiQ_bound4 (z : ℝ) (hz : 0 ≤ z) :
    |z * (1 - 11 * z + 11 * (z * z) - z * z * z)
      / (((((1 + z) * (1 + z)) * (1 + z)) * (1 + z)) * (1 + z))| ≤ 1 := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  rw [abs_div, abs_mul, abs_of_nonneg hz,
    abs_of_pos (by positivity :
      (0 : ℝ) < ((((1 + z) * (1 + z)) * (1 + z)) * (1 + z)) * (1 + z))]
  rw [div_le_one (by positivity)]
  have h : |1 - 11 * z + 11 * (z * z) - z * z * z|
      ≤ 1 + 11 * z + 11 * (z * z) + z * z * z := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg z, hz]
  have h2 : z * (1 + 11 * z + 11 * (z * z) + z * z * z)
      ≤ ((((1 + z) * (1 + z)) * (1 + z)) * (1 + z)) * (1 + z) := by
    by_cases hz1 : z ≤ 1
    · have h4 : z * z + z * z * z ≤ 4 * z := by nlinarith [sq_nonneg z, hz, hz1]
      nlinarith [h4, hz, pow_nonneg hz 4]
    · have hz1' : 1 ≤ z := le_of_lt (not_le.mp hz1)
      have h4 : z * z + z * z * z ≤ 4 * (z * z * z * z) := by
        nlinarith [sq_nonneg (z - 1), hz, hz1']
      nlinarith [h4, hz, hz1', pow_nonneg hz 5]
  nlinarith [mul_le_mul_of_nonneg_left h hz, h2]

/-! ### The identification `DzdIter b φ = φQ b` and the bound -/

/-- `DzdIter b φ` is the explicit rational form `φQ b`, for `z > -1` (where all the
expressions are differentiable). -/
theorem phiQ_DzdIter_eq : ∀ b : ℕ, b ≤ 4 → ∀ z : ℝ, -1 < z →
    Work.Elliptic.DzdIter b (fun z : ℝ => z / (1 + z)) z = phiQ b z := by
  intro b
  induction b with
  | zero => intro _ z _; rfl
  | succ n ih =>
      intro hb z hz
      have hn : n ≤ 3 := by omega
      rw [Work.Elliptic.DzdIter_succ]
      show z * deriv (Work.Elliptic.DzdIter n (fun z : ℝ => z / (1 + z))) z = phiQ (n + 1) z
      have hderiv : deriv (Work.Elliptic.DzdIter n (fun z : ℝ => z / (1 + z))) z
          = deriv (phiQ n) z := by
        have hev : (fun w : ℝ => Work.Elliptic.DzdIter n (fun z : ℝ => z / (1 + z)) w)
            =ᶠ[𝓝 z] phiQ n :=
          Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hz) (fun w hw => ih (by omega) w hw)
        exact hev.deriv.eq_of_nhds
      rw [hderiv]
      have hz' : (1 + z) ≠ 0 := by linarith
      interval_cases n
      · exact phiQ_step0 z hz'
      · exact phiQ_step1 z hz'
      · exact phiQ_step2 z hz'
      · exact phiQ_step3 z hz'

/-- **The bound used by `mul_phi_Hk`**: every `z∂_z`-iterate of `z/(1+z)` of order `≤ 4` is
bounded by `1` on `[0,∞)`. -/
theorem phiSelf_DzdIter_bound (b : ℕ) (hb : b ≤ 4) (z : ℝ) (hz : 0 ≤ z) :
    |Work.Elliptic.DzdIter b (fun z : ℝ => z / (1 + z)) z| ≤ 1 := by
  rw [phiQ_DzdIter_eq b hb z (by linarith)]
  interval_cases b
  · exact phiQ_bound0 z hz
  · exact phiQ_bound1 z hz
  · exact phiQ_bound2 z hz
  · exact phiQ_bound3 z hz
  · exact phiQ_bound4 z hz

/-- The same bound for the two-variable lift `fun z _ => φ z`. -/
theorem phiSelf_DzdIter_bound_phiF (b : ℕ) (hb : b ≤ 4) (z : ℝ) (hz : 0 ≤ z) :
    |Work.Elliptic.DzdIter b (fun z : ℝ => Work.FTS.NonlinRows.NRow10aux.phiF z) z| ≤ 1 :=
  phiSelf_DzdIter_bound b hb z hz

end

end Work.FTS.NonlinRows.NRow10aux
