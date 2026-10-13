/-
# `Work.FTS.LocData.Phi_div_deriv`

The recursion `D_z Phi_n = Phi_{n+1}` for the radial polynomials `PhiR` of the localised data
of the N9 node, in the normalised form

  `z * (PhiR n w / (1+w)^{n+2})' = PhiR (n+1) z / (1+z)^{n+3}`   for `n ≤ 3`, `z ≠ -1`.

For `n ≤ 3` all the `PhiR i` with `i ≤ 4` are the explicit polynomials `PhiR n z = 2z·R_n(z)`
with `R_0 = 1`, `R_1 = 1-z`, `R_2 = 1-4z+z²`, `R_3 = 1-11z+11z²-z³`, `R_4 = 1-26z+66z²-26z³+z⁴`,
so the identity is a rational-function computation: the four cases are done with the quotient
rule (`HasDerivAt.fun_div`), the numerator and the denominator are differentiated with the
product rule and `HasDerivAt.pow`, and the resulting rational identity is cleared with
`field_simp` and closed by `ring`.

Since the pointwise operation instances on function types are not unfolded during
unification, every hypothesis obtained from `HasDerivAt.mul`/`HasDerivAt.pow` is first
restated in the *lambda* shape in which the target is phrased, using
`HasDerivAt.congr_of_eventuallyEq` plus a pointwise `funext`/`simp`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.LocData.HkFstarDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.LocData

theorem Phi_div_deriv (n : ℕ) (hn : n ≤ 3) {z : ℝ} (hz : z ≠ -1) :
    z * deriv (fun w : ℝ => PhiR n w / (1 + w) ^ (n + 2)) z
      = PhiR (n + 1) z / (1 + z) ^ (n + 3) := by
  have h1 : (1 : ℝ) + z ≠ 0 := by
    intro h
    exact hz (by linarith)
  interval_cases n
  · -- n = 0 :  PhiR 0 w = 2w,  PhiR 1 z = 2z(1-z)
    show z * deriv (fun w : ℝ => PhiR 0 w / (1 + w) ^ 2) z = PhiR 1 z / (1 + z) ^ 3
    have hsub2 : (2 : ℕ) - 1 = 1 := by norm_num
    have hp2 : (1 + z) ^ 2 ≠ 0 := pow_ne_zero 2 h1
    have hnum : HasDerivAt (fun w : ℝ => PhiR 0 w) 2 z := by
      have h0 : HasDerivAt (fun w : ℝ => 2 * w) 2 z :=
        hasDerivAt_const_mul (c := (2 : ℝ)) (x := z)
      refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards with w
        simp
      · ring
    have hden : HasDerivAt (fun w : ℝ => (1 + w) ^ 2) (2 * (1 + z)) z := by
      have h0 : HasDerivAt ((fun w : ℝ => 1 + w) ^ 2) (2 * (1 + z)) z := by
        refine ((((hasDerivAt_id' (x := z)).const_add (1 : ℝ)).pow 2).congr_deriv ?_)
        simp [hsub2]
      refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards with w
        simp
      · ring
    have hq : HasDerivAt (fun w : ℝ => PhiR 0 w / (1 + w) ^ 2)
        (2 * (1 - z) / (1 + z) ^ 3) z := by
      refine (hnum.fun_div hden (pow_ne_zero 2 h1)).congr_deriv ?_
      simp only [PhiR_zero]
      field_simp [h1, hp2]
      ring
    have hgoal : deriv (fun w : ℝ => PhiR 0 w / (1 + w) ^ 2) z
        = 2 * (1 - z) / (1 + z) ^ 3 := by
      simpa using hq.deriv
    rw [hgoal, PhiR_one]
    ring
  · -- n = 1 :  PhiR 1 w = 2w(1-w),  PhiR 2 z = 2z(1-4z+z²)
    show z * deriv (fun w : ℝ => PhiR 1 w / (1 + w) ^ 3) z = PhiR 2 z / (1 + z) ^ 4
    have hsub3 : (3 : ℕ) - 1 = 2 := by norm_num
    have hp3 : (1 + z) ^ 3 ≠ 0 := pow_ne_zero 3 h1
    have hp32 : ((1 + z) ^ 3) ^ 2 ≠ 0 := pow_ne_zero 2 hp3
    have hnum : HasDerivAt (fun w : ℝ => PhiR 1 w) (2 * (1 - z) + 2 * z * (-1)) z := by
      have ha : HasDerivAt (fun w : ℝ => 2 * w) 2 z :=
        hasDerivAt_const_mul (c := (2 : ℝ)) (x := z)
      have hb : HasDerivAt (fun w : ℝ => 1 - w) (-1) z :=
        (hasDerivAt_id' (x := z)).const_sub (1 : ℝ)
      have h0 : HasDerivAt ((fun w : ℝ => 2 * w) * (fun w : ℝ => 1 - w))
          (2 * (1 - z) + 2 * z * (-1)) z := ha.mul hb
      refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards with w
        simp
      · ring
    have hden : HasDerivAt (fun w : ℝ => (1 + w) ^ 3) (3 * (1 + z) ^ 2) z := by
      have h0 : HasDerivAt ((fun w : ℝ => 1 + w) ^ 3) (3 * (1 + z) ^ 2) z := by
        refine ((((hasDerivAt_id' (x := z)).const_add (1 : ℝ)).pow 3).congr_deriv ?_)
        simp [hsub3]
      refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards with w
        simp
      · ring
    have hq : HasDerivAt (fun w : ℝ => PhiR 1 w / (1 + w) ^ 3)
        (2 * (1 - 4 * z + z ^ 2) / (1 + z) ^ 4) z := by
      refine (hnum.fun_div hden (pow_ne_zero 3 h1)).congr_deriv ?_
      simp only [PhiR_one]
      field_simp [h1, hp3, hp32]
      ring
    have hgoal : deriv (fun w : ℝ => PhiR 1 w / (1 + w) ^ 3) z
        = 2 * (1 - 4 * z + z ^ 2) / (1 + z) ^ 4 := by
      simpa using hq.deriv
    rw [hgoal, PhiR_two]
    ring
  · -- n = 2 :  PhiR 2 w = 2w(1-4w+w²),  PhiR 3 z = 2z(1-11z+11z²-z³)
    show z * deriv (fun w : ℝ => PhiR 2 w / (1 + w) ^ 4) z = PhiR 3 z / (1 + z) ^ 5
    have hsub2 : (2 : ℕ) - 1 = 1 := by norm_num
    have hsub4 : (4 : ℕ) - 1 = 3 := by norm_num
    have hp4 : (1 + z) ^ 4 ≠ 0 := pow_ne_zero 4 h1
    have hp42 : ((1 + z) ^ 4) ^ 2 ≠ 0 := pow_ne_zero 2 hp4
    have hsq : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by
      have h0 : HasDerivAt ((fun x : ℝ => x) ^ 2) (2 * z) z := by
        refine (((hasDerivAt_id' (x := z)).pow 2).congr_deriv ?_)
        simp [hsub2]
      refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards with w
        simp
      · ring
    have hquad : HasDerivAt (fun w : ℝ => 1 - 4 * w + w ^ 2) (-4 + 2 * z) z := by
      have h4 : HasDerivAt (fun w : ℝ => 4 * w) 4 z :=
        hasDerivAt_const_mul (c := (4 : ℝ)) (x := z)
      have hlin : HasDerivAt (fun w : ℝ => 1 - 4 * w) (0 - 4) z :=
        (hasDerivAt_const (c := (1 : ℝ)) (x := z)).sub h4
      exact (hlin.add hsq).congr_deriv (by ring)
    have ha : HasDerivAt (fun w : ℝ => 2 * w) 2 z :=
      hasDerivAt_const_mul (c := (2 : ℝ)) (x := z)
    have hnum : HasDerivAt (fun w : ℝ => PhiR 2 w)
        (2 * (1 - 4 * z + z ^ 2) + 2 * z * (-4 + 2 * z)) z := by
      have h0 : HasDerivAt ((fun w : ℝ => 2 * w) * (fun w : ℝ => 1 - 4 * w + w ^ 2))
          (2 * (1 - 4 * z + z ^ 2) + 2 * z * (-4 + 2 * z)) z := ha.mul hquad
      refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards with w
        simp
      · ring
    have hden : HasDerivAt (fun w : ℝ => (1 + w) ^ 4) (4 * (1 + z) ^ 3) z := by
      have h0 : HasDerivAt ((fun w : ℝ => 1 + w) ^ 4) (4 * (1 + z) ^ 3) z := by
        refine ((((hasDerivAt_id' (x := z)).const_add (1 : ℝ)).pow 4).congr_deriv ?_)
        simp [hsub4]
      refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards with w
        simp
      · ring
    have hq : HasDerivAt (fun w : ℝ => PhiR 2 w / (1 + w) ^ 4)
        (2 * (1 - 11 * z + 11 * z ^ 2 - z ^ 3) / (1 + z) ^ 5) z := by
      refine (hnum.fun_div hden (pow_ne_zero 4 h1)).congr_deriv ?_
      simp only [PhiR_two]
      field_simp [h1, hp4, hp42]
      ring
    have hgoal : deriv (fun w : ℝ => PhiR 2 w / (1 + w) ^ 4) z
        = 2 * (1 - 11 * z + 11 * z ^ 2 - z ^ 3) / (1 + z) ^ 5 := by
      simpa using hq.deriv
    rw [hgoal, PhiR_three]
    ring
  · -- n = 3 :  PhiR 3 w = 2w(1-11w+11w²-w³),  PhiR 4 z = 2z(1-26z+66z²-26z³+z⁴)
    show z * deriv (fun w : ℝ => PhiR 3 w / (1 + w) ^ 5) z = PhiR 4 z / (1 + z) ^ 6
    have hsub2 : (2 : ℕ) - 1 = 1 := by norm_num
    have hsub3 : (3 : ℕ) - 1 = 2 := by norm_num
    have hsub5 : (5 : ℕ) - 1 = 4 := by norm_num
    have hp5 : (1 + z) ^ 5 ≠ 0 := pow_ne_zero 5 h1
    have hp52 : ((1 + z) ^ 5) ^ 2 ≠ 0 := pow_ne_zero 2 hp5
    have hsq : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by
      have h0 : HasDerivAt ((fun x : ℝ => x) ^ 2) (2 * z) z := by
        refine (((hasDerivAt_id' (x := z)).pow 2).congr_deriv ?_)
        simp [hsub2]
      refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards with w
        simp
      · ring
    have hcu : HasDerivAt (fun w : ℝ => w ^ 3) (3 * z ^ 2) z := by
      have h0 : HasDerivAt ((fun x : ℝ => x) ^ 3) (3 * z ^ 2) z := by
        refine (((hasDerivAt_id' (x := z)).pow 3).congr_deriv ?_)
        simp [hsub3]
      refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards with w
        simp
      · ring
    have hcub : HasDerivAt (fun w : ℝ => 1 - 11 * w + 11 * w ^ 2 - w ^ 3)
        (-11 + 22 * z - 3 * z ^ 2) z := by
      have h11 : HasDerivAt (fun w : ℝ => 11 * w) 11 z :=
        hasDerivAt_const_mul (c := (11 : ℝ)) (x := z)
      have h11sq : HasDerivAt (fun w : ℝ => 11 * w ^ 2) (11 * (2 * z)) z :=
        hsq.const_mul (11 : ℝ)
      have hlin : HasDerivAt (fun w : ℝ => 1 - 11 * w) (0 - 11) z :=
        (hasDerivAt_const (c := (1 : ℝ)) (x := z)).sub h11
      exact ((hlin.add h11sq).sub hcu).congr_deriv (by ring)
    have ha : HasDerivAt (fun w : ℝ => 2 * w) 2 z :=
      hasDerivAt_const_mul (c := (2 : ℝ)) (x := z)
    have hnum : HasDerivAt (fun w : ℝ => PhiR 3 w)
        (2 * (1 - 11 * z + 11 * z ^ 2 - z ^ 3) + 2 * z * (-11 + 22 * z - 3 * z ^ 2)) z := by
      have h0 : HasDerivAt ((fun w : ℝ => 2 * w) * (fun w : ℝ => 1 - 11 * w + 11 * w ^ 2 - w ^ 3))
          (2 * (1 - 11 * z + 11 * z ^ 2 - z ^ 3) + 2 * z * (-11 + 22 * z - 3 * z ^ 2)) z :=
        ha.mul hcub
      refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards with w
        simp
      · ring
    have hden : HasDerivAt (fun w : ℝ => (1 + w) ^ 5) (5 * (1 + z) ^ 4) z := by
      have h0 : HasDerivAt ((fun w : ℝ => 1 + w) ^ 5) (5 * (1 + z) ^ 4) z := by
        refine ((((hasDerivAt_id' (x := z)).const_add (1 : ℝ)).pow 5).congr_deriv ?_)
        simp [hsub5]
      refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards with w
        simp
      · ring
    have hq : HasDerivAt (fun w : ℝ => PhiR 3 w / (1 + w) ^ 5)
        (2 * (1 - 26 * z + 66 * z ^ 2 - 26 * z ^ 3 + z ^ 4) / (1 + z) ^ 6) z := by
      refine (hnum.fun_div hden (pow_ne_zero 5 h1)).congr_deriv ?_
      simp only [PhiR_three]
      field_simp [h1, hp5, hp52]
      ring
    have hgoal : deriv (fun w : ℝ => PhiR 3 w / (1 + w) ^ 5) z
        = 2 * (1 - 26 * z + 66 * z ^ 2 - 26 * z ^ 3 + z ^ 4) / (1 + z) ^ 6 := by
      simpa using hq.deriv
    rw [hgoal, PhiR_four]
    ring

end Work.FTS.LocData
