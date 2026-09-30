/-
Copyright: area `Profiles` of the aspherical 4-manifold project.

# The tangent extension of the exponential

`tangentExp K` is the convex `C¹` function which equals the tangent line `K e² (r - 1)` for
`r ≤ 2` and `K e^r` for `r ≥ 2`.  It is the model function that is smoothed against the bump
`eta` to produce the filling profiles.

Because it is defined as a primitive (`∫ s in 2..r, K * Real.exp (max s 2)`), all of
continuity, differentiability, monotonicity and convexity are immediate; the two "value"
lemmas reduce the interval integral to the value of a constant/exponential integrand.
-/
import Submission.Work.Profiles.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open MeasureTheory Filter
open scoped Interval ContDiff Topology

namespace Work.Profiles

theorem differentiable_tangentExp (K : ℝ) : Differentiable ℝ (tangentExp K) := by
  have h : Continuous fun s : ℝ => K * Real.exp (max s 2) := by fun_prop
  have h' := intervalIntegral.differentiable_integral_of_continuous (a := (2 : ℝ)) h
  exact h'.const_add (K * Real.exp 2)

theorem continuous_tangentExp (K : ℝ) : Continuous (tangentExp K) :=
  (differentiable_tangentExp K).continuous

theorem hasDerivAt_tangentExp (K r : ℝ) :
    HasDerivAt (tangentExp K) (K * Real.exp (max r 2)) r := by
  have h : Continuous fun s : ℝ => K * Real.exp (max s 2) := by fun_prop
  have h' := intervalIntegral.integral_hasDerivAt_right (a := (2 : ℝ)) (h.intervalIntegrable _ _)
    (h.stronglyMeasurableAtFilter volume (𝓝 r)) h.continuousAt
  exact h'.const_add (K * Real.exp 2)

theorem deriv_tangentExp (K r : ℝ) : deriv (tangentExp K) r = K * Real.exp (max r 2) :=
  (hasDerivAt_tangentExp K r).deriv

theorem tangentExp_eq_left {K r : ℝ} (hr : r ≤ 2) :
    tangentExp K r = K * Real.exp 2 * (r - 1) := by
  have hcongr : Set.EqOn (fun s : ℝ => K * Real.exp (max s 2))
      (fun _ : ℝ => K * Real.exp 2) [[(2 : ℝ), r]] := by
    intro s hs
    change K * Real.exp (max s 2) = K * Real.exp 2
    simp only [Set.mem_uIcc] at hs
    rw [max_eq_right]
    rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact le_trans h2 hr
    · exact h2
  rw [tangentExp, intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const]
  ring

theorem tangentExp_eq_right {K r : ℝ} (hr : 2 ≤ r) :
    tangentExp K r = K * Real.exp r := by
  have hcongr : Set.EqOn (fun s : ℝ => K * Real.exp (max s 2))
      (fun s : ℝ => K * Real.exp s) [[(2 : ℝ), r]] := by
    intro s hs
    change K * Real.exp (max s 2) = K * Real.exp s
    simp only [Set.mem_uIcc] at hs
    rw [max_eq_left]
    rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h1
    · exact le_trans hr h1
  have hexp : ∫ s in (2 : ℝ)..r, Real.exp s = Real.exp r - Real.exp 2 := by
    have h := intervalIntegral.integral_deriv_eq_sub (a := (2 : ℝ)) (b := r)
      (f := Real.exp) (fun x _ => Real.differentiableAt_exp)
      (by rw [Real.deriv_exp]; exact Real.continuous_exp.intervalIntegrable _ _)
    rwa [Real.deriv_exp] at h
  rw [tangentExp, intervalIntegral.integral_congr hcongr,
    intervalIntegral.integral_const_mul, hexp]
  ring

theorem monotone_tangentExp {K : ℝ} (hK : 0 ≤ K) : Monotone (tangentExp K) := by
  refine monotone_of_deriv_nonneg (differentiable_tangentExp K) fun r => ?_
  rw [deriv_tangentExp]
  positivity

theorem convexOn_tangentExp {K : ℝ} (hK : 0 ≤ K) : ConvexOn ℝ Set.univ (tangentExp K) := by
  refine Monotone.convexOn_univ_of_deriv (differentiable_tangentExp K) fun x y hxy => ?_
  rw [deriv_tangentExp, deriv_tangentExp]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (max_le_max hxy le_rfl)) hK

end Work.Profiles
