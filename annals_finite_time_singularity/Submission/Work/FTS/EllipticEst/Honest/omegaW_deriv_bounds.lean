import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.weight_derivs_explicit
import Submission.Work.FTS.EllipticEst.weight_algebra_fts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Derivative bounds for the truncated vorticity profile `z ↦ z w(z)² χ(z)`

`Work.Spaces.w z = (1+z)²/z²` is the radial weight of the paper.  This file proves the two
pointwise bounds needed for the *far field* of the truncated vorticity profile
`z ↦ z w(z)² χ(z)` and of the second `z`-derivative of `z ↦ z² w(z)² χ(z)`:

* `|d/dz (z w(z)² χ(z))| ≤ (3 + C₁) w(z)²`,
* `|d²/dz² (z² w(z)² χ(z))| ≤ (6 + 4C₁ + C₂) w(z)²`,

under the hypotheses `|z χ'(z)| ≤ C₁`, `|z² χ''(z)| ≤ C₂`, `|χ| ≤ 1` (so `χ` is a bounded
cutoff with bounded logarithmic derivatives, as produced by a smooth truncation).

The proof is an exact computation with the rational forms `w(z)² = (1+z)⁴/z⁴`,
`z w(z)² = (1+z)⁴/z³`, `z² w(z)² = (1+z)⁴/z²` and their derivatives (all available in
`Work.FTS.EllipticEst.weight_derivs_explicit`), followed by the elementary bounds
`|(z-3)/(1+z)| ≤ 3`, `|(2z²-4z+6)/(1+z)²| ≤ 6` and `|4(z-1)/(1+z)| ≤ 4` valid for `z > 0`.
-/

noncomputable section

open scoped Real Topology
open Filter

namespace Work.FTS.EllipticEst.Honest

/-! ## Elementary algebra of the weight `w` -/

/-- `w(z)² = (1+z)⁴/z⁴` for `z ≠ 0`. -/
private lemma w_sq_eq {z : ℝ} (hz : z ≠ 0) :
    (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
  rw [Work.Spaces.w]
  field_simp

/-- `z · w(z)² = (1+z)⁴/z³` for `z ≠ 0`. -/
private lemma mul_w_sq_eq {z : ℝ} (hz : z ≠ 0) :
    z * (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 3 := by
  rw [Work.Spaces.w]
  field_simp

/-- `z² · w(z)² = (1+z)⁴/z²` for `z ≠ 0`. -/
private lemma sq_mul_w_sq_eq {z : ℝ} (hz : z ≠ 0) :
    z ^ 2 * (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 2 := by
  rw [Work.Spaces.w]
  field_simp

/-! ## Elementary bounds valid on `z > 0` -/

/-- `|(z-3)/(1+z)| ≤ 3` for `z > 0` (the supremum `3` is approached as `z → 0⁺`). -/
private lemma abs_coef1 {z : ℝ} (hz : 0 < z) : |(z - 3) / (1 + z)| ≤ 3 := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  rw [abs_div, abs_of_pos h1z, div_le_iff₀ h1z, abs_le]
  constructor <;> linarith

/-- `|(2z²-4z+6)/(1+z)²| ≤ 6` for `z > 0` (the supremum `6` is attained at `z = 0`). -/
private lemma abs_coef2 {z : ℝ} (hz : 0 < z) : |(2 * z ^ 2 - 4 * z + 6) / (1 + z) ^ 2| ≤ 6 := by
  have hnum : 0 < 2 * z ^ 2 - 4 * z + 6 := by nlinarith [sq_nonneg (z - 1)]
  have hden : (0 : ℝ) < (1 + z) ^ 2 := by positivity
  rw [abs_div, abs_of_pos hnum, abs_of_pos hden, div_le_iff₀ hden]
  nlinarith [sq_nonneg z, hz]

/-- `|4(z-1)/(1+z)| ≤ 4` for `z > 0` (the supremum `4` is attained at `z = 0`). -/
private lemma abs_coef3 {z : ℝ} (hz : 0 < z) : |4 * (z - 1) / (1 + z)| ≤ 4 := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  rw [abs_div, abs_of_pos h1z, div_le_iff₀ h1z]
  have h : |z - 1| ≤ 1 + z := by rw [abs_le]; constructor <;> linarith
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  linarith

/-! ## The two derivative bounds -/

theorem omegaW_deriv_bounds {χ : ℝ → ℝ} {C₁ C₂ : ℝ}
    (hχ : ContDiff ℝ 2 χ) (hχ1 : ∀ z, |z * deriv χ z| ≤ C₁)
    (hχ2 : ∀ z, |z ^ 2 * deriv (deriv χ) z| ≤ C₂) (hχb : ∀ z, |χ z| ≤ 1)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    (∀ z, 0 < z → |deriv (fun y => y * ((Work.Spaces.w y) ^ 2 * χ y)) z|
        ≤ (3 + C₁) * (Work.Spaces.w z) ^ 2) ∧
    (∀ z, 0 < z → |deriv (fun y => deriv (fun x => x ^ 2 * ((Work.Spaces.w x) ^ 2 * χ x)) y) z|
        ≤ (6 + 4 * C₁ + C₂) * (Work.Spaces.w z) ^ 2) := by
  have hχd : Differentiable ℝ χ := hχ.differentiable (by norm_num)
  have hχ'd : Differentiable ℝ (deriv χ) := hχ.differentiable_deriv_two
  have hχat : ∀ y : ℝ, HasDerivAt χ (deriv χ y) y := fun y => (hχd y).hasDerivAt
  have hχ'at : ∀ y : ℝ, HasDerivAt (deriv χ) (deriv (deriv χ) y) y := fun y =>
    (hχ'd y).hasDerivAt
  constructor
  · -- first derivative of `y ↦ y w(y)² χ(y)`
    intro z hz
    have hz0 : z ≠ 0 := ne_of_gt hz
    -- the `y ↦ y w(y)²` part
    have h1 : HasDerivAt (fun y : ℝ => y * (Work.Spaces.w y) ^ 2)
        ((z - 3) * (1 + z) ^ 3 / z ^ 4) z := by
      have hev : (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) =ᶠ[𝓝 z]
          (fun y : ℝ => (1 + y) ^ 4 / y ^ 3) := by
        filter_upwards [isOpen_ne.mem_nhds hz0] with y hy
        exact mul_w_sq_eq hy
      exact (hev.hasDerivAt_iff).mpr (weight_derivs_explicit.2.2.1 z hz0)
    have hderiv : HasDerivAt (fun y : ℝ => y * (Work.Spaces.w y) ^ 2 * χ y)
        ((z - 3) * (1 + z) ^ 3 / z ^ 4 * χ z + z * (Work.Spaces.w z) ^ 2 * deriv χ z) z :=
      h1.mul (hχat z)
    -- move to the parenthesisation of the statement
    have hev0 : (fun y : ℝ => y * ((Work.Spaces.w y) ^ 2 * χ y)) =ᶠ[𝓝 z]
        (fun y : ℝ => y * (Work.Spaces.w y) ^ 2 * χ y) := by
      filter_upwards with y
      ring
    rw [hev0.deriv_eq, hderiv.deriv]
    have hw : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    -- factor out `w(z)²`
    have hfac : (z - 3) * (1 + z) ^ 3 / z ^ 4 * χ z + z * (Work.Spaces.w z) ^ 2 * deriv χ z
        = (Work.Spaces.w z) ^ 2 * (z * deriv χ z + (z - 3) / (1 + z) * χ z) := by
      have h1z : (1 + z) ≠ 0 := by linarith
      rw [mul_w_sq_eq hz0, w_sq_eq hz0]
      field_simp
      ring
    rw [hfac, abs_mul, abs_of_nonneg hw]
    calc (Work.Spaces.w z) ^ 2 * |z * deriv χ z + (z - 3) / (1 + z) * χ z|
        ≤ (Work.Spaces.w z) ^ 2 * (C₁ + 3) := by
          apply mul_le_mul_of_nonneg_left _ hw
          have h2 : |(z - 3) / (1 + z) * χ z| ≤ 3 := by
            rw [abs_mul]
            calc |(z - 3) / (1 + z)| * |χ z| ≤ |(z - 3) / (1 + z)| * 1 :=
                  mul_le_mul_of_nonneg_left (hχb z) (abs_nonneg _)
              _ = |(z - 3) / (1 + z)| := mul_one _
              _ ≤ 3 := abs_coef1 hz
          calc |z * deriv χ z + (z - 3) / (1 + z) * χ z|
              ≤ |z * deriv χ z| + |(z - 3) / (1 + z) * χ z| := abs_add_le _ _
            _ ≤ C₁ + 3 := add_le_add (hχ1 z) h2
      _ = (3 + C₁) * (Work.Spaces.w z) ^ 2 := by ring
  · -- second derivative of `y ↦ y² w(y)² χ(y)`
    intro z hz
    have hz0 : z ≠ 0 := ne_of_gt hz
    -- step A: the first derivative, on the punctured line
    have hA : ∀ y : ℝ, y ≠ 0 →
        deriv (fun x : ℝ => x ^ 2 * ((Work.Spaces.w x) ^ 2 * χ x)) y
          = 2 * (y - 1) * (1 + y) ^ 3 / y ^ 3 * χ y + (1 + y) ^ 4 / y ^ 2 * deriv χ y := by
      intro y hy
      have hev : (fun x : ℝ => x ^ 2 * ((Work.Spaces.w x) ^ 2 * χ x)) =ᶠ[𝓝 y]
          (fun x : ℝ => (1 + x) ^ 4 / x ^ 2 * χ x) := by
        filter_upwards [isOpen_ne.mem_nhds hy] with x hx
        rw [← mul_assoc, sq_mul_w_sq_eq hx]
      rw [hev.deriv_eq]
      have h1 : HasDerivAt (fun x : ℝ => (1 + x) ^ 4 / x ^ 2)
          (2 * (y - 1) * (1 + y) ^ 3 / y ^ 3) y := weight_derivs_explicit.1 y hy
      have hprod : HasDerivAt (fun x : ℝ => (1 + x) ^ 4 / x ^ 2 * χ x)
          (2 * (y - 1) * (1 + y) ^ 3 / y ^ 3 * χ y + (1 + y) ^ 4 / y ^ 2 * deriv χ y) y :=
        h1.mul (hχat y)
      exact hprod.deriv
    -- step B: transfer the outer derivative to the explicit expression
    have hev2 : (fun y : ℝ => deriv (fun x : ℝ => x ^ 2 * ((Work.Spaces.w x) ^ 2 * χ x)) y)
        =ᶠ[𝓝 z] (fun y : ℝ =>
          2 * (y - 1) * (1 + y) ^ 3 / y ^ 3 * χ y + (1 + y) ^ 4 / y ^ 2 * deriv χ y) := by
      filter_upwards [isOpen_ne.mem_nhds hz0] with y hy
      exact hA y hy
    rw [hev2.deriv_eq]
    -- step C: differentiate the two products
    have h1 : HasDerivAt (fun y : ℝ => 2 * (y - 1) * (1 + y) ^ 3 / y ^ 3 * χ y)
        ((1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) / z ^ 4 * χ z
          + 2 * (z - 1) * (1 + z) ^ 3 / z ^ 3 * deriv χ z) z :=
      (weight_derivs_explicit.2.1 z hz0).mul (hχat z)
    have h2 : HasDerivAt (fun y : ℝ => (1 + y) ^ 4 / y ^ 2 * deriv χ y)
        (2 * (z - 1) * (1 + z) ^ 3 / z ^ 3 * deriv χ z
          + (1 + z) ^ 4 / z ^ 2 * deriv (deriv χ) z) z :=
      (weight_derivs_explicit.1 z hz0).mul (hχ'at z)
    have hsum : deriv (fun y : ℝ =>
          2 * (y - 1) * (1 + y) ^ 3 / y ^ 3 * χ y + (1 + y) ^ 4 / y ^ 2 * deriv χ y) z
        = (1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) / z ^ 4 * χ z
          + 4 * (z - 1) * (1 + z) ^ 3 / z ^ 3 * deriv χ z
          + (1 + z) ^ 4 / z ^ 2 * deriv (deriv χ) z := by
      have hprod : HasDerivAt (fun y : ℝ =>
            2 * (y - 1) * (1 + y) ^ 3 / y ^ 3 * χ y + (1 + y) ^ 4 / y ^ 2 * deriv χ y)
          ((1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) / z ^ 4 * χ z
            + 2 * (z - 1) * (1 + z) ^ 3 / z ^ 3 * deriv χ z
            + (2 * (z - 1) * (1 + z) ^ 3 / z ^ 3 * deriv χ z
              + (1 + z) ^ 4 / z ^ 2 * deriv (deriv χ) z)) z :=
        h1.add h2
      rw [hprod.deriv]
      ring
    rw [hsum]
    have hw : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    -- factor out `w(z)²`
    have hfac : (1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) / z ^ 4 * χ z
          + 4 * (z - 1) * (1 + z) ^ 3 / z ^ 3 * deriv χ z
          + (1 + z) ^ 4 / z ^ 2 * deriv (deriv χ) z
        = (Work.Spaces.w z) ^ 2 * ((2 * z ^ 2 - 4 * z + 6) / (1 + z) ^ 2 * χ z
            + 4 * (z - 1) / (1 + z) * (z * deriv χ z)
            + z ^ 2 * deriv (deriv χ) z) := by
      have h1z : (1 + z) ≠ 0 := by linarith
      rw [w_sq_eq hz0]
      field_simp
    rw [hfac, abs_mul, abs_of_nonneg hw]
    calc (Work.Spaces.w z) ^ 2 * |(2 * z ^ 2 - 4 * z + 6) / (1 + z) ^ 2 * χ z
            + 4 * (z - 1) / (1 + z) * (z * deriv χ z) + z ^ 2 * deriv (deriv χ) z|
        ≤ (Work.Spaces.w z) ^ 2 * (6 + 4 * C₁ + C₂) := by
          apply mul_le_mul_of_nonneg_left _ hw
          have hA2 : |(2 * z ^ 2 - 4 * z + 6) / (1 + z) ^ 2 * χ z| ≤ 6 := by
            rw [abs_mul]
            calc |(2 * z ^ 2 - 4 * z + 6) / (1 + z) ^ 2| * |χ z|
                ≤ |(2 * z ^ 2 - 4 * z + 6) / (1 + z) ^ 2| * 1 :=
                  mul_le_mul_of_nonneg_left (hχb z) (abs_nonneg _)
              _ = |(2 * z ^ 2 - 4 * z + 6) / (1 + z) ^ 2| := mul_one _
              _ ≤ 6 := abs_coef2 hz
          have hB2 : |4 * (z - 1) / (1 + z) * (z * deriv χ z)| ≤ 4 * C₁ := by
            rw [abs_mul]
            calc |4 * (z - 1) / (1 + z)| * |z * deriv χ z|
                ≤ |4 * (z - 1) / (1 + z)| * C₁ :=
                  mul_le_mul_of_nonneg_left (hχ1 z) (abs_nonneg _)
              _ ≤ 4 * C₁ := mul_le_mul_of_nonneg_right (abs_coef3 hz) hC₁
          have h5 := hχ2 z
          calc |(2 * z ^ 2 - 4 * z + 6) / (1 + z) ^ 2 * χ z
                + 4 * (z - 1) / (1 + z) * (z * deriv χ z) + z ^ 2 * deriv (deriv χ) z|
              ≤ |(2 * z ^ 2 - 4 * z + 6) / (1 + z) ^ 2 * χ z
                  + 4 * (z - 1) / (1 + z) * (z * deriv χ z)|
                + |z ^ 2 * deriv (deriv χ) z| := abs_add_le _ _
            _ ≤ (|(2 * z ^ 2 - 4 * z + 6) / (1 + z) ^ 2 * χ z|
                  + |4 * (z - 1) / (1 + z) * (z * deriv χ z)|)
                + |z ^ 2 * deriv (deriv χ) z| := by
                exact add_le_add (abs_add_le _ _) le_rfl
            _ ≤ 6 + 4 * C₁ + C₂ := by linarith
      _ = (6 + 4 * C₁ + C₂) * (Work.Spaces.w z) ^ 2 := by ring

end Work.FTS.EllipticEst.Honest
