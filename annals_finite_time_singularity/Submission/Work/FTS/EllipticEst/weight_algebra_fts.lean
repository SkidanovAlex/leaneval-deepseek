import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.EllipticEst.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open Filter

/-! ## Helper lemmas: the two derived weights and their derivatives

Throughout, the two derived weights are the rational functions

* `F z = z ^ 2 * w z ^ 2 = (1+z)^4 / z^2`,
* `G z = z * w z ^ 2 = (1+z)^4 / z^3`,

and all derivatives are computed by comparing with the rational functions
`(1+y)^4 / y^2`, `(1+y)^4 / y^3` and `2*(y-1)*(1+y)^3/y^3`, which agree with the
derived weights in a *neighbourhood* of every `z ≠ 0` (the punctured line is a
neighbourhood of `z`), so that `Filter.EventuallyEq.deriv_eq` transfers the
derivative. -/

/-- The first derived weight as a rational function: `z ^ 2 * w z ^ 2 = (1+z)^4/z^2`. -/
private lemma sq_mul_w_sq (z : ℝ) (hz : z ≠ 0) :
    z ^ 2 * (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 2 := by
  rw [Work.Spaces.w]
  field_simp

/-- The second derived weight as a rational function: `z * w z ^ 2 = (1+z)^4/z^3`. -/
private lemma mul_w_sq (z : ℝ) (hz : z ≠ 0) :
    z * (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 3 := by
  rw [Work.Spaces.w]
  field_simp

/-- The derivative of the rational function `(1+y)^4/y^2`. -/
private lemma deriv_rational_4_2 (z : ℝ) (hz : z ≠ 0) :
    deriv (fun y : ℝ => (1 + y) ^ 4 / y ^ 2) z = 2 * (z - 1) * (1 + z) ^ 3 / z ^ 3 := by
  rw [deriv_fun_div (c := fun y : ℝ => (1 + y) ^ 4) (d := fun y : ℝ => y ^ 2)
        (by fun_prop) (by fun_prop) (pow_ne_zero 2 hz),
      deriv_fun_pow (f := fun y : ℝ => 1 + y) (by fun_prop) 4,
      deriv_fun_pow (f := fun y : ℝ => y) (by fun_prop) 2,
      deriv_const_add (f := fun y : ℝ => y) (1 : ℝ), congr_fun deriv_id'' z]
  field_simp
  ring

/-- The derivative of the rational function `(1+y)^4/y^3`. -/
private lemma deriv_rational_4_3 (z : ℝ) (hz : z ≠ 0) :
    deriv (fun y : ℝ => (1 + y) ^ 4 / y ^ 3) z = (z - 3) * (1 + z) ^ 3 / z ^ 4 := by
  rw [deriv_fun_div (c := fun y : ℝ => (1 + y) ^ 4) (d := fun y : ℝ => y ^ 3)
        (by fun_prop) (by fun_prop) (pow_ne_zero 3 hz),
      deriv_fun_pow (f := fun y : ℝ => 1 + y) (by fun_prop) 4,
      deriv_fun_pow (f := fun y : ℝ => y) (by fun_prop) 3,
      deriv_const_add (f := fun y : ℝ => y) (1 : ℝ), congr_fun deriv_id'' z]
  field_simp
  ring

/-- The derivative of the rational function `2*(y-1)*(1+y)^3/y^3`. -/
private lemma deriv_rational_second (z : ℝ) (hz : z ≠ 0) :
    deriv (fun y : ℝ => 2 * (y - 1) * (1 + y) ^ 3 / y ^ 3) z
      = (1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) / z ^ 4 := by
  rw [deriv_fun_div (c := fun y : ℝ => 2 * (y - 1) * (1 + y) ^ 3) (d := fun y : ℝ => y ^ 3)
        (by fun_prop) (by fun_prop) (pow_ne_zero 3 hz)]
  rw [deriv_fun_mul (c := fun y : ℝ => 2 * (y - 1)) (d := fun y : ℝ => (1 + y) ^ 3)
        (by fun_prop) (by fun_prop)]
  rw [deriv_const_mul (c := (2 : ℝ)) (d := fun y : ℝ => y - 1) (by fun_prop)]
  rw [deriv_sub_const (f := fun y : ℝ => y) (1 : ℝ)]
  rw [deriv_fun_pow (f := fun y : ℝ => 1 + y) (by fun_prop) 3,
      deriv_fun_pow (f := fun y : ℝ => y) (by fun_prop) 3,
      deriv_const_add (f := fun y : ℝ => y) (1 : ℝ), congr_fun deriv_id'' z]
  field_simp
  ring

/-- `F = fun z => z ^ 2 * w z ^ 2` agrees with `(1+y)^4/y^2` near every `z ≠ 0`. -/
private lemma eventuallyEq_F (z : ℝ) (hz : z ≠ 0) :
    (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) =ᶠ[nhds z] (fun y : ℝ => (1 + y) ^ 4 / y ^ 2) := by
  filter_upwards [isOpen_ne.mem_nhds hz] with y hy
  exact sq_mul_w_sq y hy

/-- `G = fun z => z * w z ^ 2` agrees with `(1+y)^4/y^3` near every `z ≠ 0`. -/
private lemma eventuallyEq_G (z : ℝ) (hz : z ≠ 0) :
    (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) =ᶠ[nhds z] (fun y : ℝ => (1 + y) ^ 4 / y ^ 3) := by
  filter_upwards [isOpen_ne.mem_nhds hz] with y hy
  exact mul_w_sq y hy

/-- The first derivative of the derived weight `F`. -/
private lemma deriv_F (z : ℝ) (hz : z ≠ 0) :
    deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z
      = 2 * (z - 1) * (1 + z) ^ 3 / z ^ 3 := by
  rw [(eventuallyEq_F z hz).deriv_eq]
  exact deriv_rational_4_2 z hz

/-- The first derivative of the derived weight `G`. -/
private lemma deriv_G (z : ℝ) (hz : z ≠ 0) :
    deriv (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z = (z - 3) * (1 + z) ^ 3 / z ^ 4 := by
  rw [(eventuallyEq_G z hz).deriv_eq]
  exact deriv_rational_4_3 z hz

/-- The second derivative of the derived weight `F`. -/
private lemma deriv2_F (z : ℝ) (hz : z ≠ 0) :
    deriv (deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2)) z
      = (1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) / z ^ 4 := by
  have h2 : deriv (fun y : ℝ => (1 + y) ^ 4 / y ^ 2)
      =ᶠ[nhds z] (fun y : ℝ => 2 * (y - 1) * (1 + y) ^ 3 / y ^ 3) := by
    filter_upwards [isOpen_ne.mem_nhds hz] with y hy
    exact deriv_rational_4_2 y hy
  rw [((eventuallyEq_F z hz).deriv.trans h2).deriv_eq]
  exact deriv_rational_second z hz

/-- **The algebra of the radial weight `w z = (1+z)²/z²` and its two derived weights** `z²w²` (the coefficient of `-α²∂_zzΦ·Φ` after one integration by parts) and `z w²` (the coefficient of `-α(5+α)∂_zΦ·Φ`).  All identities hold for `z ≠ 0`; the two-sided bounds hold for `z > 0`, and the cruder bounds on the half-line `z ≥ 1` are the ones used to control the truncation error terms.

`z²w² = (1+z)^4/z^2 =: F`, `z w² = (1+z)^4/z^3 =: G`, `F' = 2(z-1)(1+z)^3/z^3`, `F'' = (1+z)^2(2z²-4z+6)/z^4`, `G' = (z-3)(1+z)^3/z^4`; `F'' ≤ 6w²`, `G' ≥ -3w²`, `F'' ≥ 0`; and for `z ≥ 1`: `|F'| ≤ 12z`, `F ≤ 16z²`, `G ≤ 16z`. -/
theorem weight_algebra_fts :
    (∀ z : ℝ, z ≠ 0 → z ^ 2 * (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 2) ∧
    (∀ z : ℝ, z ≠ 0 → z * (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 3) ∧
    (∀ z : ℝ, z ≠ 0 →
      deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z = 2 * (z - 1) * (1 + z) ^ 3 / z ^ 3) ∧
    (∀ z : ℝ, z ≠ 0 →
      deriv (fun z => z * (Work.Spaces.w z) ^ 2) z = (z - 3) * (1 + z) ^ 3 / z ^ 4) ∧
    (∀ z : ℝ, z ≠ 0 →
      deriv (deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2)) z
        = (1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) / z ^ 4) ∧
    (∀ z : ℝ, 0 < z →
      deriv (deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2)) z ≤ 6 * (Work.Spaces.w z) ^ 2) ∧
    (∀ z : ℝ, 0 < z →
      -3 * (Work.Spaces.w z) ^ 2 ≤ deriv (fun z => z * (Work.Spaces.w z) ^ 2) z) ∧
    (∀ z : ℝ, 0 < z → 0 ≤ deriv (deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2)) z) ∧
    (∀ z : ℝ, 1 ≤ z → |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z| ≤ 12 * z) ∧
    (∀ z : ℝ, 1 ≤ z → z ^ 2 * (Work.Spaces.w z) ^ 2 ≤ 16 * z ^ 2) ∧
    (∀ z : ℝ, 1 ≤ z → z * (Work.Spaces.w z) ^ 2 ≤ 16 * z) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact sq_mul_w_sq z hz
  · intro z hz
    exact mul_w_sq z hz
  · intro z hz
    exact deriv_F z hz
  · intro z hz
    exact deriv_G z hz
  · intro z hz
    exact deriv2_F z hz
  · -- `F'' ≤ 6 w²`
    intro z hz
    rw [deriv2_F z (ne_of_gt hz)]
    have hkey : 0 ≤ 6 * (Work.Spaces.w z) ^ 2
        - (1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) / z ^ 4 := by
      rw [Work.Spaces.w]
      rw [show 6 * ((1 + z) ^ 2 / z ^ 2) ^ 2 - (1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) / z ^ 4
          = (1 + z) ^ 2 * (4 * z ^ 2 + 16 * z) / z ^ 4 by
        field_simp
        ring]
      positivity
    linarith
  · -- `G' ≥ -3 w²`
    intro z hz
    rw [deriv_G z (ne_of_gt hz)]
    have hkey : 0 ≤ (z - 3) * (1 + z) ^ 3 / z ^ 4 + 3 * (Work.Spaces.w z) ^ 2 := by
      rw [Work.Spaces.w]
      rw [show (z - 3) * (1 + z) ^ 3 / z ^ 4 + 3 * ((1 + z) ^ 2 / z ^ 2) ^ 2
          = 4 * z * (1 + z) ^ 3 / z ^ 4 by
        field_simp
        ring]
      positivity
    linarith
  · -- `F'' ≥ 0`
    intro z hz
    rw [deriv2_F z (ne_of_gt hz)]
    have h1 : 0 < 2 * z ^ 2 - 4 * z + 6 := by nlinarith [sq_nonneg (z - 1)]
    positivity
  · -- `|F'| ≤ 12 z` for `z ≥ 1`
    intro z hz
    have hz0 : 0 < z := by linarith
    rw [deriv_F z (ne_of_gt hz0), abs_of_nonneg (by positivity)]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < z ^ 3)]
    nlinarith [sq_nonneg (z - 1), hz, sq_nonneg z, pow_pos hz0 3]
  · -- `F ≤ 16 z²` for `z ≥ 1`
    intro z hz
    have hz0 : 0 < z := by linarith
    rw [sq_mul_w_sq z (ne_of_gt hz0)]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
    have h : (1 + z) ^ 4 ≤ (2 * z) ^ 4 :=
      pow_le_pow_left₀ (by positivity) (by linarith : 1 + z ≤ 2 * z) 4
    nlinarith [h]
  · -- `G ≤ 16 z` for `z ≥ 1`
    intro z hz
    have hz0 : 0 < z := by linarith
    rw [mul_w_sq z (ne_of_gt hz0)]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < z ^ 3)]
    have h : (1 + z) ^ 4 ≤ (2 * z) ^ 4 :=
      pow_le_pow_left₀ (by positivity) (by linarith : 1 + z ≤ 2 * z) 4
    nlinarith [h]

end Work.FTS.EllipticEst
