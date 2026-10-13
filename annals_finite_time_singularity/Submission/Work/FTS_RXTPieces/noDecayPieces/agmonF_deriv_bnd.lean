/-
# The Agmon-type derivative bound for the weighted radial flux `z ↦ z (v(z) w(z))²`

For a function `v : ℝ → ℝ` differentiable on the open half-line `(0,∞)` with derivative
`v'`, the weighted flux

  `F(y) = y * (v(y) * w(y))²`,   `w(y) = (1+y)²/y²`,

is differentiable at every `x > 0` with derivative

  `F'(x) = 2 v(x) (x v'(x)) w(x)² + v(x)² w(x)² (x-3)/(1+x)`,

because `w'/w = -2/(x(1+x))`; and the derivative is bounded pointwise by

  `|F'(x)| ≤ 4 (v(x) w(x))² + (x v'(x) w(x))²`,

since `2 |A| |B| ≤ A² + B²` and `|(x-3)/(1+x)| ≤ 3` for `x > 0`.  These are the pointwise
inputs of the Agmon-type weighted `L²` argument of the no-decay route of the construction
(see `Submission/Work/FTS_RegExport/NOTES_FINAL.md` §17).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RXTPieces.noDecayPieces

/-- The radial weight `w(z) = (1+z)²/z²` has `z`-derivative `-2(1+z)/z³` away from `z = 0`. -/
private lemma hasDerivAt_w {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt Work.Spaces.w (-2 * (1 + z) / z ^ 3) z := by
  have hnum : HasDerivAt (fun z : ℝ => (1 + z) ^ 2) (2 * (1 + z)) z := by
    convert ((hasDerivAt_id z).const_add 1).pow 2 using 1 <;> (first | rfl | simp)
  have hden : HasDerivAt (fun z : ℝ => z ^ 2) (2 * z) z := by
    convert (hasDerivAt_id z).pow 2 using 1 <;> (first | rfl | simp)
  have hne : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
  have h := hnum.div hden hne
  convert h using 1
  · rfl
  · field_simp
    ring

/-- `|(x-3)/(1+x)| ≤ 3` for `x > 0`. -/
private lemma abs_div_three_le (x : ℝ) (hx : 0 < x) : |(x - 3) / (1 + x)| ≤ 3 := by
  have h1 : (0 : ℝ) < 1 + x := by linarith
  rw [abs_div, abs_of_pos h1, div_le_iff₀ h1, abs_le]
  constructor <;> linarith

/-- The elementary inequality behind the Agmon bound: for `|q| ≤ 3`,
`|2 A B + A² q| ≤ 4 A² + B²`.  Indeed `2|A||B| ≤ A² + B²` and `A²|q| ≤ 3 A²`. -/
private lemma abs_two_mul_add_sq_le (A B q : ℝ) (hq : |q| ≤ 3) :
    |2 * A * B + A ^ 2 * q| ≤ 4 * A ^ 2 + B ^ 2 := by
  have h1 : |2 * A * B + A ^ 2 * q| ≤ 2 * |A| * |B| + |A| ^ 2 * |q| := by
    calc |2 * A * B + A ^ 2 * q| ≤ |2 * A * B| + |A ^ 2 * q| := abs_add_le _ _
      _ = 2 * |A| * |B| + |A| ^ 2 * |q| := by
        rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have h2 : 2 * |A| * |B| ≤ |A| ^ 2 + |B| ^ 2 := by
    have h := two_mul_le_add_sq |A| |B|
    linarith
  have h3 : |A| ^ 2 * |q| ≤ 3 * |A| ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hq (sq_nonneg |A|)
    nlinarith [h]
  calc |2 * A * B + A ^ 2 * q| ≤ 2 * |A| * |B| + |A| ^ 2 * |q| := h1
    _ ≤ (|A| ^ 2 + |B| ^ 2) + 3 * |A| ^ 2 := add_le_add h2 h3
    _ = 4 * A ^ 2 + B ^ 2 := by rw [sq_abs, sq_abs]; ring

theorem agmonF_deriv_bnd {v v' : ℝ → ℝ}
    (hv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt v (v' x) x) :
    ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => y * (v y * Work.Spaces.w y) ^ 2)
        (2 * v x * (x * v' x) * (Work.Spaces.w x) ^ 2
          + (v x) ^ 2 * (Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x))) x
      ∧ |2 * v x * (x * v' x) * (Work.Spaces.w x) ^ 2
            + (v x) ^ 2 * (Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x))|
          ≤ 4 * (v x * Work.Spaces.w x) ^ 2 + (x * v' x * Work.Spaces.w x) ^ 2 := by
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  have hxne : x ≠ 0 := ne_of_gt hx0
  refine ⟨?_, ?_⟩
  · -- the derivative: product rule, chain rule, and `w' = -2(1+x)/x³`
    have hvx : HasDerivAt v (v' x) x := hv x hx
    have hwx : HasDerivAt Work.Spaces.w (-2 * (1 + x) / x ^ 3) x := hasDerivAt_w hxne
    have hmul : HasDerivAt (fun y : ℝ => v y * Work.Spaces.w y)
        (v' x * Work.Spaces.w x + v x * (-2 * (1 + x) / x ^ 3)) x := hvx.mul hwx
    have hsq : HasDerivAt (fun y : ℝ => (v y * Work.Spaces.w y) ^ 2)
        (2 * (v x * Work.Spaces.w x) ^ (2 - 1)
          * (v' x * Work.Spaces.w x + v x * (-2 * (1 + x) / x ^ 3))) x := by
      convert hmul.pow 2 using 1
    have hprod := (hasDerivAt_id x).mul hsq
    refine hprod.congr_deriv ?_
    simp only [id_eq]
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one,
      show Work.Spaces.w x = (1 + x) ^ 2 / x ^ 2 from rfl]
    field_simp
    ring
  · -- the bound: triangle inequality, AM–GM, and `|(x-3)/(1+x)| ≤ 3`
    have hq : |(x - 3) / (1 + x)| ≤ 3 := abs_div_three_le x hx0
    have hmain := abs_two_mul_add_sq_le (v x * Work.Spaces.w x) (x * v' x * Work.Spaces.w x)
      ((x - 3) / (1 + x)) hq
    refine le_of_eq_of_le ?_ hmain
    congr 1
    ring

end Work.FTS_RXTPieces.noDecayPieces
