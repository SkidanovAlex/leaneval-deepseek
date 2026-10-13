import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.StrongEps.ClassCRHS.DzBoundR2
import Submission.Work.FTS.StrongEps.ClassCRHS.StarAux
import Submission.Work.Elliptic.L12Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real

namespace Work.FTS.StrongEps.H5.Atoms

set_option autoImplicit false

open Work.FTS.StrongEps.ClassCRHS

/-! ## The level-`5` polynomial data for `SR2`

`DzBoundR2` provides the substitution `x = z/(1+z)` (with `D_z = x(1-x)∂_x`) and the
polynomials `polyR2 i` for `i ≤ 4`, together with their cofactors `AR2 i` satisfying
`polyR2 i x = x²(1-x)·AR2 i x`.  Here we add the missing level: the ordinary derivative
`dpolyR2_5` of `polyR2 4`, the iterate `polyR2_5 x = x(1-x)·(polyR2 4)' x`, and its
cofactor `AR2_5` (of degree `6`, with coefficient `ℓ¹`-norm `318158`). -/

/-- The ordinary derivative of `polyR2 4`
(`(32x² - 746x³ + 4834x⁴ - 13560x⁵ + 18800x⁶ - 12720x⁷ + 3360x⁸)'`). -/
def dpolyR2_5 (x : ℝ) : ℝ :=
  64 * x - 2238 * x ^ 2 + 19336 * x ^ 3 - 67800 * x ^ 4 + 112800 * x ^ 5 - 89040 * x ^ 6
    + 26880 * x ^ 7

/-- The level-`5` iterate `polyR2 5 x = x(1-x)·(polyR2 4)' x` in the variable `x = z/(1+z)`. -/
def polyR2_5 (x : ℝ) : ℝ := x * (1 - x) * dpolyR2_5 x

/-- The cofactor of `polyR2 5`: `polyR2 5 x = x²(1-x)·AR2_5 x`. -/
def AR2_5 (x : ℝ) : ℝ :=
  64 - 2238 * x + 19336 * x ^ 2 - 67800 * x ^ 3 + 112800 * x ^ 4 - 89040 * x ^ 5
    + 26880 * x ^ 6

/-- The polynomial cofactor of `polyR2 5`: `polyR2 5 x = x²(1-x)·AR2_5 x`. -/
lemma factor_polyR2_5 (x : ℝ) : polyR2_5 x = x ^ 2 * (1 - x) * AR2_5 x := by
  simp only [polyR2_5, dpolyR2_5, AR2_5]; ring

/-- The explicit derivative of `polyR2 4`. -/
lemma hasDerivAt_polyR2_four (x : ℝ) :
    HasDerivAt (polyR2 4) (dpolyR2_5 x) x := by
  have h2 : HasDerivAt
      (fun y : ℝ => 32 * y ^ 2 - 746 * y ^ 3 + 4834 * y ^ 4 - 13560 * y ^ 5
        + 18800 * y ^ 6 - 12720 * y ^ 7 + 3360 * y ^ 8)
      (64 * x - 2238 * x ^ 2 + 19336 * x ^ 3 - 67800 * x ^ 4 + 112800 * x ^ 5
        - 89040 * x ^ 6 + 26880 * x ^ 7) x := by
    have hc := (((((((hasDerivAt_pow 2 x).const_mul 32).sub
      ((hasDerivAt_pow 3 x).const_mul 746)).add
      ((hasDerivAt_pow 4 x).const_mul 4834)).sub
      ((hasDerivAt_pow 5 x).const_mul 13560)).add
      ((hasDerivAt_pow 6 x).const_mul 18800)).sub
      ((hasDerivAt_pow 7 x).const_mul 12720)).add
      ((hasDerivAt_pow 8 x).const_mul 3360)
    convert hc using 1
    norm_num
    ring
  simpa only [polyR2, dpolyR2_5] using h2

/-- The cofactor `AR2_5` is bounded by `318158` on `[0,1]` (its coefficient `ℓ¹`-norm is
`64 + 2238 + 19336 + 67800 + 112800 + 89040 + 26880 = 318158`). -/
lemma cof_bound_5 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : |AR2_5 x| ≤ 318158 := by
  have h2 : x ^ 2 ≤ 1 := pow_le_one₀ (n := 2) hx0 hx1
  have h3 : x ^ 3 ≤ 1 := pow_le_one₀ (n := 3) hx0 hx1
  have h4 : x ^ 4 ≤ 1 := pow_le_one₀ (n := 4) hx0 hx1
  have h5 : x ^ 5 ≤ 1 := pow_le_one₀ (n := 5) hx0 hx1
  have h6 : x ^ 6 ≤ 1 := pow_le_one₀ (n := 6) hx0 hx1
  have g2 : 0 ≤ x ^ 2 := pow_nonneg hx0 2
  have g3 : 0 ≤ x ^ 3 := pow_nonneg hx0 3
  have g4 : 0 ≤ x ^ 4 := pow_nonneg hx0 4
  have g5 : 0 ≤ x ^ 5 := pow_nonneg hx0 5
  have g6 : 0 ≤ x ^ 6 := pow_nonneg hx0 6
  simp only [AR2_5]
  rw [abs_le]
  constructor <;> nlinarith

/-- The `5`-th `D_z`-iterate of `SR2`, expressed through the substitution `x = z/(1+z)`. -/
lemma DzdIter_SR2_eq5 (z : ℝ) (hz : 1 + z ≠ 0) :
    Work.Elliptic.DzdIter 5 SR2 z = polyR2_5 (xtR2 z) := by
  have hz' : z ≠ -1 := by intro h; exact hz (by linarith)
  have hev : Work.Elliptic.DzdIter 4 SR2 =ᶠ[nhds z] fun w => polyR2 4 (xtR2 w) := by
    filter_upwards [eventually_ne_nhds hz'] with w hw
    exact DzdIter_SR2_eq 4 (le_refl 4) w (by intro h; exact hw (by linarith))
  have hcomp : deriv (fun w => polyR2 4 (xtR2 w)) z
      = dpolyR2_5 (xtR2 z) * (1 / (1 + z) ^ 2) := by
    have hX := hasDerivAt_xtR2 z hz
    have hp := hasDerivAt_polyR2_four (xtR2 z)
    exact (hp.comp z hX).deriv
  rw [show Work.Elliptic.DzdIter 5 SR2 z
        = z * deriv (Work.Elliptic.DzdIter 4 SR2) z from rfl, hev.deriv_eq, hcomp]
  rw [show z * (dpolyR2_5 (xtR2 z) * (1 / (1 + z) ^ 2))
        = xtR2 z * (1 - xtR2 z) * dpolyR2_5 (xtR2 z) from by
      calc z * (dpolyR2_5 (xtR2 z) * (1 / (1 + z) ^ 2))
            = (z * (1 / (1 + z) ^ 2)) * dpolyR2_5 (xtR2 z) := by ring
        _ = (xtR2 z * (1 - xtR2 z)) * dpolyR2_5 (xtR2 z) := by rw [mul_xtR2 z hz]]
  simp only [polyR2_5]

/-- `|D_z^5 SR2 z| ≤ 318158 z²/(1+z)³` for `z ≥ 0`. -/
lemma DzdIter_SR2_bound5 (z : ℝ) (hz0 : 0 ≤ z) :
    |Work.Elliptic.DzdIter 5 SR2 z| ≤ 318158 * z ^ 2 / (1 + z) ^ 3 := by
  have hz : 1 + z ≠ 0 := by positivity
  rw [DzdIter_SR2_eq5 z hz, factor_polyR2_5 (xtR2 z)]
  have hx0 : 0 ≤ xtR2 z := by simp only [xtR2]; positivity
  have hx1 : xtR2 z ≤ 1 := by
    simp only [xtR2]
    rw [div_le_one (by linarith : (0 : ℝ) < 1 + z)]
    linarith
  have hnn : 0 ≤ (xtR2 z) ^ 2 * (1 - xtR2 z) := by
    nlinarith [sq_nonneg (xtR2 z), hx1]
  have hcof := cof_bound_5 (xtR2 z) hx0 hx1
  calc |(xtR2 z) ^ 2 * (1 - xtR2 z) * AR2_5 (xtR2 z)|
      = (xtR2 z) ^ 2 * (1 - xtR2 z) * |AR2_5 (xtR2 z)| := by
        rw [abs_mul, abs_of_nonneg hnn]
    _ ≤ (xtR2 z) ^ 2 * (1 - xtR2 z) * 318158 := mul_le_mul_of_nonneg_left hcof hnn
    _ = 318158 * z ^ 2 / (1 + z) ^ 3 := by rw [sq_xtR2 z hz]; ring

/-- The level-`4` bound with the larger constant `318158`. -/
lemma bound_of_le4 (i : ℕ) (hi : i ≤ 4) (z : ℝ) (hz0 : 0 ≤ z) :
    |Work.Elliptic.DzdIter i SR2 z| ≤ 318158 * z ^ 2 / (1 + z) ^ 3 := by
  refine le_trans (DzdIter_SR2_bound i hi z hz0) ?_
  have hden : 0 ≤ (1 + z) ^ 3 := by positivity
  have hnum : 30000 * z ^ 2 ≤ 318158 * z ^ 2 := by nlinarith [sq_nonneg z]
  exact div_le_div_of_nonneg_right hnum hden

/-- The level-`5` radial iterates of `SR2 z = 2z²(1-z)/(1+z)⁴` are bounded by `C·z²/(1+z)³`
(the level-`4` version with `C = 30000` is `ClassCRHS.DzBoundR2`; `DzdIter i SR2 = z²P_i(z)/(1+z)^(4+i)`
with `deg P_i ≤ i+1`).  `DzBoundR2`'s file carries the useful substitution `x = z/(1+z)`,
under which `D_z = x(1-x)∂_x`, with the explicit polynomials `polyR2`/`AR2`; for `i = 5` one adds
`polyR2 5 = x(1-x)(polyR2 4)'` and its cofactor `AR2 5`.
The private lemmas of `DzBoundR2` may be copied into the new file (do not edit that file). -/
theorem DzIter_SR2_le5 : ∃ C : ℝ, 0 < C ∧ ∀ i : ℕ, i ≤ 5 → ∀ z : ℝ, 0 ≤ z →
    |Work.Elliptic.DzdIter i Work.FTS.StrongEps.ClassCRHS.SR2 z| ≤ C * z ^ 2 / (1 + z) ^ 3 := by
  refine ⟨318158, by norm_num, fun i hi z hz0 => ?_⟩
  by_cases h4 : i ≤ 4
  · exact bound_of_le4 i h4 z hz0
  · have h5 : i = 5 := by omega
    subst h5
    exact DzdIter_SR2_bound5 z hz0

end Work.FTS.StrongEps.H5.Atoms
