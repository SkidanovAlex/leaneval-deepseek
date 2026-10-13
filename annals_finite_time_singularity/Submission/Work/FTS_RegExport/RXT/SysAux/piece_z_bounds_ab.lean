import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXT.SysAux.PieceDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `piece_z_bounds_ab` — the radial one-variable bounds for `A1` and `B1`

`ZIter j A = (z ∂_z)^j A` is the one-variable version of the radial operator `D_z`
(`Work.FTS_RegExport.RXT.SysAux.PieceDefs`).  Here we bound its first three iterates for the
two radial profiles of the forcing decomposition,

  `A₁(z) = 2z(1-z)/(1+z)³`  and  `B₁(z) = 2z/(1+z)²`,

by `30·z/(1+z)²` respectively `10·z/(1+z)²` for `z > 0`.  Everything is completely explicit:
the iterates are the rational functions

  `ZIter 0 A₁ = 2z(1-z)/(1+z)³`,  `ZIter 1 A₁ = 2z(1-4z+z²)/(1+z)⁴`,
  `ZIter 2 A₁ = 2z(1-11z+11z²-z³)/(1+z)⁵`,
  `ZIter 0 B₁ = 2z/(1+z)²`,  `ZIter 1 B₁ = 2z(1-z)/(1+z)³`,  `ZIter 2 B₁ = 2z(1-4z+z²)/(1+z)⁴`,

and the bounds follow from the elementary estimates `|1-z| ≤ 1+z`, `|1-4z+z²| ≤ 4(1+z)²`,
`|1-11z+11z²-z³| ≤ 11(1+z)³` for `z > 0`.
-/

open scoped Real Topology

namespace Work.FTS_RegExport.RXT.SysAux

set_option autoImplicit false

/-! ### The explicit derivatives -/

private lemma deriv_f (z : ℝ) (hz : 0 < z) :
    deriv (fun w : ℝ => 2 * w * (1 - w) / (1 + w) ^ 3) z
      = 2 * (1 - 4 * z + z ^ 2) / (1 + z) ^ 4 := by
  have hden : (1 + z) ^ 3 ≠ 0 := by positivity
  have h : HasDerivAt (fun w : ℝ => 2 * w * (1 - w) / (1 + w) ^ 3)
      (2 * (1 - 4 * z + z ^ 2) / (1 + z) ^ 4) z := by
    have h1 : HasDerivAt (fun w : ℝ => 1 + w) (1 : ℝ) z := (hasDerivAt_id' z).const_add 1
    have h2 : HasDerivAt (fun w : ℝ => (1 + w) ^ 3) (3 * (1 + z) ^ 2) z := by
      simpa using h1.fun_pow 3
    have ha : HasDerivAt (fun w : ℝ => 2 * w) (2 : ℝ) z := by
      simpa using (hasDerivAt_id' z).const_mul 2
    have hb : HasDerivAt (fun w : ℝ => 1 - w) (-1 : ℝ) z := by
      simpa using (hasDerivAt_id' z).const_sub 1
    have h3 : HasDerivAt (fun w : ℝ => 2 * w * (1 - w)) (2 - 4 * z) z := by
      have hm := ha.mul hb
      convert hm using 1
      ring
    have h4 := h3.div h2 hden
    convert h4 using 1
    field_simp
    ring
  rw [h.deriv]

private lemma deriv_g (z : ℝ) (hz : 0 < z) :
    deriv (fun w : ℝ => 2 * w / (1 + w) ^ 2) z = 2 * (1 - z) / (1 + z) ^ 3 := by
  have hden : (1 + z) ^ 2 ≠ 0 := by positivity
  have h : HasDerivAt (fun w : ℝ => 2 * w / (1 + w) ^ 2) (2 * (1 - z) / (1 + z) ^ 3) z := by
    have h1 : HasDerivAt (fun w : ℝ => 1 + w) (1 : ℝ) z := (hasDerivAt_id' z).const_add 1
    have h2 : HasDerivAt (fun w : ℝ => (1 + w) ^ 2) (2 * (1 + z)) z := by
      have hp := h1.fun_pow 2
      simpa using hp
    have ha : HasDerivAt (fun w : ℝ => 2 * w) (2 : ℝ) z := by
      simpa using (hasDerivAt_id' z).const_mul 2
    have h4 := ha.div h2 hden
    convert h4 using 1
    field_simp
    ring
  rw [h.deriv]

private lemma deriv_e1 (z : ℝ) (hz : 0 < z) :
    deriv (fun w : ℝ => 2 * w * (1 - 4 * w + w ^ 2) / (1 + w) ^ 4) z
      = 2 * (1 - 11 * z + 11 * z ^ 2 - z ^ 3) / (1 + z) ^ 5 := by
  have hden : (1 + z) ^ 4 ≠ 0 := by positivity
  have h : HasDerivAt (fun w : ℝ => 2 * w * (1 - 4 * w + w ^ 2) / (1 + w) ^ 4)
      (2 * (1 - 11 * z + 11 * z ^ 2 - z ^ 3) / (1 + z) ^ 5) z := by
    have h1 : HasDerivAt (fun w : ℝ => 1 + w) (1 : ℝ) z := (hasDerivAt_id' z).const_add 1
    have h2 : HasDerivAt (fun w : ℝ => (1 + w) ^ 4) (4 * (1 + z) ^ 3) z := by
      simpa using h1.fun_pow 4
    have ha : HasDerivAt (fun w : ℝ => 2 * w) (2 : ℝ) z := by
      simpa using (hasDerivAt_id' z).const_mul 2
    have hb1 : HasDerivAt (fun w : ℝ => 1 - 4 * w) (-4 : ℝ) z := by
      simpa using ((hasDerivAt_id' z).const_mul 4).const_sub 1
    have hb2 : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by
      simpa using hasDerivAt_pow 2 z
    have hb : HasDerivAt (fun w : ℝ => 1 - 4 * w + w ^ 2) (-4 + 2 * z) z := hb1.add hb2
    have h3 : HasDerivAt (fun w : ℝ => 2 * w * (1 - 4 * w + w ^ 2)) (2 - 16 * z + 6 * z ^ 2) z := by
      have hm := ha.mul hb
      convert hm using 1
      ring
    have h4 := h3.div h2 hden
    convert h4 using 1
    field_simp
    ring
  rw [h.deriv]

/-! ### The explicit iterates -/

private lemma ZIter_f_one (z : ℝ) (hz : 0 < z) :
    ZIter 1 (fun z : ℝ => 2 * z * (1 - z) / (1 + z) ^ 3) z
      = 2 * z * (1 - 4 * z + z ^ 2) / (1 + z) ^ 4 := by
  rw [ZIter_succ_apply, ZIter_zero]
  have hd : deriv (fun z : ℝ => 2 * z * (1 - z) / (1 + z) ^ 3) z
      = 2 * (1 - 4 * z + z ^ 2) / (1 + z) ^ 4 := deriv_f z hz
  rw [hd]
  ring

private lemma ZIter_f_two (z : ℝ) (hz : 0 < z) :
    ZIter 2 (fun z : ℝ => 2 * z * (1 - z) / (1 + z) ^ 3) z
      = 2 * z * (1 - 11 * z + 11 * z ^ 2 - z ^ 3) / (1 + z) ^ 5 := by
  rw [ZIter_succ_apply]
  have hev : (fun w => ZIter 1 (fun w : ℝ => 2 * w * (1 - w) / (1 + w) ^ 3) w)
      =ᶠ[𝓝 z] fun w => 2 * w * (1 - 4 * w + w ^ 2) / (1 + w) ^ 4 := by
    filter_upwards [eventually_gt_nhds hz] with w hw
    exact ZIter_f_one w hw
  have hd : deriv (ZIter 1 (fun z : ℝ => 2 * z * (1 - z) / (1 + z) ^ 3)) z
      = deriv (fun w : ℝ => 2 * w * (1 - 4 * w + w ^ 2) / (1 + w) ^ 4) z := hev.deriv_eq
  rw [hd, deriv_e1 z hz]
  ring

private lemma ZIter_g_one (z : ℝ) (hz : 0 < z) :
    ZIter 1 (fun z : ℝ => 2 * z / (1 + z) ^ 2) z = 2 * z * (1 - z) / (1 + z) ^ 3 := by
  rw [ZIter_succ_apply, ZIter_zero]
  have hd : deriv (fun z : ℝ => 2 * z / (1 + z) ^ 2) z = 2 * (1 - z) / (1 + z) ^ 3 :=
    deriv_g z hz
  rw [hd]
  ring

private lemma ZIter_g_two (z : ℝ) (hz : 0 < z) :
    ZIter 2 (fun z : ℝ => 2 * z / (1 + z) ^ 2) z
      = 2 * z * (1 - 4 * z + z ^ 2) / (1 + z) ^ 4 := by
  rw [ZIter_succ_apply]
  have hev : (fun w => ZIter 1 (fun w : ℝ => 2 * w / (1 + w) ^ 2) w)
      =ᶠ[𝓝 z] fun w => 2 * w * (1 - w) / (1 + w) ^ 3 := by
    filter_upwards [eventually_gt_nhds hz] with w hw
    exact ZIter_g_one w hw
  have hd : deriv (ZIter 1 (fun z : ℝ => 2 * z / (1 + z) ^ 2)) z
      = deriv (fun w : ℝ => 2 * w * (1 - w) / (1 + w) ^ 3) z := hev.deriv_eq
  rw [hd, deriv_f z hz]
  ring

/-! ### The master estimate -/

/-- `|Nz| ≤ C·z·(1+z)^m` gives `|Nz/(1+z)^(m+2)| ≤ C·z/(1+z)²` for `z > 0`. -/
private lemma div_bound (z : ℝ) (hz : 0 < z) (m : ℕ) (C Nz : ℝ)
    (hN : |Nz| ≤ C * z * (1 + z) ^ m) :
    |Nz / (1 + z) ^ (m + 2)| ≤ C * (z / (1 + z) ^ 2) := by
  have hz1 : 0 < 1 + z := by linarith
  have hden : 0 < (1 + z) ^ (m + 2) := by positivity
  have hm0 : (1 + z) ^ m ≠ 0 := by positivity
  rw [abs_div, abs_of_pos hden]
  have hsplit : (1 + z) ^ (m + 2) = (1 + z) ^ m * (1 + z) ^ 2 := by rw [pow_add]
  calc |Nz| / (1 + z) ^ (m + 2)
      ≤ C * z * (1 + z) ^ m / ((1 + z) ^ m * (1 + z) ^ 2) := by
        rw [hsplit]
        exact div_le_div_of_nonneg_right hN (by positivity)
    _ = C * (z / (1 + z) ^ 2) := by field_simp

/-! ### Elementary absolute-value bounds -/

private lemma abs_one_sub (z : ℝ) (hz : 0 < z) : |1 - z| ≤ 1 + z := by
  rw [abs_le]
  constructor <;> linarith

private lemma abs_quad (z : ℝ) (hz : 0 < z) : |1 - 4 * z + z ^ 2| ≤ 4 * (1 + z) ^ 2 := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg z]

private lemma abs_cubic (z : ℝ) (hz : 0 < z) :
    |1 - 11 * z + 11 * z ^ 2 - z ^ 3| ≤ 11 * (1 + z) ^ 3 := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg z, mul_pos hz hz, sq_nonneg (z - 1)]

/-! ### The numerator estimates -/

private lemma hN_f_30 (z : ℝ) (hz : 0 < z) :
    |2 * z * (1 - z)| ≤ 30 * z * (1 + z) ^ 1 := by
  rw [pow_one]
  have hz2 : (0 : ℝ) ≤ 2 * z := by linarith
  calc |2 * z * (1 - z)| = 2 * z * |1 - z| := by rw [abs_mul, abs_of_nonneg hz2]
    _ ≤ 2 * z * (1 + z) := mul_le_mul_of_nonneg_left (abs_one_sub z hz) hz2
    _ ≤ 30 * z * (1 + z) := by nlinarith

private lemma hN_e1_30 (z : ℝ) (hz : 0 < z) :
    |2 * z * (1 - 4 * z + z ^ 2)| ≤ 30 * z * (1 + z) ^ 2 := by
  have hz2 : (0 : ℝ) ≤ 2 * z := by linarith
  calc |2 * z * (1 - 4 * z + z ^ 2)| = 2 * z * |1 - 4 * z + z ^ 2| := by
        rw [abs_mul, abs_of_nonneg hz2]
    _ ≤ 2 * z * (4 * (1 + z) ^ 2) := mul_le_mul_of_nonneg_left (abs_quad z hz) hz2
    _ ≤ 30 * z * (1 + z) ^ 2 := by nlinarith

private lemma hN_e2_30 (z : ℝ) (hz : 0 < z) :
    |2 * z * (1 - 11 * z + 11 * z ^ 2 - z ^ 3)| ≤ 30 * z * (1 + z) ^ 3 := by
  have hz2 : (0 : ℝ) ≤ 2 * z := by linarith
  have hz3 : (0 : ℝ) ≤ z * (1 + z) ^ 3 := by positivity
  calc |2 * z * (1 - 11 * z + 11 * z ^ 2 - z ^ 3)|
        = 2 * z * |1 - 11 * z + 11 * z ^ 2 - z ^ 3| := by rw [abs_mul, abs_of_nonneg hz2]
    _ ≤ 2 * z * (11 * (1 + z) ^ 3) := mul_le_mul_of_nonneg_left (abs_cubic z hz) hz2
    _ ≤ 30 * z * (1 + z) ^ 3 := by nlinarith

private lemma hN_g_10 (z : ℝ) (hz : 0 < z) :
    |2 * z| ≤ 10 * z * (1 + z) ^ 0 := by
  rw [pow_zero, mul_one]
  have hz2 : (0 : ℝ) ≤ 2 * z := by linarith
  rw [abs_of_nonneg hz2]
  linarith

private lemma hN_f_10 (z : ℝ) (hz : 0 < z) :
    |2 * z * (1 - z)| ≤ 10 * z * (1 + z) ^ 1 := by
  rw [pow_one]
  have hz2 : (0 : ℝ) ≤ 2 * z := by linarith
  calc |2 * z * (1 - z)| = 2 * z * |1 - z| := by rw [abs_mul, abs_of_nonneg hz2]
    _ ≤ 2 * z * (1 + z) := mul_le_mul_of_nonneg_left (abs_one_sub z hz) hz2
    _ ≤ 10 * z * (1 + z) := by nlinarith

private lemma hN_e1_10 (z : ℝ) (hz : 0 < z) :
    |2 * z * (1 - 4 * z + z ^ 2)| ≤ 10 * z * (1 + z) ^ 2 := by
  have hz2 : (0 : ℝ) ≤ 2 * z := by linarith
  calc |2 * z * (1 - 4 * z + z ^ 2)| = 2 * z * |1 - 4 * z + z ^ 2| := by
        rw [abs_mul, abs_of_nonneg hz2]
    _ ≤ 2 * z * (4 * (1 + z) ^ 2) := mul_le_mul_of_nonneg_left (abs_quad z hz) hz2
    _ ≤ 10 * z * (1 + z) ^ 2 := by nlinarith

theorem piece_z_bounds_ab : ∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
    (|ZIter j (fun z : ℝ => 2 * z * (1 - z) / (1 + z) ^ 3) z| ≤ 30 * (z / (1 + z) ^ 2)) ∧
    (|ZIter j (fun z : ℝ => 2 * z / (1 + z) ^ 2) z| ≤ 10 * (z / (1 + z) ^ 2)) := by
  intro j hj z hz
  interval_cases j
  · constructor
    · simp only [ZIter_zero]
      exact div_bound z hz 1 30 (2 * z * (1 - z)) (hN_f_30 z hz)
    · simp only [ZIter_zero]
      exact div_bound z hz 0 10 (2 * z) (hN_g_10 z hz)
  · constructor
    · rw [ZIter_f_one z hz]
      exact div_bound z hz 2 30 (2 * z * (1 - 4 * z + z ^ 2)) (hN_e1_30 z hz)
    · rw [ZIter_g_one z hz]
      exact div_bound z hz 1 10 (2 * z * (1 - z)) (hN_f_10 z hz)
  · constructor
    · rw [ZIter_f_two z hz]
      exact div_bound z hz 3 30 (2 * z * (1 - 11 * z + 11 * z ^ 2 - z ^ 3)) (hN_e2_30 z hz)
    · rw [ZIter_g_two z hz]
      exact div_bound z hz 2 10 (2 * z * (1 - 4 * z + z ^ 2)) (hN_e1_10 z hz)

end Work.FTS_RegExport.RXT.SysAux
