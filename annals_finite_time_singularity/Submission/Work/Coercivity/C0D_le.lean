/-
# `C0D ≤ 1/16`

`C0D = ∫_0^∞ (1/(s(1+s)w(s)))² ds` with `w(s) = (1+s)²/s²`.  On `(0,∞)` the integrand is
`s²/(1+s)⁶`, whose improper integral over `(0,∞)` equals `1/30` (antiderivative
`-1/(3(1+s)³) + 1/(2(1+s)⁴) - 1/(5(1+s)⁵)`).  Hence `C0D = 1/30 ≤ 1/16`.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.Coercivity.C0Defs
import Submission.Work.FM.Core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- Antiderivative of `s²/(1+s)⁶`: `G(s) = -1/(3(1+s)³) + 1/(2(1+s)⁴) - 1/(5(1+s)⁵)`. -/
private def c0G (s : ℝ) : ℝ :=
  (-1 / 3) * ((1 + s)⁻¹) ^ 3 + (1 / 2) * ((1 + s)⁻¹) ^ 4 - (1 / 5) * ((1 + s)⁻¹) ^ 5

/-- `G'(s) = s²/(1+s)⁶` for `s ≥ 0`. -/
private lemma c0G_hasDerivAt (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt c0G (x ^ 2 / (1 + x) ^ 6) x := by
  have hx1 : (1 : ℝ) + x ≠ 0 := by positivity
  have hbase : HasDerivAt (fun t : ℝ => ((1 : ℝ) + t)⁻¹) (-1 / (1 + x) ^ 2) x :=
    Work.FM.hasDerivAt_inv_add_const 1 x hx1
  have h1 : HasDerivAt (fun t : ℝ => (-1 / 3) * ((1 + t)⁻¹) ^ 3)
      ((-1 / 3) * (3 * ((1 + x)⁻¹) ^ 2 * (-1 / (1 + x) ^ 2))) x :=
    (hbase.pow 3).const_mul (-1 / 3)
  have h2 : HasDerivAt (fun t : ℝ => (1 / 2) * ((1 + t)⁻¹) ^ 4)
      ((1 / 2) * (4 * ((1 + x)⁻¹) ^ 3 * (-1 / (1 + x) ^ 2))) x :=
    (hbase.pow 4).const_mul (1 / 2)
  have h3 : HasDerivAt (fun t : ℝ => (1 / 5) * ((1 + t)⁻¹) ^ 5)
      ((1 / 5) * (5 * ((1 + x)⁻¹) ^ 4 * (-1 / (1 + x) ^ 2))) x :=
    (hbase.pow 5).const_mul (1 / 5)
  have hG : HasDerivAt c0G
      (((-1 / 3) * (3 * ((1 + x)⁻¹) ^ 2 * (-1 / (1 + x) ^ 2)))
        + ((1 / 2) * (4 * ((1 + x)⁻¹) ^ 3 * (-1 / (1 + x) ^ 2)))
        - ((1 / 5) * (5 * ((1 + x)⁻¹) ^ 4 * (-1 / (1 + x) ^ 2)))) x :=
    (h1.add h2).sub h3
  have hval : ((-1 / 3) * (3 * ((1 + x)⁻¹) ^ 2 * (-1 / (1 + x) ^ 2)))
        + ((1 / 2) * (4 * ((1 + x)⁻¹) ^ 3 * (-1 / (1 + x) ^ 2)))
        - ((1 / 5) * (5 * ((1 + x)⁻¹) ^ 4 * (-1 / (1 + x) ^ 2)))
      = x ^ 2 / (1 + x) ^ 6 := by
    field_simp
    ring
  rw [hval] at hG
  exact hG

/-- `G(s) → 0` as `s → +∞`. -/
private lemma c0G_tendsto : Tendsto c0G atTop (𝓝 0) := by
  change Tendsto (fun t : ℝ => (-1 / 3) * ((1 + t)⁻¹) ^ 3 + (1 / 2) * ((1 + t)⁻¹) ^ 4
      - (1 / 5) * ((1 + t)⁻¹) ^ 5) atTop (𝓝 0)
  have h1 : Tendsto (fun t : ℝ => (1 : ℝ) + t) atTop atTop :=
    tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id
  have h2 : Tendsto (fun t : ℝ => ((1 : ℝ) + t)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp h1
  have h3 : Tendsto (fun t : ℝ => ((1 : ℝ) + t)⁻¹ ^ 3) atTop (𝓝 0) := by
    simpa using h2.pow 3
  have h4 : Tendsto (fun t : ℝ => ((1 : ℝ) + t)⁻¹ ^ 4) atTop (𝓝 0) := by
    simpa using h2.pow 4
  have h5 : Tendsto (fun t : ℝ => ((1 : ℝ) + t)⁻¹ ^ 5) atTop (𝓝 0) := by
    simpa using h2.pow 5
  have hG := ((h3.const_mul (-1 / 3)).add (h4.const_mul (1 / 2))).sub (h5.const_mul (1 / 5))
  simpa using hG

/-- `s²/(1+s)⁶ ≥ 0` on `(0,∞)`. -/
private lemma c0G'_nonneg {x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    0 ≤ x ^ 2 / (1 + x) ^ 6 := by
  have hx' : (0 : ℝ) < x := hx
  have hx1 : (0 : ℝ) < 1 + x := by linarith
  positivity

/-- The improper integral `∫_0^∞ s²/(1+s)⁶ ds = 1/30`. -/
private lemma c0D_integral_key : ∫ s in Set.Ioi (0 : ℝ), s ^ 2 / (1 + s) ^ 6 = 1 / 30 := by
  have key := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
    (g := c0G) (g' := fun t : ℝ => t ^ 2 / (1 + t) ^ 6) (a := 0) (l := 0)
    (fun x hx => c0G_hasDerivAt x hx) (fun x hx => c0G'_nonneg hx) c0G_tendsto
  rw [key]
  norm_num [c0G]

/-- `C0D = 1/30`. -/
private lemma c0D_eq : C0D = 1 / 30 := by
  have hcongr : ∫ s in Set.Ioi (0 : ℝ), (1 / (s * (1 + s) * Spaces.w s)) ^ 2
      = ∫ s in Set.Ioi (0 : ℝ), s ^ 2 / (1 + s) ^ 6 := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    have hs' : (0 : ℝ) < s := hs
    have hs0 : s ≠ 0 := ne_of_gt hs'
    have hs1 : (1 : ℝ) + s ≠ 0 := by
      have : (0 : ℝ) < 1 + s := by linarith
      positivity
    rw [Spaces.w]
    field_simp
  unfold C0D
  rw [hcongr, c0D_integral_key]

theorem C0D_le : C0D ≤ 1 / 16 := by
  rw [c0D_eq]
  norm_num

end

end Work.Coercivity
