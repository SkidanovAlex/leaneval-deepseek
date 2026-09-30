import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

namespace Commons.Analysis.SpecialFunctions.Log

open Set

/-! Taylor-style lower bound for `Real.log (1 - x)` by the polynomial
`-(x + x^2/2 + x^3/3 + x^4/4 + x^5/5 + x^6/6) - 2*x^7/7`, valid for
`0 ≤ x ≤ 1/2`.

The error function
`G(x) = log (1 - x) + (x + x^2/2 + ... + x^6/6) + 2*x^7/7`
has derivative `x^6 * (1 - 2*x) / (1 - x) ≥ 0` on `[0, 1/2]` and vanishes at
`x = 0`; monotonicity on `[0, x]` gives the inequality. -/

private def Down7Fun (x : ℝ) : ℝ :=
  Real.log (1 - x) + (x + x ^ 2 / 2 + x ^ 3 / 3 + x ^ 4 / 4 + x ^ 5 / 5 + x ^ 6 / 6) +
    2 * x ^ 7 / 7

private lemma Down7Fun_hasDerivAt (a : ℝ) (ha : a < 1) :
    HasDerivAt Down7Fun (a ^ 6 * (1 - 2 * a) / (1 - a)) a := by
  have hne : (1 : ℝ) - a ≠ 0 := by linarith
  have harg : HasDerivAt (fun x : ℝ => 1 - x) (-1) a := by
    exact (hasDerivAt_id a).const_sub (1 : ℝ)
  have hlog : HasDerivAt (fun x : ℝ => Real.log (1 - x)) ((-1) / (1 - a)) a := by
    simpa using harg.log hne
  have hB := ((hasDerivAt_id a).pow 2).div_const (2 : ℝ)
  have hC := ((hasDerivAt_id a).pow 3).div_const (3 : ℝ)
  have hD := ((hasDerivAt_id a).pow 4).div_const (4 : ℝ)
  have hE := ((hasDerivAt_id a).pow 5).div_const (5 : ℝ)
  have hF := ((hasDerivAt_id a).pow 6).div_const (6 : ℝ)
  have h7 := (((hasDerivAt_id a).pow 7).const_mul (2 : ℝ)).div_const (7 : ℝ)
  have hS1 := (hasDerivAt_id a).add hB
  have hS2 := hS1.add hC
  have hS3 := hS2.add hD
  have hS4 := hS3.add hE
  have hS := hS4.add hF
  have htot := (hlog.add hS).add h7
  unfold Down7Fun
  convert htot using 1
  <;> first | rfl | (funext y; rfl) | (field_simp [hne]; simp; ring)

private lemma Down7Fun_deriv_nonneg (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ (1 : ℝ) / 2) :
    0 ≤ a ^ 6 * (1 - 2 * a) / (1 - a) := by
  have hnum : 0 ≤ a ^ 6 * (1 - 2 * a) := by
    exact mul_nonneg (pow_nonneg ha0 6) (by nlinarith)
  exact div_nonneg hnum (by linarith)

private lemma Down7Fun_nonneg (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ (1 : ℝ) / 2) :
    0 ≤ Down7Fun x := by
  have hxlt1 : x < 1 := by linarith
  have hcont : ContinuousOn Down7Fun (Set.Icc (0 : ℝ) x) := by
    intro y hy
    exact (Down7Fun_hasDerivAt y (by linarith [hy.2, hxlt1])).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ Down7Fun (interior (Set.Icc (0 : ℝ) x)) := by
    intro y hy
    have hyi : y ∈ Set.Ioo (0 : ℝ) x := by simpa [interior_Icc] using hy
    exact
      (Down7Fun_hasDerivAt y (by linarith [hyi.2, hxlt1])).differentiableAt.differentiableWithinAt
  have hnonneg : ∀ y ∈ interior (Set.Icc (0 : ℝ) x), 0 ≤ deriv Down7Fun y := by
    intro y hy
    have hyi : y ∈ Set.Ioo (0 : ℝ) x := by simpa [interior_Icc] using hy
    have hy0 : 0 ≤ y := by linarith [hyi.1]
    have hy1 : y < 1 := by linarith [hyi.2, hxlt1]
    have hyHalf : y ≤ (1 : ℝ) / 2 := by linarith [hyi.2, hx1]
    rw [(Down7Fun_hasDerivAt y hy1).deriv]
    exact Down7Fun_deriv_nonneg y hy0 hyHalf
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) x) hcont hdiff hnonneg
  have hmem0 : (0 : ℝ) ∈ Set.Icc 0 x := by exact ⟨le_rfl, hx0⟩
  have hmemX : x ∈ Set.Icc 0 x := by exact ⟨hx0, le_rfl⟩
  have hle := hmono hmem0 hmemX hx0
  have hD0 : Down7Fun 0 = 0 := by simp [Down7Fun]
  linarith

theorem log_one_sub_ge6 (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ (1 : ℝ) / 2) :
    -(u + u ^ 2 / 2 + u ^ 3 / 3 + u ^ 4 / 4 + u ^ 5 / 5 + u ^ 6 / 6) - 2 * u ^ 7 / 7 ≤
      Real.log (1 - u) := by
  have hU := Down7Fun_nonneg u hu0 hu1
  unfold Down7Fun at hU
  linarith

end Commons.Analysis.SpecialFunctions.Log