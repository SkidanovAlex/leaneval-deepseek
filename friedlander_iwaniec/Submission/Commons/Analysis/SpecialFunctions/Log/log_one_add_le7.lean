import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

namespace Commons.Analysis.SpecialFunctions.Log

open Set

/-! Taylor-style upper bound for `Real.log (1 + y)` by the polynomial
`y - y^2/2 + y^3/3 - y^4/4 + y^5/5 - y^6/6 + y^7/7`, valid for all `y ≥ 0`.

The error function `S₇(y) - log (1 + y)` has derivative `y^7 / (1 + y) ≥ 0`
and vanishes at `y = 0`; monotonicity on `[0, y]` gives the inequality. -/

private def Up7Fun (y : ℝ) : ℝ :=
  (y - y ^ 2 / 2 + y ^ 3 / 3 - y ^ 4 / 4 + y ^ 5 / 5 - y ^ 6 / 6 + y ^ 7 / 7) -
    Real.log (1 + y)

private lemma Up7Fun_hasDerivAt (a : ℝ) (ha : 0 ≤ a) :
    HasDerivAt Up7Fun (a ^ 7 / (1 + a)) a := by
  have hne : (1 : ℝ) + a ≠ 0 := by nlinarith
  have harg : HasDerivAt (fun y : ℝ => 1 + y) 1 a := by
    simpa using ((hasDerivAt_id a).const_add (1 : ℝ))
  have hlog : HasDerivAt (fun y : ℝ => Real.log (1 + y)) ((1 : ℝ) / (1 + a)) a := by
    simpa using harg.log hne
  have hsq := (hasDerivAt_id a).pow 2
  have hB := hsq.div_const (2 : ℝ)
  have hcu := (hasDerivAt_id a).pow 3
  have hC := hcu.div_const (3 : ℝ)
  have hq := (hasDerivAt_id a).pow 4
  have hD := hq.div_const (4 : ℝ)
  have hq5 := (hasDerivAt_id a).pow 5
  have hE := hq5.div_const (5 : ℝ)
  have hq6 := (hasDerivAt_id a).pow 6
  have hF := hq6.div_const (6 : ℝ)
  have hq7 := (hasDerivAt_id a).pow 7
  have hG := hq7.div_const (7 : ℝ)
  have hp1 := (hasDerivAt_id a).sub hB
  have hp2 := hp1.add hC
  have hp3 := hp2.sub hD
  have hp4 := hp3.add hE
  have hp5 := hp4.sub hF
  have hp6 := hp5.add hG
  have htot := hp6.sub hlog
  unfold Up7Fun
  convert htot using 1
  <;> first | rfl | (funext y; rfl) | (field_simp [hne]; simp; ring)

private lemma Up7Fun_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ Up7Fun x := by
  have hcont : ContinuousOn Up7Fun (Set.Icc (0 : ℝ) x) := by
    intro y hy
    exact (Up7Fun_hasDerivAt y hy.1).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ Up7Fun (interior (Set.Icc (0 : ℝ) x)) := by
    intro y hy
    have hyi : y ∈ Set.Ioo (0 : ℝ) x := by simpa [interior_Icc] using hy
    exact (Up7Fun_hasDerivAt y (le_of_lt hyi.1)).differentiableAt.differentiableWithinAt
  have hnonneg : ∀ y ∈ interior (Set.Icc (0 : ℝ) x), 0 ≤ deriv Up7Fun y := by
    intro y hy
    have hyi : y ∈ Set.Ioo (0 : ℝ) x := by simpa [interior_Icc] using hy
    have hy0 : 0 ≤ y := le_of_lt hyi.1
    rw [(Up7Fun_hasDerivAt y hy0).deriv]
    have h1 : 0 < 1 + y := by linarith
    exact div_nonneg (pow_nonneg hy0 7) (le_of_lt h1)
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) x) hcont hdiff hnonneg
  have hmem0 : (0 : ℝ) ∈ Set.Icc 0 x := by exact ⟨le_rfl, hx⟩
  have hmemX : x ∈ Set.Icc 0 x := by exact ⟨hx, le_rfl⟩
  have hle := hmono hmem0 hmemX hx
  have hU0 : Up7Fun 0 = 0 := by simp [Up7Fun]
  linarith

theorem log_one_add_le7 (w : ℝ) (hw : 0 ≤ w) :
    Real.log (1 + w) ≤ w - w ^ 2 / 2 + w ^ 3 / 3 - w ^ 4 / 4 + w ^ 5 / 5 - w ^ 6 / 6 + w ^ 7 / 7 := by
  have hU := Up7Fun_nonneg w hw
  unfold Up7Fun at hU
  linarith

end Commons.Analysis.SpecialFunctions.Log
