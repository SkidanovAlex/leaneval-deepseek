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

/-! Taylor-style upper bound for `Real.log (1 - x)` by the polynomial
`-(x + x^2/2 + x^3/3 + x^4/4 + x^5/5 + x^6/6)`, valid for `x ≤ 1/2`.

The error function `G(x) = -(x + x^2/2 + ... + x^6/6) - log (1 - x)` has
derivative `x^6 / (1 - x) ≥ 0` and vanishes at `x = 0`; monotonicity on
`[0, x]` gives the inequality. -/

private def Down6Fun (x : ℝ) : ℝ :=
  (-1 : ℝ) * (x + x ^ 2 / 2 + x ^ 3 / 3 + x ^ 4 / 4 + x ^ 5 / 5 + x ^ 6 / 6) -
    Real.log (1 - x)

private lemma Down6Fun_hasDerivAt (a : ℝ) (ha : a < 1) :
    HasDerivAt Down6Fun (a ^ 6 / (1 - a)) a := by
  have hne : (1 : ℝ) - a ≠ 0 := by linarith
  have harg : HasDerivAt (fun x : ℝ => 1 - x) (-1) a := by
    exact (hasDerivAt_id a).const_sub (1 : ℝ)
  have hlog : HasDerivAt (fun x : ℝ => Real.log (1 - x)) ((-1) / (1 - a)) a := by
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
  have hS1 := (hasDerivAt_id a).add hB
  have hS2 := hS1.add hC
  have hS3 := hS2.add hD
  have hS4 := hS3.add hE
  have hS := hS4.add hF
  have hnegS := hS.const_mul (-1 : ℝ)
  have htot := hnegS.sub hlog
  unfold Down6Fun
  convert htot using 1
  <;> first | rfl | (funext y; rfl) | (field_simp [hne]; simp; ring)

private lemma Down6Fun_nonneg (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ (1 : ℝ) / 2) :
    0 ≤ Down6Fun x := by
  have hxlt1 : x < 1 := by linarith
  have hcont : ContinuousOn Down6Fun (Set.Icc (0 : ℝ) x) := by
    intro y hy
    exact (Down6Fun_hasDerivAt y (by linarith [hy.2, hxlt1])).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ Down6Fun (interior (Set.Icc (0 : ℝ) x)) := by
    intro y hy
    have hyi : y ∈ Set.Ioo (0 : ℝ) x := by simpa [interior_Icc] using hy
    exact
      (Down6Fun_hasDerivAt y (by linarith [hyi.2, hxlt1])).differentiableAt.differentiableWithinAt
  have hnonneg : ∀ y ∈ interior (Set.Icc (0 : ℝ) x), 0 ≤ deriv Down6Fun y := by
    intro y hy
    have hyi : y ∈ Set.Ioo (0 : ℝ) x := by simpa [interior_Icc] using hy
    have hy1 : y < 1 := by linarith [hyi.2, hxlt1]
    rw [(Down6Fun_hasDerivAt y hy1).deriv]
    have hden : 0 < 1 - y := by linarith
    exact div_nonneg (pow_nonneg (le_of_lt hyi.1) 6) (le_of_lt hden)
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) x) hcont hdiff hnonneg
  have hmem0 : (0 : ℝ) ∈ Set.Icc 0 x := by exact ⟨le_rfl, hx0⟩
  have hmemX : x ∈ Set.Icc 0 x := by exact ⟨hx0, le_rfl⟩
  have hle := hmono hmem0 hmemX hx0
  have hD0 : Down6Fun 0 = 0 := by simp [Down6Fun]
  linarith

theorem log_one_sub_le6 (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ (1 : ℝ) / 2) :
    Real.log (1 - u) ≤ -(u + u ^ 2 / 2 + u ^ 3 / 3 + u ^ 4 / 4 + u ^ 5 / 5 + u ^ 6 / 6) := by
  have hU := Down6Fun_nonneg u hu0 hu1
  unfold Down6Fun at hU
  rw [show (-1 : ℝ) * (u + u ^ 2 / 2 + u ^ 3 / 3 + u ^ 4 / 4 + u ^ 5 / 5 + u ^ 6 / 6) =
      -(u + u ^ 2 / 2 + u ^ 3 / 3 + u ^ 4 / 4 + u ^ 5 / 5 + u ^ 6 / 6) by ring] at hU
  linarith

end Commons.Analysis.SpecialFunctions.Log
