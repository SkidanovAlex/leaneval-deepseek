import Mathlib
import Submission.Lib.Unif2.Work.Modulus.Defs
import Submission.Lib.Unif2.Work.Modulus.chartPoleBound
import Submission.Lib.Unif2.Work.Modulus.simpleZeroOfGrowth
import Submission.Lib.Unif2.Work.Modulus.Hypothesis

/-!
# The Green function's zero at its pole is simple

Let `E` be a unit-pole Green function at `z₀` on a Riemann surface `X`
(`Work.UnitGreen.IsUnitGreenFunctionAt`): `E` is positive and harmonic off `z₀`, has a logarithmic pole of
coefficient one at `z₀`, and decays at the ideal boundary.  Let `Φ` be holomorphic on `X`, non
vanishing off `z₀`, with modulus `exp (-E)` there.  This module proves that `Φ` has a *simple*
zero at `z₀`, i.e. `Submission.HasLogPoleAt z₀ Φ`.

The argument is purely local.  In the preferred chart `c = chartAt ℂ z₀` at the pole, with
`a = c z₀`, the pole condition on `E` says that `|E (c.symm w) + log ‖w - a‖| ≤ C` for `w` near
`a`, so the modulus of `g := Φ ∘ c.symm` satisfies the two-sided linear bound

`exp (-C) * ‖w - a‖ ≤ ‖g w‖ ≤ exp (C) * ‖w - a‖`

on a punctured neighbourhood of `a` (`Work.Modulus.chartPoleBound` for the pole bound, and the
elementary `Work.Modulus.exp_bounds_of_abs_add_log` for the passage to the modulus).  A holomorphic
function with such a two-sided *linear* growth bound has a zero of order exactly one, which is
`Work.Modulus.simpleZeroOfGrowth`; its witness `F` is the local factor `g w / (w - a)`, extended to
`a` by its limit (Riemann's removable singularity theorem).

Note how little of `hE` is used: only the logarithmic bound on `E` near the pole, together with the
modulus relation.  Neither harmonicity of `E` nor the decay at infinity plays a role.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Filter Set
open scoped Topology

noncomputable section

namespace Work.Modulus

/-- **Elementary real bound.**  If `r > 0` and `|E + log r| ≤ C`, then
`exp (-E) ≤ exp C * r` and `exp (-C) * r ≤ exp (-E)`: the modulus `exp (-E)` of the holomorphic
modulus is bounded above and below by constant multiples of `r = ‖w - a‖`. -/
theorem exp_bounds_of_abs_add_log {E C r : ℝ} (hr : 0 < r) (h : |E + Real.log r| ≤ C) :
    Real.exp (-E) ≤ Real.exp C * r ∧ Real.exp (-C) * r ≤ Real.exp (-E) := by
  have h1 : -C ≤ E + Real.log r := (abs_le.mp h).1
  have h2 : E + Real.log r ≤ C := (abs_le.mp h).2
  constructor
  · have hle : -E ≤ C + Real.log r := by linarith
    calc Real.exp (-E) ≤ Real.exp (C + Real.log r) := Real.exp_le_exp.mpr hle
      _ = Real.exp C * r := by rw [Real.exp_add, Real.exp_log hr]
  · have hle : Real.log r - C ≤ -E := by linarith
    calc Real.exp (-C) * r = r * Real.exp (-C) := by ring
      _ = Real.exp (Real.log r) * Real.exp (-C) := by rw [Real.exp_log hr]
      _ = Real.exp (Real.log r - C) := by rw [sub_eq_add_neg, Real.exp_add]
      _ ≤ Real.exp (-E) := Real.exp_le_exp.mpr hle

theorem poleOrderModulus_of_unitGreen
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {z₀ : X} {E : X → ℝ} (hE : Work.UnitGreen.IsUnitGreenFunctionAt z₀ E)
    {Φ : X → ℂ} (hhol : Submission.HolomorphicOnX Φ Set.univ)
    (hne : ∀ x, x ≠ z₀ → Φ x ≠ 0)
    (hmod : ∀ x, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x))) :
    Submission.HasLogPoleAt z₀ Φ := by
  -- the pole bound on `E`, read in the chart at `z₀`
  obtain ⟨ε, hε, _hballtgt, C, hC⟩ := chartPoleBound hE
  set c := chartAt ℂ z₀ with hc
  set a : ℂ := c z₀ with ha
  -- `Φ`, read in the chart at the pole, is analytic there
  have hg : AnalyticAt ℂ (Φ ∘ c.symm) a := hhol z₀ (mem_univ z₀)
  -- the two-sided linear growth bound of `g = Φ ∘ c.symm` at `a`
  have hup : ∀ w ∈ Metric.ball a ε, w ≠ a → ‖(Φ ∘ c.symm) w‖ ≤ Real.exp C * ‖w - a‖ := by
    intro w hw hwne
    obtain ⟨hxne, hbnd⟩ := hC w hw hwne
    have hr : 0 < ‖w - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwne)
    have h := (exp_bounds_of_abs_add_log hr hbnd).1
    simpa [hmod (c.symm w) hxne] using h
  have hlo : ∀ w ∈ Metric.ball a ε, w ≠ a → Real.exp (-C) * ‖w - a‖ ≤ ‖(Φ ∘ c.symm) w‖ := by
    intro w hw hwne
    obtain ⟨hxne, hbnd⟩ := hC w hw hwne
    have hr : 0 < ‖w - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwne)
    have h := (exp_bounds_of_abs_add_log hr hbnd).2
    simpa [hmod (c.symm w) hxne] using h
  obtain ⟨F, hFana, hFne, hFeq⟩ :=
    simpleZeroOfGrowth hε (Real.exp_pos (-C)) hg hup hlo
  refine ⟨F, ?_, ?_, ?_⟩
  · rwa [← ha]
  · rwa [← ha]
  · rw [← ha]
    exact hFeq

/-- **Legacy form** of `poleOrderModulus_of_unitGreen` for the (unsatisfiable) predicate
`Work.UnitGreen.IsUnitGreenFunctionAt`, kept so that callers of the earlier interface still compile. -/
theorem poleOrderModulus
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {z₀ : X} {E : X → ℝ} (hE : Submission.HasGreenFunctionE z₀ E)
    {Φ : X → ℂ} (hhol : Submission.HolomorphicOnX Φ Set.univ)
    (hne : ∀ x, x ≠ z₀ → Φ x ≠ 0)
    (hmod : ∀ x, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x))) :
    Submission.HasLogPoleAt z₀ Φ :=
  poleOrderModulus_of_unitGreen (isUnitGreenFunctionAt_of_hasGreenFunctionE hE) hhol hne hmod

end Work.Modulus
