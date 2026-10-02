/-
# The base window at `c₀`: `A1` ⟹ the base point's Böttcher argument is in the `α`-window

The design's `G3` produces the *base point* of the connecting path (the leak point of the
equatorial rigidity, at the level `xLeak` of the repelling coordinate) and its property is

> `|ϑ p_e - α| < δ + o(1)`,

i.e. the *Böttcher argument* of the base point is within `δ` of the direction `α`.  At `c₀` this
is exactly `A1` (`Work.GATE.Nest.nest_angle_design`, **proved**): a point of the nest region off
`K c` has its dynamical ray in the window.  The two lemmas below turn that ray statement into the
form in which the transport `Work.GATE.gate_window` consumes it
(`Work.GATE.deviation`, the `α`-relative Böttcher argument of `Gate/Defs.lean`):

* `abs_deviation_lt_of_paramRay_window` — a ray in the window gives a deviation in the window;
* `base_window_disjunction` — `A1` at the `z₁`-nest therefore puts the base point's argument in
  one of the two windows.

Together with `Work.GATE.deviation_iterate` (the transport divides the deviation by `1024^m`),
this is the chain `A1 → base window → window for the parameter`, with `G4` proved.
-/
import Submission.Work.GATE.Defs
import Submission.Work.GATE.Gate.Defs
import Submission.Work.GATE.Gate.Transport
import Submission.Work.GATE.Nest.nest_angle_design
import Submission.Work.GATE.Nest.deviation_eq_of_mem_paramRay

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE.Nest

open LeanEval.ComplexAnalysis (Mandelbar)

/-- **A ray in the window gives a deviation in the window.**  If `z` lies on the dynamical ray of
angle `ϑ` with `α - δ < ϑ ≤ α` and `δ ≤ 1/4`, then the `α`-relative Böttcher argument
(`Work.GATE.deviation`) of `z` is within `δ` of `0`. -/
theorem abs_deviation_lt_of_paramRay_window {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    {z : ℂ} {ϑ α δ : ℝ} (hz : z ∈ Work.EL.paramRay hN ϑ)
    (hδ : δ ≤ 1 / 4) (h₁ : α - δ < ϑ) (h₂ : ϑ ≤ α) :
    |Work.GATE.deviation φ α z| < δ := by
  have hα : |ϑ - α| < 1 / 2 := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  rw [deviation_eq_of_mem_paramRay hN hα hz]
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- **The base window from `A1`, in the `α₁` case.**  A point of the level-`n` nest region of the
`z₁`-nest, off the filled Julia set, whose ray `A1` puts in the `α₁`-part of the window, has its
Böttcher argument within `windowEps` of `α₁`. -/
theorem abs_deviation_lt_alpha1 {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {z : ℂ}
    {ϑ : ℝ} (hz : z ∈ Work.EL.paramRay hN ϑ)
    (h₁ : Work.EL.alpha1 - Work.Final.windowEps < ϑ) (h₂ : ϑ ≤ Work.EL.alpha1) :
    |Work.GATE.deviation φ Work.EL.alpha1 z| < Work.Final.windowEps :=
  abs_deviation_lt_of_paramRay_window hN hz (le_of_lt Work.GATE.windowEps_lt_quarter) h₁ h₂

/-- **The base window from `A1`, in the `α₂` case** (the `ι`-swapped tongue). -/
theorem abs_deviation_lt_alpha2 {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {z : ℂ}
    {ϑ : ℝ} (hz : z ∈ Work.EL.paramRay hN ϑ)
    (h₁ : Work.EL.alpha2 ≤ ϑ) (h₂ : ϑ < Work.EL.alpha2 + Work.Final.windowEps) :
    |Work.GATE.deviation φ Work.EL.alpha2 z| < Work.Final.windowEps := by
  have hα : |ϑ - Work.EL.alpha2| < 1 / 2 := by
    rw [abs_of_nonneg (by linarith)]
    linarith [Work.GATE.windowEps_lt_quarter]
  rw [deviation_eq_of_mem_paramRay hN hα hz]
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- **The base window at `c₀` (the design's `G3` base), as a disjunction of the two cases.**
A point `z` of the level-`n` nest region of the `z₁`-nest (`nest_angle_design`), off `K c`, has
its Böttcher argument within `windowEps` of one of the two root directions: the ray statement of
`A1` converted by the two lemmas above. -/
theorem base_window_disjunction {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {z : ℂ}
    {ϑ : ℝ} (hz : z ∈ Work.EL.paramRay hN ϑ)
    (hwin : (Work.EL.alpha1 - Work.Final.windowEps < ϑ ∧ ϑ ≤ Work.EL.alpha1) ∨
      (Work.EL.alpha2 ≤ ϑ ∧ ϑ < Work.EL.alpha2 + Work.Final.windowEps)) :
    |Work.GATE.deviation φ Work.EL.alpha1 z| < Work.Final.windowEps ∨
      |Work.GATE.deviation φ Work.EL.alpha2 z| < Work.Final.windowEps :=
  hwin.elim (fun h => Or.inl (abs_deviation_lt_alpha1 hN hz h.1 h.2))
    (fun h => Or.inr (abs_deviation_lt_alpha2 hN hz h.1 h.2))

end Work.GATE.Nest
