import Mathlib
import Submission.Work.Drive.Mono.Band.BandChartDefs
import Submission.Work.Smooth.Morse.Immersion
import Submission.Work.Drive.Final.LTypes
import Submission.Work.Drive.Final.GoodSweepData

/-!
# The transversal-crossing description of the `offK` clause

`offK` (`Work.Drive.Final.GoodSweepData`) asks that no critical point of the swept height in the box
and the closed slab lie on the trace of the knot.  A critical point of the swept height is a point
`z` of the surface at which the level functional annihilates the tangent plane, so if the knot
*passes through* `z` with its velocity tangent to the surface then the level functional is critical
along the knot as well — which the robustness clause (the 4th conjunct of the target) forbids.  So
`offK` can fail only at a point where the knot crosses the surface *transversally*.

This module fixes the vocabulary of that argument:

* `surfPoly` — the polynomial `(‖y‖² + 3)² - 16 (y₀² + y₁²)` whose zero set is the standard torus of
  revolution of the challenge (smooth on all of `ℝ³`, unlike the `√`-form);
* `surfLevelKnot ψ K` — the composite `t ↦ surfPoly (ψ⁻¹ (K.curve t))`, vanishing exactly where the
  knot meets the surface `F = ψ(standard torus)`;
* `offKCrossSet ψ K` — the parameters at which the knot *crosses* `F` (level zero, level function not
  critical): the set whose countability (`Work.Drive.Mono.countable_of_deriv_ne_zero`) reduces the
  bad set of `offK` to a countable union of vertical rays;
* `offKBad ψ K c σ u v a₀ b₀` — the set of pairs `(h,τ)` at which `offK` for the direction
  `nn τ = dirOf τ a₀ b₀` and the half-width `h` may fail.

The two analytic facts (the tangent-plane equation at a non-critical zero of `surfLevelKnot`, and the
countability of `offKCrossSet`) are proved in their own modules.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory Set

noncomputable section

/-- **The polynomial defining the standard torus of revolution of the challenge**:
`(‖y‖² + 3)² - 16 (y₀² + y₁²)`, whose zero set is `{(2 + cos φ)(cos θ, sin θ, ·)}`.  It is smooth on
all of `ℝ³` (unlike `(√(y₀²+y₁²) - 2)² + y₂² - 1`). -/
def surfPoly (y : R3) : ℝ := (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 + 3) ^ 2 - 16 * (y 0 ^ 2 + y 1 ^ 2)

theorem surfPoly_contDiff : ContDiff ℝ (⊤ : ℕ∞) surfPoly := by
  unfold surfPoly
  fun_prop

/-- **The standard torus lies in the zero set of `surfPoly`.** -/
theorem surfPoly_torusMap_eq_zero (u v : ℝ) : surfPoly (Work.Core.torusMap u v) = 0 := by
  rw [surfPoly, Work.Core.torusMap_apply_zero, Work.Core.torusMap_apply_one,
    Work.Core.torusMap_apply_two]
  have h1 : ((2 + Real.cos v) * Real.cos u) ^ 2 + ((2 + Real.cos v) * Real.sin u) ^ 2
      = (2 + Real.cos v) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq u]
  have h2 : (2 + Real.cos v) ^ 2 + Real.sin v ^ 2 + 3 = 4 * (2 + Real.cos v) := by
    nlinarith [Real.sin_sq_add_cos_sq v]
  rw [h1, h2]
  ring

/-- **The carrier of the surface of the challenge lies in the zero set of `surfPoly ∘ ψ⁻¹`.** -/
theorem surfPoly_invFun_eq_zero {ψ : Submission.Diffeo} {y : R3}
    (hy : y ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier) : surfPoly (ψ.invFun y) = 0 := by
  rw [Work.Smooth.Morse.torus_carrier] at hy
  obtain ⟨p, hp⟩ := Set.mem_range.mp hy
  have hpy : ψ.invFun y = Work.Core.torusMap p.1 p.2 := by
    rw [← hp]; exact ψ.left_inv _
  rw [hpy]
  exact surfPoly_torusMap_eq_zero p.1 p.2

/-- **The level function of the surface along the knot**: `t ↦ surfPoly (ψ⁻¹ (K.curve t))`, which
vanishes exactly at the parameters at which the knot lies on the surface. -/
def surfLevelKnot (ψ : Submission.Diffeo) (K : Knot) : ℝ → ℝ :=
  fun t => surfPoly (ψ.invFun (K.curve t))

theorem surfLevelKnot_contDiff (ψ : Submission.Diffeo) (K : Knot) :
    ContDiff ℝ (⊤ : ℕ∞) (surfLevelKnot ψ K) := by
  unfold surfLevelKnot
  exact surfPoly_contDiff.comp (ψ.smooth_invFun.comp K.smooth)

/-- **The set of parameters at which the knot crosses the surface transversally**: the level function
vanishes there but is *critical*.  This is the set on which the `offK` bad set is supported. -/
def offKCrossSet (ψ : Submission.Diffeo) (K : Knot) : Set ℝ :=
  {t | surfLevelKnot ψ K t = 0 ∧ deriv (surfLevelKnot ψ K) t ≠ 0}

/-- **The bad set of the `offK` clause** at the wall normal `v` and the direction basis
`a₀, b₀ ⊥ v`: the pairs `(h,τ)` for which there is a transversal crossing of the knot with the
surface, inside the box and the closed slab, at which the swept height in the direction
`nn τ = dirOf τ a₀ b₀` is critical.  `offK` at `(h, τ)` holds whenever `(h,τ) ∉ offKBad ⋯`. -/
def offKBad (ψ : Submission.Diffeo) (K : Knot) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (v a₀ b₀ : R3) : Set (ℝ × ℝ) :=
  {p | ∃ t ∈ offKCrossSet ψ K,
      K.curve t ∈ Submission.PBox s c σ ∧
      |inner ℝ v (K.curve t) - (inner ℝ v c + u)| ≤ p.1 ∧
      ∃ q : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ q = K.curve t ∧
        fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ
          ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf p.2 a₀ b₀))) q = 0}

end

end Work.Drive.Mono
