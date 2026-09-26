import Mathlib
import Submission.Work.Smooth.BoxGeneric.Defs

/-!
# `SardCoord` from two-dimensional Sard for the coordinate pull-backs

The input `Work.Smooth.BoxGeneric.SardCoord` of the chapter (a.e. level of a coordinate function on
the surface is a regular value) is exactly Sard's theorem for the `C^∞` functions
`p ↦ (ψ (torusMap p.1 p.2)) i` on the parameter plane: `u` is not a regular value exactly when
`u` is a critical value, i.e. lies in the image of the critical set.

This file

* records that the pull-backs of the coordinate functions are `2π`-periodic in both variables
  (`pullback_coord_periodic_left`, `pullback_coord_periodic_right`), so that a Sard theorem for
  periodic functions applies, and
* reduces `SardCoord ψ` to the nullity of the critical-value sets of those three functions
  (`sardCoord_of_criticalValues_null`).

The missing ingredient is therefore a *two-dimensional* Sard theorem (for `C²` functions
`ℝ² → ℝ`, the sharp smoothness), which Mathlib does not contain; the sibling chapter
`Submission/Work/Smooth/Morse` carries the same kind of input in the form
`Work.Smooth.Morse.LocallyFiniteCriticalValues`/`AERegularValues`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.BoxGeneric.Sard

noncomputable section

/-- The pull-back of a coordinate function is `2π`-periodic in the first parameter. -/
theorem pullback_coord_periodic_left (ψ : Submission.Diffeo) (i : Fin 3) (p : ℝ × ℝ) :
    Work.Smooth.Morse.pullback ψ (fun y : R3 => y i) (p.1 + 2 * Real.pi, p.2) =
      Work.Smooth.Morse.pullback ψ (fun y : R3 => y i) p := by
  simp only [Work.Smooth.Morse.pullback, Work.Smooth.Morse.param,
    Work.Core.torusMap_add_two_pi_left]

/-- The pull-back of a coordinate function is `2π`-periodic in the second parameter. -/
theorem pullback_coord_periodic_right (ψ : Submission.Diffeo) (i : Fin 3) (p : ℝ × ℝ) :
    Work.Smooth.Morse.pullback ψ (fun y : R3 => y i) (p.1, p.2 + 2 * Real.pi) =
      Work.Smooth.Morse.pullback ψ (fun y : R3 => y i) p := by
  simp only [Work.Smooth.Morse.pullback, Work.Smooth.Morse.param,
    Work.Core.torusMap_add_two_pi_right]

/-- The pull-back of a coordinate function is `C^∞` on the parameter plane. -/
theorem pullback_coord_contDiff (ψ : Submission.Diffeo) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Smooth.Morse.pullback ψ (fun y : R3 => y i)) :=
  Work.Smooth.Morse.pullback_contDiff ψ (by fun_prop)

/-- **`SardCoord` from two-dimensional Sard.**  If the critical values of the three coordinate
pull-backs are null, then almost every level of every coordinate function on the surface is a
regular value. -/
theorem sardCoord_of_criticalValues_null (ψ : Submission.Diffeo)
    (h : ∀ i : Fin 3, MeasureTheory.volume {u : ℝ | ∃ p : ℝ × ℝ,
      Work.Smooth.Morse.pullback ψ (fun y : R3 => y i) p = u ∧
        fderiv ℝ (Work.Smooth.Morse.pullback ψ (fun y : R3 => y i)) p = 0} = 0) :
    SardCoord ψ := by
  intro i
  rw [MeasureTheory.ae_iff]
  have hset : {u : ℝ | ¬ Work.Smooth.Morse.IsRegularValue ψ (fun y : R3 => y i) u} =
      {u : ℝ | ∃ p : ℝ × ℝ, Work.Smooth.Morse.pullback ψ (fun y : R3 => y i) p = u ∧
        fderiv ℝ (Work.Smooth.Morse.pullback ψ (fun y : R3 => y i)) p = 0} := by
    ext u
    simp only [Work.Smooth.Morse.IsRegularValue, Work.Smooth.Morse.mem_criticalValues,
      Work.Smooth.Morse.criticalParam, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro hu
      obtain ⟨p, hd, hp⟩ := Classical.not_not.mp hu
      exact ⟨p, hp, hd⟩
    · rintro ⟨p, hp, hd⟩ hu
      exact hu ⟨p, hd, hp⟩
  rw [hset]
  exact h i

end

end Work.Smooth.BoxGeneric.Sard
