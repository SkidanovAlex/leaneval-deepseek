import Mathlib
import Submission.Work.Smooth.BoxGeneric.Sard.criticalValues_null_of_contDiffTwo_periodic
import Submission.Work.Smooth.Morse.Defs

/-!
# Almost every level of a `C²` function on the surface is a regular value

This file discharges the Sard-type input `Work.Smooth.Morse.AERegularValues ψ φ` for every `C²`
function `φ : ℝ³ → ℝ`, with no smoothness beyond `C²`.

The statement is exactly Sard's theorem for `φ|_F` in the form in which the Morse/sweep chapter
consumes it: the set of *non-regular* levels of `φ|_F` is

`criticalValues ψ φ = (pullback ψ φ) '' {p | fderiv ℝ (pullback ψ φ) p = 0}`,

the image of the critical set of the pull-back of `φ` to the parameter plane.  The parameter plane
version of the critical-value set is

`{u | ∃ p, pullback ψ φ p = u ∧ fderiv ℝ (pullback ψ φ) p = 0}`,

which is Lebesgue-null by the two-dimensional Sard theorem for periodic `C²` functions of the
sibling chapter (`Work.Smooth.BoxGeneric.Sard.criticalValues_null_of_contDiffTwo_periodic`); the
periodicity in each variable is the `2π`-periodicity of the parametrisation
(`pullback_add_two_pi_left`, `pullback_add_two_pi_right`, proved here for an arbitrary `g`).

Hence the complement of the critical-value set is conull, i.e. almost every level is regular.
-/

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory

namespace Work.Smooth.Morse

noncomputable section

/-- The pull-back `pullback ψ g` is `2π`-periodic in the first (longitude) variable, because the
parametrisation of the standard torus is (`Work.Core.torusMap_add_two_pi_left`). -/
theorem pullback_add_two_pi_left (ψ : Submission.Diffeo) (g : R3 → ℝ) (p : ℝ × ℝ) :
    pullback ψ g (p.1 + 2 * Real.pi, p.2) = pullback ψ g p := by
  simp only [pullback, param, Work.Core.torusMap_add_two_pi_left]

/-- The pull-back `pullback ψ g` is `2π`-periodic in the second (meridian) variable. -/
theorem pullback_add_two_pi_right (ψ : Submission.Diffeo) (g : R3 → ℝ) (p : ℝ × ℝ) :
    pullback ψ g (p.1, p.2 + 2 * Real.pi) = pullback ψ g p := by
  simp only [pullback, param, Work.Core.torusMap_add_two_pi_right]

/-- The pull-back of a `C²` function is `C²`: it is the composition of the `C∞` parametrisation of
the surface with the function. -/
theorem pullback_contDiff_two (ψ : Submission.Diffeo) {g : R3 → ℝ} (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 (pullback ψ g) := by
  have hparam : ContDiff ℝ 2 (param ψ) :=
    (param_contDiff ψ).of_le (WithTop.coe_le_coe.mpr le_top)
  exact ContDiff.comp hg hparam

/-- The set of non-regular levels of `pullback ψ g` is the critical-value set of `pullback ψ g`,
written as an existential over the parameter plane (the form in which the two-dimensional Sard
theorem of `Work.Smooth.BoxGeneric.Sard` is stated). -/
theorem setOf_not_isRegularValue_eq (ψ : Submission.Diffeo) (g : R3 → ℝ) :
    {t : ℝ | ¬ IsRegularValue ψ g t} =
      {u : ℝ | ∃ p : ℝ × ℝ, pullback ψ g p = u ∧ fderiv ℝ (pullback ψ g) p = 0} := by
  ext u
  simp only [IsRegularValue, mem_criticalValues, Set.mem_ofPred_eq]
  constructor
  · intro hu
    obtain ⟨p, hd, hp⟩ := Classical.not_not.mp hu
    exact ⟨p, hp, hd⟩
  · rintro ⟨p, hp, hd⟩ hu
    exact hu ⟨p, hd, hp⟩

/-- **Almost every level of a `C²` function on the surface is a regular value** (Sard's theorem for
`φ|_F`): the critical values of the pull-back of `φ` to the parameter plane are Lebesgue-null
(two-dimensional Sard for periodic `C²` functions), and they are exactly the non-regular levels of
`φ|_F`. -/
theorem aeRegularValues_of_contDiffTwo (ψ : Submission.Diffeo) {φ : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ} (hφ : ContDiff ℝ 2 φ) : Work.Smooth.Morse.AERegularValues ψ φ := by
  have hnull := Work.Smooth.BoxGeneric.Sard.criticalValues_null_of_contDiffTwo_periodic
    (pullback_contDiff_two ψ hφ) (pullback_add_two_pi_left ψ φ) (pullback_add_two_pi_right ψ φ)
  rw [AERegularValues, MeasureTheory.ae_iff, setOf_not_isRegularValue_eq]
  exact hnull

end

end Work.Smooth.Morse
