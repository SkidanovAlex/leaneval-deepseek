import Mathlib
import Submission.Work.Isotopy.exists_localInverse_param
import Submission.Work.Isotopy.partialFderivSection

/-!
# The pointwise local retraction along a smooth family of arcs

Step (ii) of `CutPush/NOTES_R1_R2_plan.md`: at every point `(lam, x)` of the trail box, the
regularity of the arc `Φ lam` at `x` produces — via `Work.Isotopy.exists_localInverse_param` — open
boxes and a local inverse `par` with

  `par s (Φ s y) = y`   whenever `s ∈ O`, `y ∈ U`, `Φ s y ∈ B`,

i.e. exactly the `hretr` shape consumed by `Work.Isotopy.patchedVelocity_of_boxes`
(`Isotopy/velocityFieldPatch.lean`).  The regularity hypothesis of `exists_localInverse_param` is
discharged from `hreg` by `Work.Isotopy.injective_partial_uncurry` — this is where the bridge of
`Isotopy/partialFderivSection.lean` is spent, and no derivative reasoning remains here.

The boxes are triple (`O` in the family parameter, `U` in the source, `B` in the ambient), because
that is the shape in which `exists_localInverse_param` returns its data: the retraction identity is
available for `y ∈ U`, and `Φ s y ∈ B` is the guard under which it is *used* by the velocity patch.
-/

namespace Work.Isotopy

open scoped ContDiff
open Set

set_option linter.unusedVariables false

/-- **A local retraction of a smooth family of arcs, at one point of the trail.** -/
theorem exists_localRetraction_at {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    (Φ : ℝ → ℝ → F) (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry Φ))
    (lam x : ℝ) (hreg : fderiv ℝ (fun t : ℝ => Φ lam t) x 1 ≠ 0) :
    ∃ (O : Set ℝ) (U : Set ℝ) (B : Set F) (par : ℝ → F → ℝ),
      IsOpen O ∧ lam ∈ O ∧ IsOpen U ∧ x ∈ U ∧ IsOpen B ∧ Φ lam x ∈ B ∧
      (∀ s ∈ O, ∀ y ∈ U, Φ s y ∈ B → par s (Φ s y) = y) := by
  obtain ⟨O, U, W, h, h1, h2, h3, h4, h5, h6, _h7, _h8, _h9, h10⟩ :=
    exists_localInverse_param (Function.uncurry Φ) Set.univ isOpen_univ lam x (mem_univ _)
      hΦ.contDiffOn Set.univ isOpen_univ (mem_univ _)
      (injective_partial_uncurry Φ hΦ lam x hreg)
  exact ⟨O, U, W, h, h1, h2, h3, h4, h5, h6,
    fun s hs y hy _ => h10 s hs y hy⟩

end Work.Isotopy
