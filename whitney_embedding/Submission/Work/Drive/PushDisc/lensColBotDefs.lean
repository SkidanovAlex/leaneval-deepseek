import Mathlib
import Submission.Work.Drive.PushDisc.lensRegularDefs
import Submission.Work.Drive.Whitney.whitneyDiscDefs

/-!
# The lower-collar-bad parameter set of the lens perturbation

`Work.Drive.PushDisc.badColBot f Δ₀ ρ γ₁` is the set of perturbation parameters `v` for which the
vertical derivative `fderiv ℝ (lensMap Δ₀ ρ v) (x, 0) (0, 1)` at the *lower* edge of the lens meets
the tangent space of `f` at the point `γ₁ (sigR x)` of the first arc, for some `x ∈ (-1, 1)`.

This is the definition used by `Work.Drive.PushDisc.dimH_badColBot`
(`Submission/Work/Drive/PushDisc/dimH_badColBot.lean`); it is stated with the explicit type
`(Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))` of the parameter space, which is definitionally
the abbreviation `Work.Drive.PushDisc.Prm n` of `exists_goodLensParam.lean`, so that the two can be
used interchangeably.

NOTE (wiring).  `Work.Drive.PushDisc.badColBot` is also defined in
`Submission/Work/Drive/PushDisc/exists_goodLensParam.lean`, next to the two *temporary stand-ins*
for the collar bounds.  A module may not import both definitions, and the collar bound
`dimH_badColBot` cannot be imported by `exists_goodLensParam.lean` unless the latter stops defining
`badColBot` here.  The intended wiring is therefore: `exists_goodLensParam.lean` imports this module
(and `Submission.Work.Drive.PushDisc.dimH_badColBot`), deletes its own `def badColBot` together with
the `dimH_badColBot` stand-in, and keeps using the definition from here.  Nothing else in this
development depends on `exists_goodLensParam.lean`.
-/

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff ENNReal
open Set Metric MeasureTheory Topology Filter

/-- The "lower-collar-bad" parameters of the lens perturbation. -/
def badColBot {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))) (ρ : ℝ) (γ₁ : ℝ → M) :
    Set ((Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))) :=
  {v | ∃ x ∈ Set.Ioo (-1 : ℝ) 1,
    fderiv ℝ (lensMap Δ₀ ρ v) (x, 0) (0, 1) ∈
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f
        (γ₁ (Work.Drive.Whitney.sigR x))).range}

end Work.Drive.PushDisc
