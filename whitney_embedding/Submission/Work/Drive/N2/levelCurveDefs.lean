import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Projection.Basic
import Submission.Work.Projection.Defs

/-!
# Bad projection directions for a level set covered by curves

This file fixes the vocabulary for the "level set embedding" argument (`n = 2`, compact case).

Given a smooth map `e : M → ℝ^{k+1}` and a family of curves `γ i : ℝ → M`, defined on open sets
`V i ⊆ ℝ`, which covers the level set `f ⁻¹' {b}` and is tangent to it (see
`Work.Drive.N2.exists_finite_levelCover`), the projection `projVec u : ℝ^{k+1} → ℝ^k`
(vocabulary of `Submission/Work/Projection/Basic.lean`, with `ker (projVec u) = ℝ ∙ (u,1)`) is
*injectivity-bad* if it identifies two points of the curve cover, and *immersion-bad* if it kills
the tangent vector of some curve.

Both sets are images of explicit parametrisations (`(s,t) ↦ extract (e (γ i s) - e (γ j t))` from
`V i × V j`, and `t ↦ extract (fderiv ℝ (e ∘ γ i) t 1)` from `V i`), whose domains are open subsets
of `ℝ²` and `ℝ` respectively.  Hence `dimH` of the union is at most `2`; since the projection
argument only needs `dimH bad < k`, this is enough as soon as `k ≥ 3`.

## Main definitions

* `Work.Drive.N2.levelBadInj`
* `Work.Drive.N2.levelBadImm`
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff

variable {M : Type*} [TopologicalSpace M]

/-- **Injectivity-bad projection directions.**  `u` is bad if two points of the curve cover of the
level set have the same image under `projVec u`, i.e. if their difference is a nonzero multiple of
`(u,1)`.  The definition is by the explicit parametrisation: `u` occurs as the `extract` of a
difference `e (γ i s) - e (γ j t)` whose last coordinate is nonzero. -/
noncomputable def levelBadInj {k N : ℕ} (e : M → EuclideanSpace ℝ (Fin (k+1)))
    (γ : Fin N → ℝ → M) (V : Fin N → Set ℝ) : Set (EuclideanSpace ℝ (Fin k)) :=
  {u | ∃ (i j : Fin N) (s t : ℝ), s ∈ V i ∧ t ∈ V j ∧
      (e (γ i s) - e (γ j t)) (Fin.last k) ≠ 0 ∧
      Work.Projection.extract (e (γ i s) - e (γ j t)) = u}

/-- **Immersion-bad projection directions.**  `u` is bad if the projection kills the tangent vector
of one of the curves, i.e. if the derivative of `e ∘ γ i` at some `t ∈ V i` lies in `ℝ ∙ (u,1)`.
Again the definition is by the explicit parametrisation `t ↦ extract (fderiv ℝ (e ∘ γ i) t 1)`. -/
noncomputable def levelBadImm {k N : ℕ} (e : M → EuclideanSpace ℝ (Fin (k+1)))
    (γ : Fin N → ℝ → M) (V : Fin N → Set ℝ) : Set (EuclideanSpace ℝ (Fin k)) :=
  {u | ∃ (i : Fin N) (t : ℝ), t ∈ V i ∧
      (fderiv ℝ (fun s => e (γ i s)) t (1 : ℝ)) (Fin.last k) ≠ 0 ∧
      Work.Projection.extract (fderiv ℝ (fun s => e (γ i s)) t (1 : ℝ)) = u}

end Work.Drive.N2
