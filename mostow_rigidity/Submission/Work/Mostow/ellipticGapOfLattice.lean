import Mathlib
import Submission.Work.Mostow.ellipticGapAtCusp

/-!
# The elliptic rotation gap of the cusp stabiliser (re-homed name)

The elliptic rotation gap `Work.Mostow.ellipticGapOfLattice` used by
`Work.Mostow.cuspStabCocompactOfLattice` was renamed to `Work.Mostow.ellipticGapAtCusp`
(proved in `Submission/Work/Mostow/ellipticGapAtCusp.lean`).  This module re-exports the theorem
under its old name so that the modules importing it keep working.
-/

namespace Work.Mostow

theorem ellipticGapOfLattice (n : ℕ) (hn : 3 ≤ n)
    (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Work.Mostow.parFixed Γ) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ (γ : Γ) (A : Submission.Mostow.E n →ₗ[ℝ] Submission.Mostow.E n)
      (v : Submission.Mostow.E n),
      (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ≠ 1 →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      (∃ p : Submission.Mostow.E n, (γ : LeanEval.Geometry.MostowRigidity.PO n 1) • p = p) →
      (∀ y : Submission.Mostow.E n, inner ℝ y ξ = 0 → inner ℝ (A y) ξ = 0) →
      (∀ y : Submission.Mostow.E n, inner ℝ y ξ = 0 → ‖A y‖ = ‖y‖) →
      (∀ (y : Submission.Mostow.E n) (D : ℝ), inner ℝ y ξ = 0 → 0 < D →
        Work.Mostow.lev ξ ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • Work.Mostow.hptOf ξ y D) = D ∧
        Work.Mostow.yc ξ ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • Work.Mostow.hptOf ξ y D) = A y + v) →
      ∃ y : Submission.Mostow.E n, inner ℝ y ξ = 0 ∧ ‖y‖ = 1 ∧ θ ≤ ‖A y - y‖ :=
  ellipticGapAtCusp n hn hA hI Γ hΓ ξ hξ

end Work.Mostow
