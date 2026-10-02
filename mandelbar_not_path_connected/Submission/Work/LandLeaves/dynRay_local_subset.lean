import Mathlib
import Submission.Work.LandLeaves.TypeGeometry
import Submission.Work.LandLeaves.exists_local_repelling_branch
import Submission.Work.LandLeaves.isDynBottcherHomeo_of_isDynBottcher

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

theorem dynRay_local_subset {c : ℂ} {φ : ℂ → ℂ} (hφ : Work.ParamRays.IsDynBottcher c φ)
    {k : ℕ} {y : ℂ} (hrep : Work.Landing.IsRepelling c k y) :
    ∃ (r r' : ℝ) (g : ℂ → ℂ), 0 < r ∧ r < r' ∧ g y = y ∧
      (∀ w : ℂ, ‖w - y‖ ≤ r' → (LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] (g w) = w) ∧
      (∀ z : ℂ, ‖z - y‖ ≤ r → ‖(LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] z - y‖ ≤ r' →
         g ((LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] z) = z) ∧
      (∀ θ : ℝ, ∀ z ∈ Work.Landing.dynRay c φ θ, ‖z - y‖ ≤ r ∧
         ‖(LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] z - y‖ ≤ r' →
         ∃ w ∈ Work.Landing.dynRay c φ ((Work.Landing.angDouble)^[2 * k] θ),
            ‖w - y‖ ≤ r' ∧ g w = z) := by
  obtain ⟨r, r', κ, g, hr, hrr', hκ0, hκ1, hgy, hcontr, hright, hleft⟩ :=
    exists_local_repelling_branch (c := c) (k := k) (y := y) hrep
  refine ⟨r, r', g, hr, hrr', hgy, hright, hleft, ?_⟩
  intro θ z hz hzr
  refine ⟨(LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] z, ?_, hzr.2, hleft z hzr.1 hzr.2⟩
  rw [← dynRay_iterate_eq hφ θ (2 * k)]
  exact ⟨z, hz, rfl⟩


end Work.LandLeaves
