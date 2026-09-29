import Mathlib
import Submission.Work.TMComp.PerfectDefs

namespace Work.TMComp.Perfect

/-- A self-adjoint idempotent `P` on `ℓ²(ℤ)` whose range is contained in the complex line through
a unit vector `u` lying in its range is the orthogonal projection onto that line. -/
theorem proj_apply_unit
    (P : LeanEval.Analysis.TenMartini.EllTwo →L[ℂ] LeanEval.Analysis.TenMartini.EllTwo)
    (hP : P * P = P) (hPstar : star P = P)
    {u : LeanEval.Analysis.TenMartini.EllTwo} (hu : ‖u‖ = 1) (hPu : P u = u)
    (hrange : ∀ w : LeanEval.Analysis.TenMartini.EllTwo, P w = w → ∃ c : ℂ, w = c • u) :
    ∀ x : LeanEval.Analysis.TenMartini.EllTwo, P x = (inner ℂ u x) • u := by
  intro x
  -- `P` fixes every element of its range.
  have hPP : P (P x) = P x := by
    rw [← mul_apply_eq_comp, hP]
  -- hence `P x` lies on the line `ℂ ∙ u`.
  obtain ⟨c, hc⟩ := hrange (P x) hPP
  -- `P` is self-adjoint.
  have hAdj : ContinuousLinearMap.adjoint P = P := by
    rw [← ContinuousLinearMap.star_eq_adjoint, hPstar]
  -- `⟪u, P x⟫ = ⟪u, x⟫`, since `P u = u` and `P* = P`.
  have hstep : inner ℂ u (P x) = inner ℂ u x := by
    rw [← ContinuousLinearMap.adjoint_inner_left P x u, hAdj, hPu]
  have huu : inner ℂ u u = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hu]
    norm_num
  -- evaluating `⟪u, P x⟫ = ⟪u, c • u⟫` gives `c`.
  have hcval : inner ℂ u (P x) = c := by
    rw [hc, inner_smul_right, huu, mul_one]
  have hcx : c = inner ℂ u x := by
    rw [← hcval, hstep]
  rw [hc, hcx]

end Work.TMComp.Perfect
