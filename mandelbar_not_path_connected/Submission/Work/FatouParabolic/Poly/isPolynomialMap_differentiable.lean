import Mathlib
import Submission.Work.FatouParabolic.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouParabolic.Poly

/-- The evaluation map of a complex polynomial is entire. -/
private lemma differentiable_polynomial_eval (P : Polynomial ℂ) :
    Differentiable ℂ (fun z : ℂ => P.eval z) := by
  have h1 : (fun z : ℂ => P.eval z) = fun z : ℂ => Polynomial.aeval z P := by
    funext z
    rw [Polynomial.aeval_def]
    simp
  rw [h1]
  exact P.differentiable_aeval

/-- A polynomial map of degree at least two is (complex) differentiable. -/
theorem isPolynomialMap_differentiable {F : ℂ → ℂ}
    (h : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F) : Differentiable ℂ F := by
  obtain ⟨P, _hdeg, hF⟩ := h
  rw [show F = fun z : ℂ => P.eval z from funext hF]
  exact differentiable_polynomial_eval P

end Work.FatouParabolic.Poly
