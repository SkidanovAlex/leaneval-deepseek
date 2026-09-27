import Mathlib
import Submission.Work.Mostow.localIsomDefs
import Submission.Work.Mostow.segfunHasDerivAt
import Submission.Work.Mostow.segfunSpeed

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-!
# Chain rule along the geodesic segment for a differentiable isometry

This is the two-line computation at the heart of the `localIsom` area: if `F` is `C¹` with
`gH (F u) (fderiv ℝ F u v) = gH u v` (the infinitesimal isometry condition), then the composite
`s ↦ F (segfun p q s)` is differentiable at `t` with derivative the image under `fderiv ℝ F` of the
tangent vector of `segfun`, and that image has hyperbolic length `1` at `F (segfun p q t)`.

The first conjunct is the chain rule (`HasFDerivAt.comp_hasDerivAt`) combined with
`segfunHasDerivAt`; the second conjunct rewrites with the isometry hypothesis `hiso` and then
appeals to unit speed of `segfun` (`segfunSpeed`).
-/

theorem compSegfunDeriv {n : ℕ} (F : E n → E n) (hF : ContDiff ℝ 1 F)
    (hiso : ∀ u v, gH (F u) (fderiv ℝ F u v) = gH u v)
    (p q : E n) (hpq : p ≠ q) (t : ℝ) (ht : t ∈ Set.Icc 0 (hdist p q)) :
    HasDerivAt (fun s => F (segfun p q s))
      (fderiv ℝ F (segfun p q t) ((- Real.cosh (hdist p q - t) / Real.sinh (hdist p q)) • p +
        (Real.cosh t / Real.sinh (hdist p q)) • q)) t ∧
    gH (F (segfun p q t))
      (fderiv ℝ F (segfun p q t) ((- Real.cosh (hdist p q - t) / Real.sinh (hdist p q)) • p +
        (Real.cosh t / Real.sinh (hdist p q)) • q)) = 1 := by
  have hd := segfunHasDerivAt p q hpq t ht
  have hfderiv : HasFDerivAt F (fderiv ℝ F (segfun p q t)) (segfun p q t) :=
    (hF.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  refine ⟨?_, ?_⟩
  · have hchain := hfderiv.comp_hasDerivAt t hd
    simpa [Function.comp_def] using hchain
  · rw [hiso, segfunSpeed p q hpq t ht]

end Work.Mostow
