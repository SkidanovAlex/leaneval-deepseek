import Mathlib
import Submission.Work.Mostow.localIsomDefs
import Submission.Work.Mostow.gHLowerBound
import Submission.Work.Mostow.tangentEqLiftTan
import Submission.Work.Mostow.minkLiftTan

/-!
# Tangency versus the chart metric

For a vector `W` of the ambient Minkowski space `ℝ^{Fin n ⊕ 1}` which is tangent to the hyperboloid
at the point `hlift p` (that is, `mink_localIsomDefs W (hlift p) = 0`), the Minkowski square `mink_localIsomDefs W W` is the
hyperbolic length-square `gH p (spatial W)` of its chart part `spatial W`, and it vanishes only for
`W = 0`.  Equivalently: the tangent space at a point of the hyperboloid is spacelike, and the chart
metric `gH` is the restriction of the Minkowski form to it.  This is the elementary dictionary used
by the `localIsom` area.

The proof assembles three independent facts:

* `Work.Mostow.tangentEqLiftTan`: a tangent vector at `hlift p` is the lift `liftTan p (spatial W)`
  of its chart part;
* `Work.Mostow.minkLiftTan`: the Minkowski square of a lifted chart vector `v` is `gH p v`;
* `Work.Mostow.gHLowerBound`: `gH u` is positive definite (indeed `gH u v ≥ ‖v‖ ^ 2 / (1 + ‖u‖ ^ 2)`).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-- The tangent lift of the zero chart vector is the zero ambient vector. -/
lemma liftTan_zero {n : ℕ} (p : E n) : liftTan p (0 : E n) = 0 := by
  funext x
  rcases x with i | j
  · rfl
  · fin_cases j; simp [liftTan]

theorem minkTangent {n : ℕ} (p : E n) (W : Fin n ⊕ Fin 1 → ℝ) (h : mink_localIsomDefs W (hlift p) = 0) :
    mink_localIsomDefs W W = gH p (spatial W) ∧ (mink_localIsomDefs W W = 0 ↔ W = 0) := by
  have hW : W = liftTan p (spatial W) := tangentEqLiftTan p W h
  have h1 : mink_localIsomDefs W W = gH p (spatial W) :=
    (congrArg (fun x => mink_localIsomDefs x x) hW).trans (minkLiftTan p (spatial W))
  refine ⟨h1, ?_, ?_⟩
  · intro h0
    have hg : gH p (spatial W) = 0 := by rw [← h1]; exact h0
    have hv : spatial W = 0 := (gHLowerBound p (spatial W)).2.mp hg
    rw [hW, hv, liftTan_zero]
  · intro h0
    rw [h0]
    simp [mink_localIsomDefs]

end Work.Mostow
