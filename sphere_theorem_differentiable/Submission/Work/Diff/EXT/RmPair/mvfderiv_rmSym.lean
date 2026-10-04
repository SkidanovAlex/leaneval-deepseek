import Mathlib
import Submission.Work.Diff.EXT.reactBase
import Submission.Work.Diff.EXT.evX.mvfderiv_rmSymV

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Leibniz rule for the symmetrized reaction `rmSym`

`Work.Diff.EXT.RmPair.mvfderiv_rmSym` is the componentwise product rule for the bilinear form
`rmSym = (rmPair (·) (·) + rmPair (·) (·))/2`:

`d (y ↦ rmSym (A y) (B y))_x v = rmSym (dA) (B x) + rmSym (A x) (dB)`.

Here it is obtained from the equivalent statement `Work.Diff.EXT.evX.mvfderiv_rmSymV`, which is
proved in this workspace by differentiating the bounded bilinear map
`(X, Y) ↦ rmSym X Y` (`IsBoundedBilinearMap.deriv_apply`) and applying the manifold chain rule; the
componentwise form then follows from the identification of the `Curv4 n`-valued derivative with the
array of its component derivatives.  Keeping this module as a thin wrapper preserves the name for
the modules that were written against it.
-/

namespace Work.Diff.EXT.RmPair

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Work.Diff.EXT

/-- The product rule for `rmSym` in its two arguments (componentwise). -/
theorem mvfderiv_rmSym
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (A B : M → Submission.Diff.Alg.Curv4 (Module.finrank ℝ E))
    (x : M) (v : TangentSpace I x)
    (hA : ∀ p q r s, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) (fun y => A y p q r s) x)
    (hB : ∀ p q r s, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) (fun y => B y p q r s) x)
    (i j k l : Fin (Module.finrank ℝ E)) :
    mvfderiv I (fun y => Work.Diff.EXT.rmSym (A y) (B y) i j k l) x v
      = Work.Diff.EXT.rmSym
          (fun p q r s => mvfderiv I (fun y => A y p q r s) x v) (B x) i j k l
        + Work.Diff.EXT.rmSym
          (A x) (fun p q r s => mvfderiv I (fun y => B y p q r s) x v) i j k l :=
  Work.Diff.EXT.evX.mvfderiv_rmSymV (Module.finrank ℝ E) A B x v hA hB i j k l

end Work.Diff.EXT.RmPair
