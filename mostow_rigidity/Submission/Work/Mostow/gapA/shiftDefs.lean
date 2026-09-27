import Mathlib
import Submission.Work.Mostow.gapA.defs
import Submission.Work.Mostow.QIDefs

/-!
# The "shifted" point of the hyperboloid model

Given `w : E n`, a Minkowski vector `N : Fin n ⊕ Fin 1 → ℝ` and a real number `d`, we decompose
`hlift w = (hlift w - N) + N` and scale the first summand by `cosh (d+1)/cosh d` and the second
by `sinh (d+1)/sinh d`.  When `N` is the normal component `gcN a b w` of `w` with respect to the
geodesic joining `a` and `b`, and `d = distGeod a b w`, the resulting vector is the point of `ℍⁿ`
at distance `1` from `w` on the perpendicular through `w`, going away from the geodesic; its
distance to the geodesic is `d + 1`.
-/

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-- The Minkowski vector obtained from `hlift w` by scaling the component along `N` by
`sinh (d+1)/sinh d` and the complementary component by `cosh (d+1)/cosh d`. -/
def shiftVec (w : E n) (N : Fin n ⊕ Fin 1 → ℝ) (d : ℝ) : Fin n ⊕ Fin 1 → ℝ :=
  Real.cosh (d + 1) • ((Real.cosh d)⁻¹ • (hlift w - N))
    + Real.sinh (d + 1) • ((Real.sinh d)⁻¹ • N)

/-- The chart point of `shiftVec w N d`. -/
def shiftPt (w : E n) (N : Fin n ⊕ Fin 1 → ℝ) (d : ℝ) : E n :=
  WithLp.toLp 2 (fun i : Fin n => shiftVec w N d (Sum.inl i))

end

end Work.Mostow.gapA
