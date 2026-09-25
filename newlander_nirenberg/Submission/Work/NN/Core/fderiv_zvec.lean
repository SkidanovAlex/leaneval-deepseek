import Mathlib
import Submission.Work.NN.Core.Defs

namespace Work.NN.Core

open LeanEval.Geometry.NewlanderNirenberg
open Submission
open Set
open scoped ContDiff

/-- The tuple `zvec T` of standard coordinates is `y ↦ ecInvL n (T y)`. -/
lemma zvec_eq {n : ℕ} (T : E n ≃L[ℝ] F n) : zvec T = fun y : E n => ecInvL n (T y) := by
  funext y j
  rfl

/-- The differential of the tuple `zvec T = (y ↦ (zcoord T j y)_j)` of standard coordinates is the
constant linear map `tupleDeriv T`. -/
lemma fderiv_zvec {n : ℕ} (T : E n ≃L[ℝ] F n) (y : E n) :
    fderiv ℝ (zvec T) y = tupleDeriv T := by
  rw [zvec_eq T]
  exact fderiv_ecInvL_T T y

end Work.NN.Core
