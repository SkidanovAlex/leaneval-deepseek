import Mathlib
import Submission.Work.NN.Core.Defs

namespace Work.NN.Core

open LeanEval.Geometry.NewlanderNirenberg
open Submission
open Set
open scoped ContDiff

/-- `tupleDerivInv T` is a two-sided inverse of `tupleDeriv T` (the differential of the tuple of
standard coordinate functions `zvec T`). -/
lemma tupleDeriv_comp {n : ℕ} (T : E n ≃L[ℝ] F n) :
    (tupleDerivInv T).comp (tupleDeriv T) = 1 ∧ (tupleDeriv T).comp (tupleDerivInv T) = 1 := by
  constructor
  · ext x
    simp [tupleDeriv, tupleDerivInv, ContinuousLinearMap.comp_apply]
  · ext z
    simp [tupleDeriv, tupleDerivInv, ContinuousLinearMap.comp_apply]

end Work.NN.Core
