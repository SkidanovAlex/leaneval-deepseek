import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Choose.Sum

namespace Commons.Analysis.Walsh

theorem sum_powerset_neg_one_pow_complex {ι : Type*} [DecidableEq ι] (A : Finset ι) :
    (∑ t ∈ A.powerset, (-1 : ℂ) ^ t.card) = if A = ∅ then 1 else 0 := by
  have h := congrArg (fun z : ℤ => (z : ℂ))
    (Finset.sum_powerset_neg_one_pow_card (x := A))
  push_cast at h
  simpa using h

end Commons.Analysis.Walsh