import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Real.Basic

namespace Commons.Data.Finset

theorem prod_ite_one_mem {κ Ω : Type*} [DecidableEq Ω] (s : Finset κ) (T : κ → Finset Ω) (x : Ω) :
    (∏ i ∈ s, (if x ∈ T i then (1 : ℝ) else 0)) = (if ∀ i ∈ s, x ∈ T i then 1 else 0) := by
  simpa using Finset.prod_boole (s := s) (p := fun i => x ∈ T i) (M₀ := ℝ)

end Commons.Data.Finset