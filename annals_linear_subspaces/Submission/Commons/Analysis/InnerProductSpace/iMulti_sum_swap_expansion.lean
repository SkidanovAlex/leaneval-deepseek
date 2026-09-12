import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.LinearAlgebra.ExteriorPower.Basic

namespace Commons.Analysis.InnerProductSpace

lemma iMulti_sum_swap_expansion {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (e c : Fin k → E) :
    exteriorPower.ιMulti ℝ k (fun r : Fin k => e r + c r) =
      (Finset.univ : Finset (Finset (Fin k))).sum (fun T : Finset (Fin k) =>
        exteriorPower.ιMulti ℝ k (fun r : Fin k => if r ∈ T then c r else e r)) := by
  classical
  -- The argument `fun r => e r + c r` is the pointwise sum `c + e`.
  have h_arg : (fun r : Fin k => e r + c r) = c + e := by
    funext r
    simp [add_comm]
  -- Expand by multilinearity: a sum in every slot yields the sum over all
  -- choices, i.e. over all subsets `T` of `Fin k` (those slots taking `c`).
  have h := (exteriorPower.ιMulti ℝ k).map_add_univ c e
  rw [h_arg, h]
  congr

end Commons.Analysis.InnerProductSpace