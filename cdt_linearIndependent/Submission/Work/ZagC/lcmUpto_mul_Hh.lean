import Mathlib
import Submission.Work.ZagC.defs

/-!
# `lcm(1,…,m) * H_k ∈ ℤ` for `k ≤ m`

Every `j ∈ {1,…,k}` divides `lcmUpto m = lcm(1,…,m)` because `j ≤ k ≤ m`, hence
`lcmUpto m / j` is a natural number.  Multiplying out `H_k = Σ_{j=1}^k 1/j` therefore
gives the integer `Σ_{j=1}^k lcmUpto m / j`.
-/

namespace Work.ZagC

open Finset
open scoped BigOperators

noncomputable section

theorem lcmUpto_mul_Hh (m k : ℕ) (h : k ≤ m) : ∃ z : ℤ, (Submission.CDTPlan.lcmUpto m : ℚ) * Work.ZagC.Hh k = z := by
  refine ⟨((∑ j ∈ Finset.Icc 1 k, Submission.CDTPlan.lcmUpto m / j : ℕ) : ℤ), ?_⟩
  rw [Work.ZagC.Hh, Finset.mul_sum]
  rw [Int.cast_natCast, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j hj
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hj
  have hjm : j ≤ m := le_trans h2 h
  have hdiv : j ∣ Submission.CDTPlan.lcmUpto m := by
    unfold Submission.CDTPlan.lcmUpto
    exact Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨h1, hjm⟩)
  have hjnz : (j : ℚ) ≠ 0 := by
    have : j ≠ 0 := by omega
    exact_mod_cast this
  rw [Nat.cast_div hdiv hjnz, div_eq_mul_inv]

end

end Work.ZagC
