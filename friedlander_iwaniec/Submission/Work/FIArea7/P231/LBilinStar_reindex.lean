import Mathlib
import Submission.Work.FIArea7.P231Defs
import Submission.Work.FIArea7.P231.ReducedReindex

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea7.P231

open Finset
open scoped BigOperators

noncomputable section

/-- **The reindexing identity of Prop. 23.1.**  The bilinear form `L∗(M,N)` is a sum over the
`c`-smooth decomposition `m = a·m'`, `n = b·n'` of restricted bilinear forms with modulus `a·b·c`
and coefficients supported on the `c`-coprime parts. -/
lemma LBilinStar_reindex {c M N : ℕ} (hc : 1 ≤ c) (psi : GaussianInt → ℂ) (α β : ℕ → ℂ) :
    LBilinStar M N c psi α β
      = ∑ a ∈ (Finset.Icc 1 M).filter (IsSmooth c),
          ∑ b ∈ (Finset.Icc 1 N).filter (IsSmooth c),
            (if Nat.Coprime a b then
              LBilinStar (M / a) (N / b) (a * b * c) psi
                (fun m' => if Nat.Coprime m' c then α (a * m') else 0)
                (fun n' => if Nat.Coprime n' c then β (b * n') else 0)
            else 0) := by
  rw [LBilinStar]
  rw [sum_Icc_Icc_reindex_smooth hc
        (fun m n => (if Nat.Coprime m n then α m * β n * quadEigen psi (c * m * n) else 0))]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  obtain ⟨_, haS⟩ := Finset.mem_filter.mp ha
  obtain ⟨_, hbS⟩ := Finset.mem_filter.mp hb
  by_cases hab : Nat.Coprime a b
  · rw [if_pos hab, LBilinStar]
    refine Finset.sum_congr rfl (fun m' hm' => Finset.sum_congr rfl (fun n' hn' => ?_))
    by_cases h1 : Nat.Coprime m' c
    · by_cases h2 : Nat.Coprime n' c
      · have hiff : Nat.Coprime (a * m') (b * n') ↔ Nat.Coprime m' n' := by
          rw [coprime_mul_iff_of_smooth hc haS hbS h1 h2]
          exact ⟨fun h => h.2, fun h => ⟨hab, h⟩⟩
        have harg : c * (a * m') * (b * n') = a * b * c * m' * n' := by ring
        simp only [hiff, if_pos h1, if_pos h2, harg]
      · simp only [if_neg h2, mul_zero, zero_mul, ite_self]
    · simp only [if_neg h1, mul_zero, zero_mul, ite_self]
  · rw [if_neg hab]
    refine Finset.sum_eq_zero (fun m' hm' => Finset.sum_eq_zero (fun n' hn' => ?_))
    by_cases h1 : Nat.Coprime m' c
    · by_cases h2 : Nat.Coprime n' c
      · have hcop : ¬ Nat.Coprime (a * m') (b * n') := fun h =>
          hab ((coprime_mul_iff_of_smooth hc haS hbS h1 h2).mp h).1
        simp only [if_neg hcop, if_pos h1, if_pos h2]
      · simp only [if_neg h2, mul_zero, zero_mul, ite_self]
    · simp only [if_neg h1, mul_zero, zero_mul, ite_self]

end

end Work.FIArea7.P231
