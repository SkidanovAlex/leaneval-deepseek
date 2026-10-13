import Mathlib
import Submission.Work.WilE3.API.Rem.eTayBasic

namespace Work.WilE3.API.Rem

theorem sum_b_smul_eTayGrad {k : ℕ} (y x : Fin k → ℝ) (S : Finset (Fin k → ℕ))
    (b : (Fin k → ℕ) → ℝ) :
    (∑ m ∈ S, b m • Work.WilE3.API.eTayGrad y m x)
      = ∑ i : Fin k, (∑ m ∈ S.filter (fun m => 0 < m i),
            b m * Work.WilE3.API.eTayMon y (Work.WilE3.API.miS m i) x) •
          (ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i) := by
  -- Unfold the gradient of each monomial and push the scalar `b m` inside.
  rw [show (∑ m ∈ S, b m • Work.WilE3.API.eTayGrad y m x)
        = ∑ m ∈ S, ∑ i : Fin k,
            (b m * (if 0 < m i then Work.WilE3.API.eTayMon y (Work.WilE3.API.miS m i) x
              else 0)) •
              (ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i) from
      Finset.sum_congr rfl (fun m _ => by
        simp only [Work.WilE3.API.eTayGrad]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [smul_smul])]
  -- Interchange the two sums and pull the scalar out of the inner one.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_smul]
  congr 1
  -- Restrict to the multi-indices with positive `i`-th coordinate.
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  by_cases h : 0 < m i <;> simp [h]

end Work.WilE3.API.Rem
