import Mathlib
import Submission.Work.LinnikAreas.Density4.BzS3.sigma_half_sqrt_defs
import Submission.Work.LinnikAreas.Density4.BzS3.aTerm_sum_le
import Submission.Commons.Analysis.Abel.summation_by_parts

namespace Work.LinnikAreas.Density4.BzS3

open Finset

/-- **`Σ_{r ≤ V} r^{-1/2}·σ_{-1/2}(r)·(1 + log(2V/r)) = O(√V)`.**

The unweighted partial sums `A(m) = Σ_{r ≤ m} aTerm r` are `O(√m)`
(`aTerm_sum_le`); Abel's summation identity (`Commons.Analysis.Abel.summation_by_parts`)
turns the weighted sum into the boundary term plus the correction
`Σ_{m < V} (log(2V/m) − log(2V/(m+1)))·A(m)`.  Since the weight has increments
`log(1 + 1/m) ≤ 1/m`, and `Σ_{m ≤ M} 1/√m ≤ 2√M`, both pieces are `O(√V)`. -/
theorem sigma_half_sqrt_sum : ∃ C : ℝ, 0 < C ∧ ∀ V : ℕ, 1 ≤ V →
    (∑ r ∈ Finset.Icc 1 V, (1 / Real.sqrt (r : ℝ))
        * (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ))
        * (1 + Real.log (2 * (V : ℝ) / (r : ℝ)))) ≤ C * Real.sqrt (V : ℝ) := by
  refine ⟨64, by norm_num, ?_⟩
  intro V hV
  have hVpos : (0:ℝ) < (V:ℝ) := by exact_mod_cast (by omega : 0 < V)
  have haTerm_nonneg : ∀ r, 0 ≤ aTerm r := by
    intro r
    rw [aTerm]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun d _ => by positivity))
  -- Identify the target with the `aTerm`-weighted sum.
  have hgeom : (∑ r ∈ Finset.Icc 1 V, (1 / Real.sqrt (r : ℝ))
        * (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ))
        * (1 + Real.log (2 * (V : ℝ) / (r : ℝ))))
      = ∑ m ∈ Finset.Icc 1 V,
          (1 + Real.log (2 * (V:ℝ) / (m:ℝ))) * aTerm m := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [aTerm]; ring
  rw [hgeom]
  -- Abel summation.
  rw [_root_.Commons.Analysis.Abel.summation_by_parts
        (fun m => 1 + Real.log (2 * (V:ℝ) / (m:ℝ))) aTerm V]
  -- Boundary term `(1 + log 2)·A(V)`.
  have hW_V : 1 + Real.log (2 * (V:ℝ)/(V:ℝ)) ≤ 2 := by
    have h2 : 2 * (V:ℝ)/(V:ℝ) = 2 := by
      rw [mul_div_assoc, div_self hVpos.ne', mul_one]
    rw [h2]
    have hlog2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
      linarith
    linarith
  have hA_V : ∑ m ∈ Finset.Icc 1 V, aTerm m ≤ 16 * Real.sqrt (V:ℝ) := aTerm_sum_le V hV
  have hA_V_nonneg : 0 ≤ ∑ m ∈ Finset.Icc 1 V, aTerm m :=
    Finset.sum_nonneg (fun m _ => haTerm_nonneg m)
  have hterm1 : (1 + Real.log (2 * (V:ℝ)/(V:ℝ))) * (∑ m ∈ Finset.Icc 1 V, aTerm m)
      ≤ 32 * Real.sqrt (V:ℝ) := by
    have h := mul_le_mul hW_V hA_V hA_V_nonneg (by norm_num : (0:ℝ) ≤ 2)
    linarith [h]
  -- Correction sum.
  have hterm2 : ∑ m ∈ Finset.Icc 1 (V-1),
        ((1 + Real.log (2 * (V:ℝ)/(m:ℝ))) - (1 + Real.log (2 * (V:ℝ)/((m+1:ℕ):ℝ))))
        * (∑ k ∈ Finset.Icc 1 m, aTerm k) ≤ 32 * Real.sqrt (V:ℝ) := by
    have step1 : ∑ m ∈ Finset.Icc 1 (V-1),
        ((1 + Real.log (2 * (V:ℝ)/(m:ℝ))) - (1 + Real.log (2 * (V:ℝ)/((m+1:ℕ):ℝ))))
        * (∑ k ∈ Finset.Icc 1 m, aTerm k)
        ≤ ∑ m ∈ Finset.Icc 1 (V-1), (1/(m:ℝ)) * (16 * Real.sqrt (m:ℝ)) := by
      apply Finset.sum_le_sum
      intro m hm
      obtain ⟨hm1, _⟩ := Finset.mem_Icc.mp hm
      have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
      have h2Vm : (0:ℝ) < 2*(V:ℝ)/(m:ℝ) := by positivity
      have h2Vmp1 : (0:ℝ) < 2*(V:ℝ)/((m+1:ℕ):ℝ) := by positivity
      have hquot : (2*(V:ℝ)/(m:ℝ))/(2*(V:ℝ)/((m+1:ℕ):ℝ)) = ((m+1:ℕ):ℝ)/(m:ℝ) := by
        field_simp
      have hdiff : (1 + Real.log (2*(V:ℝ)/(m:ℝ)))
            - (1 + Real.log (2*(V:ℝ)/((m+1:ℕ):ℝ))) ≤ 1/(m:ℝ) := by
        have hlogeq : (1 + Real.log (2*(V:ℝ)/(m:ℝ)))
              - (1 + Real.log (2*(V:ℝ)/((m+1:ℕ):ℝ)))
            = Real.log (((m+1:ℕ):ℝ)/(m:ℝ)) := by
          have h1 : (1 + Real.log (2*(V:ℝ)/(m:ℝ)))
                - (1 + Real.log (2*(V:ℝ)/((m+1:ℕ):ℝ)))
              = Real.log (2*(V:ℝ)/(m:ℝ)) - Real.log (2*(V:ℝ)/((m+1:ℕ):ℝ)) := by ring
          rw [h1, ← Real.log_div h2Vm.ne' h2Vmp1.ne', hquot]
        rw [hlogeq]
        have hsplit : (((m+1:ℕ):ℝ))/(m:ℝ) = 1 + 1/(m:ℝ) := by
          rw [Nat.cast_add, Nat.cast_one, add_div, div_self hmpos.ne']
        calc Real.log (((m+1:ℕ):ℝ)/(m:ℝ))
            ≤ (((m+1:ℕ):ℝ)/(m:ℝ)) - 1 := Real.log_le_sub_one_of_pos (by positivity)
          _ = 1/(m:ℝ) := by rw [hsplit]; ring
      have hAd : (∑ k ∈ Finset.Icc 1 m, aTerm k) ≤ 16 * Real.sqrt (m:ℝ) := aTerm_sum_le m hm1
      have hsm : 0 ≤ ∑ k ∈ Finset.Icc 1 m, aTerm k :=
        Finset.sum_nonneg (fun k _ => haTerm_nonneg k)
      exact mul_le_mul hdiff hAd hsm (by positivity)
    refine le_trans step1 ?_
    have step2 : ∑ m ∈ Finset.Icc 1 (V-1), (1/(m:ℝ)) * (16 * Real.sqrt (m:ℝ))
        = 16 * ∑ m ∈ Finset.Icc 1 (V-1), Real.sqrt (m:ℝ)/(m:ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm; ring
    rw [step2]
    have hV1 : ((V-1 : ℕ) : ℝ) ≤ (V:ℝ) := by exact_mod_cast Nat.sub_le V 1
    calc 16 * ∑ m ∈ Finset.Icc 1 (V-1), Real.sqrt (m:ℝ)/(m:ℝ)
        ≤ 16 * (2 * Real.sqrt ((V-1 : ℕ):ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact Work.Commons.Analysis.Series.sum_Icc_sqrt_div_self_le (V-1)
      _ ≤ 16 * (2 * Real.sqrt (V:ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          nlinarith [Real.sqrt_le_sqrt hV1, Real.sqrt_nonneg ((V-1:ℕ):ℝ), Real.sqrt_nonneg (V:ℝ)]
      _ = 32 * Real.sqrt (V:ℝ) := by ring
  linarith [hterm1, hterm2]

end Work.LinnikAreas.Density4.BzS3
