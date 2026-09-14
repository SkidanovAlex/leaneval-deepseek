import Mathlib
import Submission.Commons.NumberTheory.ZMod.sum_minrep_weight_le

/-!
# The weighted sum over `ZMod M` (unconditional form)

For `M ≥ 1` and `t ≥ 0`,
`∑_{b : ZMod M} min t (M / (2·d(b))) ≤ M · (1 + log M)`,
where `d(b) = min b.val (M - b.val)` is the distance of `b` to `0` in `ZMod M`.

This is the `t`-free version of the weighted estimate: the truncation by `t`
only decreases each term, so the bound is independent of `t`. It is the
intermediate estimate `hg_bound` used in `sum_minrep_weight_le`.
-/

open scoped BigOperators

namespace Commons.NumberTheory.ZMod

theorem sum_minrep_weight_all (M : ℕ) [NeZero M] (t : ℝ) (ht : 0 ≤ t) :
    (∑ b : ZMod M, min t ((M : ℝ) / (2 * ((min b.val (M - b.val) : ℕ) : ℝ))))
      ≤ (M : ℝ) * (1 + Real.log M) := by
  have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)
  have hm : (0:ℝ) ≤ (M:ℝ) := by positivity
  have hg : (∑ b : ZMod M, min t ((M:ℝ)/(2*((min b.val (M-b.val):ℕ):ℝ))))
      ≤ ((M:ℝ)/2) * (∑ b : ZMod M, (1/(b.val:ℝ) + 1/(((-b).val:ℕ):ℝ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b _
    exact sum_minrep_weight_pointwise M t ht b
  have hSS : (∑ b : ZMod M, (1/(b.val:ℝ) + 1/(((-b).val:ℕ):ℝ)))
      = 2 * (∑ b : ZMod M, 1/(b.val:ℝ)) := by
    rw [Finset.sum_add_distrib]
    have hneg : (∑ b : ZMod M, 1/(((-b).val:ℕ):ℝ)) = (∑ b : ZMod M, 1/(b.val:ℝ)) := by
      have h := Equiv.sum_comp (Equiv.neg (ZMod M)) (fun b : ZMod M => (1:ℝ)/(b.val:ℝ))
      simpa using h
    rw [hneg]; ring
  have hS : (∑ b : ZMod M, 1/(b.val:ℝ)) ≤ 1 + Real.log (M:ℝ) := by
    rw [sum_zmod_val_eq_sum_range M (fun j => (1:ℝ)/(j:ℝ))]
    calc ∑ j ∈ Finset.range M, (1:ℝ)/(j:ℝ)
        ≤ ∑ j ∈ Finset.Icc 0 M, (1:ℝ)/(j:ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro j hj; simp only [Finset.mem_range] at hj; simp only [Finset.mem_Icc]; omega
          · intro j hj hnj; positivity
      _ = ∑ j ∈ Finset.Icc 1 M, (1:ℝ)/(j:ℝ) := by
          rw [← Finset.insert_Icc_succ_left_eq_Icc (show 0 ≤ M by omega)]
          rw [Finset.sum_insert (by simp [Finset.mem_Icc])]
          simp
      _ ≤ 1 + Real.log (M:ℝ) := Commons.Analysis.ExpLog.harmonic_le_one_add_log M hM1
  calc (∑ b : ZMod M, min t ((M:ℝ)/(2*((min b.val (M-b.val):ℕ):ℝ))))
      ≤ ((M:ℝ)/2) * (∑ b : ZMod M, (1/(b.val:ℝ) + 1/(((-b).val:ℕ):ℝ))) := hg
    _ = ((M:ℝ)/2) * (2 * (∑ b : ZMod M, 1/(b.val:ℝ))) := by rw [hSS]
    _ = (M:ℝ) * (∑ b : ZMod M, 1/(b.val:ℝ)) := by ring
    _ ≤ (M:ℝ) * (1 + Real.log (M:ℝ)) := mul_le_mul_of_nonneg_left hS hm

end Commons.NumberTheory.ZMod
