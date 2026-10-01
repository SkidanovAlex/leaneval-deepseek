import Mathlib
import Submission.Work.LinnikAreas.Density4.sum_Icc_filter_dvd_reindex

namespace Work.LinnikAreas.Density4

/-- The `{0,1}`-valued indicator of a conjunction is the product of the two indicators. -/
private lemma coprime_indicator_and (A B : Prop) [Decidable A] [Decidable B] :
    (if A ∧ B then (1 : ℝ) else 0) = (if A then 1 else 0) * (if B then 1 else 0) := by
  by_cases h1 : A <;> by_cases h2 : B <;> simp_all

/-- Reindexing the multiples of `d²` in `[1,Q]`: the coprime indicator of `d²·k` splits as
`[d ⊥ r]·[k ⊥ r]`, and the count becomes `Σ_{k ≤ Q/d²} [k ⊥ r]`.
Proof route: `sum_Icc_filter_dvd_reindex Q (d^2) (by positivity) φ` with
`φ n := if Nat.Coprime n r then (1:ℝ) else 0`, then rewrite `(d^2 * k).Coprime r` with
`Nat.coprime_mul_iff_left` and `Nat.coprime_pow_left_iff`, and pull the constant `[d ⊥ r]` out of the
sum (`Finset.mul_sum`). -/
theorem sum_sq_dvd_filter_coprime_reindex (Q r d : ℕ) (hr : 1 ≤ r) (hd : 1 ≤ d) :
    (∑ n ∈ (Finset.Icc 1 Q).filter (fun n => d ^ 2 ∣ n),
        (if Nat.Coprime n r then (1 : ℝ) else 0))
      = (if Nat.Coprime d r then 1 else 0) *
          ∑ k ∈ Finset.Icc 1 (Q / d ^ 2), (if Nat.Coprime k r then (1 : ℝ) else 0) := by
  have hd2 : 1 ≤ d ^ 2 := by nlinarith [hd]
  rw [sum_Icc_filter_dvd_reindex Q (d ^ 2) hd2]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hc : (d ^ 2 * k).Coprime r ↔ Nat.Coprime d r ∧ Nat.Coprime k r := by
    rw [Nat.coprime_mul_iff_left, Nat.coprime_pow_left_iff (by norm_num : (0 : ℕ) < 2)]
  rw [if_congr hc rfl rfl]
  exact coprime_indicator_and _ _

end Work.LinnikAreas.Density4
