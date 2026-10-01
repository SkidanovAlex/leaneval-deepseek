import Mathlib
import Submission.Work.LinnikAreas.Density4.DoubleSumDefs

namespace Work.LinnikAreas.Density4

/-- Pointwise identity: for `a ≠ 0` and `b ≠ 0`,
`Q · (dsebG r a · (μ b / b)) = dsebM Q r a b`. -/
private lemma dsebG_mul_eq_dsebM (Q r a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (Q : ℝ) * (dsebG r a * ((ArithmeticFunction.moebius b : ℝ) / (b : ℝ)))
      = dsebM Q r a b := by
  unfold dsebG dsebM
  by_cases hc : Nat.Coprime a r
  · rw [if_pos hc, if_pos hc]
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    field_simp
  · rw [if_neg hc, if_neg hc]
    ring

/-- **Distribution of the main term** (pure algebra, no hypotheses on `Q`, `r`).
With `dsebG r a = [a ⟂ r]·μ(a)/a²`, `Bsum r = ∑_{b ∣ r} μ(b)/b` and
`dsebM Q r a b = [a ⟂ r]·μ(a)μ(b)·(Q/(a²b))` (see `DoubleSumDefs`):

`Q · (∑_{a ≤ Q} dsebG r a) · Bsum r = ∑_{a ≤ Q} ∑_{b ∣ r} dsebM Q r a b`.

Route: `Finset.sum_mul_sum` to distribute the product of the two sums, `Finset.mul_sum` to pull
`Q` inside, then the pointwise identity `Q · (dsebG r a · (μ b / b)) = dsebM Q r a b` for
`b ∈ r.divisors` (so `b ≠ 0`): split on `Nat.Coprime a r` and `close by ring`. -/
theorem main_term_eq_double_sum (Q r : ℕ) :
    (Q : ℝ) * ((∑ a ∈ Finset.Icc 1 Q, dsebG r a) * Bsum r)
      = ∑ a ∈ Finset.Icc 1 Q, ∑ b ∈ r.divisors, dsebM Q r a b := by
  unfold Bsum
  rw [Finset.sum_mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  refine dsebG_mul_eq_dsebM Q r a b ?_ ?_
  · exact fun h => (Finset.mem_Icc.mp ha).1.not_gt (by omega)
  · obtain ⟨hdvd, hr⟩ := Nat.mem_divisors.mp hb
    intro h
    subst h
    exact hr (Nat.zero_dvd.mp hdvd)

end Work.LinnikAreas.Density4
