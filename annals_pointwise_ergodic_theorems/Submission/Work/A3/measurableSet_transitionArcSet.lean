import Mathlib
import Submission.Work.A3.majorArc_split

/-!
# Measurability of the transition arc set (Area A3)

`transitionArcSet Q N γ` is the union, over the reduced fractions `a/q` with `q ≤ N^γ`, of the arcs
of radius `1/(q N^{d/2})` (`d = deg Q`) cut down by the transition threshold
`|θ - a/q| N^d ≤ (N/q)^{d/(d+1)}/100`.  Both conditions on `θ - a/q` are of the form
`|θ - c| ≤ r` with `c`, `r` independent of `θ`, so for fixed `(q, a)` the set is an intersection of
two closed sets; taking the countable union over `(q, a) ∈ ℕ × ℤ` gives measurability.
-/

set_option autoImplicit false

namespace Work.A3

open MeasureTheory Polynomial
open scoped BigOperators

noncomputable section

/-- The "coherent + transition" part of the major arcs is a countable union of closed sets, hence
measurable. -/
lemma measurableSet_transitionArcSet (Q : Polynomial ℤ) (N : ℕ) (γ : ℝ) :
    MeasurableSet (Work.A3.transitionArcSet Q N γ) := by
  unfold transitionArcSet
  rw [Set.ofPred_exists]
  refine MeasurableSet.iUnion fun q => ?_
  rw [Set.ofPred_exists]
  refine MeasurableSet.iUnion fun a => ?_
  by_cases h : 1 ≤ q ∧ IsCoprime a (q : ℤ) ∧ (q : ℝ) ≤ (N : ℝ) ^ γ
  · have hcont : Continuous fun θ : ℝ => |θ - (a : ℝ) / (q : ℝ)| :=
      (continuous_id.sub continuous_const).abs
    have hset : Set.ofPred (fun θ : ℝ => 1 ≤ q ∧ IsCoprime a (q : ℤ) ∧ (q : ℝ) ≤ (N : ℝ) ^ γ ∧
        |θ - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) * (N : ℝ) ^ ((Q.natDegree : ℝ) / 2)) ∧
        |θ - (a : ℝ) / (q : ℝ)| * (N : ℝ) ^ Q.natDegree ≤
          ((N : ℝ) / (q : ℝ)) ^ ((Q.natDegree : ℝ) / (Q.natDegree + 1)) / 100) =
        {θ : ℝ | |θ - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) * (N : ℝ) ^ ((Q.natDegree : ℝ) / 2))} ∩
        {θ : ℝ | |θ - (a : ℝ) / (q : ℝ)| * (N : ℝ) ^ Q.natDegree ≤
          ((N : ℝ) / (q : ℝ)) ^ ((Q.natDegree : ℝ) / (Q.natDegree + 1)) / 100} := by
      ext θ
      constructor
      · intro hm
        exact ⟨hm.2.2.2.1, hm.2.2.2.2⟩
      · intro hm
        exact ⟨h.1, h.2.1, h.2.2, hm.1, hm.2⟩
    rw [hset]
    exact MeasurableSet.inter
      (measurableSet_le hcont.measurable measurable_const)
      (measurableSet_le (hcont.mul_const _).measurable measurable_const)
  · convert MeasurableSet.empty using 1
    ext θ
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    exact fun h1 h2 h3 _ _ => h ⟨h1, h2, h3⟩

end

end Work.A3
