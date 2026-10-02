import Submission.Work.ConeSwitch.MathlibNoHG

namespace Work.Deep.Kahn

open scoped Classical in
/-- **Weierstrass product inequality / union-bound product estimate.**  For reals `a i ∈ [0,1]`
indexed by a finite set `s`, `1 - ∑ a i ≤ ∏ (1 - a i)`.  This is the estimate that turns a
bound `∑ x j ≤ 1/2` on a sum of LLL potentials into the product bound
`∏ (1 - x j) ≥ 1/2` in the asymmetric Lovász local lemma.

Sketch: induction on `s`.  For `s = insert i s'` with `i ∉ s'`, multiply the induction
hypothesis `1 - ∑_{s'} a ≤ ∏_{s'} (1 - a)` by `1 - a i ≥ 0` and use
`(1 - A) * (1 - a i) = 1 - (A + a i) + A * a i ≥ 1 - (A + a i)`. -/
theorem one_sub_sum_le_prod {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ a i) (h1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s' hi ih =>
    -- specialize the two hypotheses to the smaller set `s'`
    have h0' : ∀ j ∈ s', 0 ≤ a j := fun j hj => h0 j (Finset.mem_insert_of_mem hj)
    have h1' : ∀ j ∈ s', a j ≤ 1 := fun j hj => h1 j (Finset.mem_insert_of_mem hj)
    have hai : 0 ≤ a i := h0 i (by simp)
    have hai1 : a i ≤ 1 := h1 i (by simp)
    -- the partial sum is nonnegative, so the cross term `a i * (∑_{s'} a)` is ≥ 0
    have hA : (0:ℝ) ≤ ∑ j ∈ s', a j := Finset.sum_nonneg fun j hj => h0' j hj
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    -- the two-factor instance of the inequality:
    -- `1 - (a i + A) = (1 - a i) * (1 - A) - a i * A ≤ (1 - a i) * (1 - A)`
    have key : 1 - (a i + ∑ j ∈ s', a j) ≤ (1 - a i) * (1 - ∑ j ∈ s', a j) := by
      have hmul : 0 ≤ a i * ∑ j ∈ s', a j := mul_nonneg hai hA
      have hr : (1 - a i) * (1 - ∑ j ∈ s', a j)
          = 1 - (a i + ∑ j ∈ s', a j) + a i * ∑ j ∈ s', a j := by ring
      rw [hr]
      linarith
    -- scale the induction hypothesis by the nonnegative factor `1 - a i`
    calc 1 - (a i + ∑ j ∈ s', a j)
        ≤ (1 - a i) * (1 - ∑ j ∈ s', a j) := key
      _ ≤ (1 - a i) * ∏ j ∈ s', (1 - a j) :=
          mul_le_mul_of_nonneg_left (ih h0' h1') (sub_nonneg.mpr hai1)

end Work.Deep.Kahn
