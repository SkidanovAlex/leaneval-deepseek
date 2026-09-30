import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- `∏(1+a_i) ≤ 1/(1−Σ a_i)` for nonnegative `a_i` with `Σ a_i < 1`. -/
lemma prod_one_add_le_inv_one_sub_sum {ι : Type*} (s : Finset ι) (b : ι → ℝ)
    (hb : ∀ i ∈ s, 0 ≤ b i) (hs : ∑ i ∈ s, b i < 1) :
    ∏ i ∈ s, (1 + b i) ≤ 1 / (1 - ∑ i ∈ s, b i) := by
  classical
  revert hb hs
  refine Finset.induction_on s ?_ ?_
  · intro hb hs
    simp
  · intro a s ha ih hb hs
    rw [Finset.sum_insert ha] at hs
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hbs : ∀ i ∈ s, 0 ≤ b i := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hba : 0 ≤ b a := hb a (Finset.mem_insert_self a s)
    have hss : 0 ≤ ∑ i ∈ s, b i := Finset.sum_nonneg hbs
    have hst : ∑ i ∈ s, b i < 1 := by linarith
    have hD : 0 < 1 - ∑ i ∈ s, b i := by linarith
    have hE : 0 < 1 - (b a + ∑ i ∈ s, b i) := by linarith
    have ih' := ih hbs hst
    have hca : 0 ≤ 1 + b a := by linarith
    calc (1 + b a) * ∏ i ∈ s, (1 + b i)
        ≤ (1 + b a) * (1 / (1 - ∑ i ∈ s, b i)) := mul_le_mul_of_nonneg_left ih' hca
      _ ≤ 1 / (1 - (b a + ∑ i ∈ s, b i)) := by
            rw [mul_one_div, div_le_div_iff₀ hD hE]
            nlinarith [hba, hss, mul_nonneg hba hss, mul_self_nonneg (b a)]

end Work.BW
