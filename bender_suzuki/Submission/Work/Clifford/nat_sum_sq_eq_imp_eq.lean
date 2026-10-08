import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Clifford

open Finset

theorem nat_sum_sq_eq_imp_eq {ι : Type*} [Fintype ι] (f : ι → ℕ)
    (h : (∑ i, f i) ^ 2 = ∑ i, (f i) ^ 2) :
    ∀ i j, f i ≠ 0 → f j ≠ 0 → i = j := by
  classical
  -- Expand both squares into products and expand the left product into a double sum.
  simp only [pow_two] at h
  rw [Finset.sum_mul_sum] at h
  -- Split each inner sum into its diagonal term and the off-diagonal part.
  have hsplit : ∀ i, ∑ j, f i * f j = f i * f i + ∑ j ∈ Finset.univ.erase i, f i * f j := by
    intro i
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    abel
  simp_rw [hsplit] at h
  rw [Finset.sum_add_distrib] at h
  -- Hence the sum of all off-diagonal products vanishes.
  have hzero : (∑ i, ∑ j ∈ Finset.univ.erase i, f i * f j) = 0 := by
    omega
  intro i j hi hj
  by_contra hij
  have hinner : ∑ j ∈ Finset.univ.erase i, f i * f j = 0 :=
    Finset.sum_eq_zero_iff.mp hzero i (Finset.mem_univ i)
  have hterm : f i * f j = 0 :=
    Finset.sum_eq_zero_iff.mp hinner j (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)
  rcases Nat.mul_eq_zero.mp hterm with h' | h'
  · exact hi h'
  · exact hj h'

end Work.Clifford
