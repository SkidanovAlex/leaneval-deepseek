import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.AppVII

/-- Splitting the double sum `∑ᵢ ∑ⱼ (f i - f j)^2` into the block on the support
`S = {f ≠ 0}` and the block on the complement `Z = {f = 0}`: the cross terms with a
vanishing coordinate contribute exactly the missing pieces, giving the claimed bound. -/
theorem double_sum_sq_ge {p : ℕ} (f : Fin p → ℤ) (hf : ∀ i, 0 ≤ f i) :
    2 * ((Finset.univ.filter (fun i => f i = 0)).card : ℤ) *
        (∑ i ∈ Finset.univ.filter (fun i => f i ≠ 0), (f i) ^ 2)
      ≤ ∑ i : Fin p, ∑ j : Fin p, (f i - f j) ^ 2 := by
  classical
  set S : Finset (Fin p) := Finset.univ.filter (fun i => f i ≠ 0) with hSdef
  set Z : Finset (Fin p) := Finset.univ.filter (fun i => f i = 0) with hZdef
  have hSmem : ∀ i, i ∈ S ↔ f i ≠ 0 := by intro i; simp [hSdef]
  have hZmem : ∀ i, i ∈ Z ↔ f i = 0 := by intro i; simp [hZdef]
  have hdisj : Disjoint S Z := by
    rw [Finset.disjoint_left]
    intro i hiS hiZ
    exact (hSmem i).mp hiS ((hZmem i).mp hiZ)
  have hunion : S ∪ Z = Finset.univ := by
    ext i
    rw [Finset.mem_union, hSmem, hZmem]
    constructor
    · intro _; exact Finset.mem_univ i
    · intro _
      by_cases h : f i = 0
      · exact Or.inr h
      · exact Or.inl h
  have hpart : (∑ i : Fin p, ∑ j : Fin p, (f i - f j)^2)
      = (∑ i ∈ S, ∑ j : Fin p, (f i - f j)^2) + (∑ i ∈ Z, ∑ j : Fin p, (f i - f j)^2) := by
    rw [← hunion, Finset.sum_union hdisj]
  have hSle : (∑ i ∈ S, ∑ j ∈ Z, (f i - f j)^2) ≤ (∑ i ∈ S, ∑ j : Fin p, (f i - f j)^2) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Z)
    intro j hj hjZ
    exact sq_nonneg _
  have hZle : (∑ i ∈ Z, ∑ j ∈ S, (f i - f j)^2) ≤ (∑ i ∈ Z, ∑ j : Fin p, (f i - f j)^2) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    intro j hj hjS
    exact sq_nonneg _
  have hB : (∑ i ∈ S, ∑ j ∈ Z, (f i - f j)^2)
      = (Z.card : ℤ) * (∑ i ∈ S, (f i)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hinner : ∀ j ∈ Z, (f i - f j)^2 = (f i)^2 := by
      intro j hj; rw [(hZmem j).mp hj, sub_zero]
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul]
  have hA : (∑ i ∈ Z, ∑ j ∈ S, (f i - f j)^2)
      = (Z.card : ℤ) * (∑ j ∈ S, (f j)^2) := by
    have hinner2 : ∀ i ∈ Z, (∑ j ∈ S, (f i - f j)^2) = (∑ j ∈ S, (f j)^2) := by
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [(hZmem i).mp hi, zero_sub, neg_sq]
    rw [Finset.sum_congr rfl hinner2, Finset.sum_const, nsmul_eq_mul]
  have key : (Z.card : ℤ) * (∑ i ∈ S, (f i)^2) + (Z.card : ℤ) * (∑ i ∈ S, (f i)^2)
      ≤ ∑ i : Fin p, ∑ j : Fin p, (f i - f j)^2 := by
    calc (Z.card : ℤ) * (∑ i ∈ S, (f i)^2) + (Z.card : ℤ) * (∑ i ∈ S, (f i)^2)
        = (∑ i ∈ S, ∑ j ∈ Z, (f i - f j)^2) + (∑ i ∈ Z, ∑ j ∈ S, (f i - f j)^2) := by
          rw [hB, hA]
      _ ≤ (∑ i ∈ S, ∑ j : Fin p, (f i - f j)^2) + (∑ i ∈ Z, ∑ j : Fin p, (f i - f j)^2) :=
          add_le_add hSle hZle
      _ = ∑ i : Fin p, ∑ j : Fin p, (f i - f j)^2 := hpart.symm
  calc 2 * (Z.card : ℤ) * (∑ i ∈ S, (f i)^2)
      = (Z.card : ℤ) * (∑ i ∈ S, (f i)^2) + (Z.card : ℤ) * (∑ i ∈ S, (f i)^2) := by ring
    _ ≤ ∑ i : Fin p, ∑ j : Fin p, (f i - f j)^2 := key

end Work.Hering.AppVII
