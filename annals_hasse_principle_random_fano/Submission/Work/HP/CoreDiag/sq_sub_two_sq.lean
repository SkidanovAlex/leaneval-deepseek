import Mathlib

namespace Work.HP.CoreDiag

theorem sq_sub_two_sq {β : Type*} [AddCommGroup β] [DecidableEq β] (Z : Finset β) (c : β → ℝ) (hneg : ∀ x ∈ Z, -x ∈ Z) (hne : ∀ x ∈ Z, x ≠ -x) (hc : ∀ x, c (-x) = c x) : (∑ x ∈ Z, c x) ^ 2 - 2 * ∑ x ∈ Z, (c x) ^ 2 = ∑ p ∈ (Z.product Z).filter (fun p => p.1 ≠ p.2 ∧ p.1 ≠ -p.2), c p.1 * c p.2 := by
  set S := ∑ x ∈ Z, c x with hS
  -- Rewrite the filtered sum over the product as an iterated sum.
  have hRHS : (∑ p ∈ (Z.product Z).filter (fun p => p.1 ≠ p.2 ∧ p.1 ≠ -p.2), c p.1 * c p.2)
      = ∑ x ∈ Z, ∑ y ∈ Z, (if x ≠ y ∧ x ≠ -y then c x * c y else 0) := by
    rw [Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
  -- For `x ∈ Z`, the sum of `c` over the `y` with `y ≠ x` and `y ≠ -x` is `S - 2 * c x`.
  have hfilter : ∀ x ∈ Z, (∑ y ∈ Z.filter (fun y => x ≠ y ∧ x ≠ -y), c y) = S - 2 * c x := by
    intro x hx
    have hnegx : -x ∈ Z := hneg x hx
    have hne' : x ≠ -x := hne x hx
    -- The complement of the good set inside `Z` is exactly `{x, -x}`.
    have hcompl : Z.filter (fun y => ¬ (x ≠ y ∧ x ≠ -y)) = {x, -x} := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hy⟩
        by_cases h : x = y
        · exact Or.inl h.symm
        · right
          have hxny : x = -y := by
            by_contra h2
            exact hy ⟨h, h2⟩
          rw [hxny]; simp
      · rintro (rfl | rfl)
        · exact ⟨hx, by simp⟩
        · exact ⟨hnegx, by simp⟩
    have hsplit := Finset.sum_filter_add_sum_filter_not Z (fun y => x ≠ y ∧ x ≠ -y) c
    rw [hcompl, Finset.sum_pair hne', hc x, ← hS] at hsplit
    have htwo : c x + c x = 2 * c x := by ring
    rw [htwo] at hsplit
    exact eq_sub_iff_add_eq.mpr hsplit
  -- Each inner sum over `y` equals `c x * (S - 2 * c x)`.
  have hinner : ∀ x ∈ Z, (∑ y ∈ Z, (if x ≠ y ∧ x ≠ -y then c x * c y else 0)) = c x * (S - 2 * c x) := by
    intro x hx
    rw [← Finset.sum_filter (p := fun y => x ≠ y ∧ x ≠ -y)]
    rw [← Finset.mul_sum]
    rw [hfilter x hx]
  -- Final algebra: `∑ x, c x * (S - 2 * c x) = S^2 - 2 * ∑ x, (c x)^2`.
  have hsum2 : (∑ x ∈ Z, c x * (S - 2 * c x)) = S ^ 2 - 2 * ∑ x ∈ Z, (c x) ^ 2 := by
    have h1 : ∀ x, c x * (S - 2 * c x) = c x * S - 2 * (c x) ^ 2 := fun x => by ring
    simp_rw [h1]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← hS]
    ring
  rw [hRHS, Finset.sum_congr rfl hinner, hsum2]

end Work.HP.CoreDiag
