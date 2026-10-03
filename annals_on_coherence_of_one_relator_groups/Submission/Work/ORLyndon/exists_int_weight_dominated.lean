import Mathlib

namespace Work.ORLyndon

/-- Given rational weights `φ` on a finite set `s` that annihilate `e` and strictly dominate
every index `j ≠ i₀` for the pairings with `f j`, one can find *integer* weights `c` doing the
same.  The point is that `φ` can be rescaled by a common denominator: multiplying by a positive
integer preserves both the vanishing `∑ c y · e y = 0` and the strict inequalities (the sums are
linear in the weights), and clearing the denominators makes the rescaled weights integral. -/
theorem exists_int_weight_dominated {α : Type*} [DecidableEq α] {ι : Type*}
    (s : Finset α) (e : α → ℚ) (f : ι → α → ℚ) (i₀ : ι)
    (hsep : ∃ φ : α → ℚ, (∑ y ∈ s, φ y * e y) = 0 ∧
      ∀ j, j ≠ i₀ → (∑ y ∈ s, φ y * f j y) < (∑ y ∈ s, φ y * f i₀ y)) :
    ∃ c : α → ℤ, (∑ y ∈ s, (c y : ℚ) * e y) = 0 ∧
      (∀ j, (∑ y ∈ s, (c y : ℚ) * f j y) ≤ (∑ y ∈ s, (c y : ℚ) * f i₀ y)) ∧
      (∀ j, (∑ y ∈ s, (c y : ℚ) * f j y) = (∑ y ∈ s, (c y : ℚ) * f i₀ y) → j = i₀) := by
  classical
  obtain ⟨φ, hφe, hφf⟩ := hsep
  -- Step 1: a positive common denominator `N` for the values of `φ` on `s`.
  have hden : ∃ N : ℕ, 0 < N ∧ ∀ y ∈ s, ∃ m : ℤ, (N : ℚ) * φ y = m := by
    refine ⟨∏ z ∈ s, (φ z).den, ?_, ?_⟩
    · exact Finset.prod_pos (fun z _ => Rat.den_pos (φ z))
    · intro y hy
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun z => (φ z).den) hy
      refine ⟨(k : ℤ) * (φ y).num, ?_⟩
      have hnum : φ y * ((φ y).den : ℚ) = ((φ y).num : ℚ) := by
        nth_rewrite 1 [← Rat.num_div_den (φ y)]
        rw [div_mul_cancel₀]
        exact_mod_cast Rat.den_nz (φ y)
      have hN : ((∏ z ∈ s, (φ z).den : ℕ) : ℚ) = ((φ y).den : ℚ) * (k : ℚ) := by
        rw [hk]; push_cast; ring
      rw [hN]
      push_cast
      linear_combination (k : ℚ) * hnum
  obtain ⟨N, hNpos, hN⟩ := hden
  have hNpos' : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hNpos
  -- Step 2: the integer weight vector `c`, whose value at `y ∈ s` rounds `N * φ y`.
  set c : α → ℤ := fun y => if hy : y ∈ s then Classical.choose (hN y hy) else 0 with hcdef
  have hc : ∀ y ∈ s, ((c y : ℚ)) = (N : ℚ) * φ y := by
    intro y hy
    simp only [hcdef]
    rw [dif_pos hy]
    exact (Classical.choose_spec (hN y hy)).symm
  -- Step 3: scaling by the positive `N` preserves vanishing and strict domination.
  refine ⟨c, ?_, ?_, ?_⟩
  · have hmain : (∑ y ∈ s, (c y : ℚ) * e y) = (N : ℚ) * (∑ y ∈ s, φ y * e y) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro y hy
      rw [hc y hy]; ring
    rw [hmain, hφe, mul_zero]
  · intro j
    have hje : (∑ y ∈ s, (c y : ℚ) * f j y) = (N : ℚ) * (∑ y ∈ s, φ y * f j y) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro y hy
      rw [hc y hy]; ring
    have hie : (∑ y ∈ s, (c y : ℚ) * f i₀ y) = (N : ℚ) * (∑ y ∈ s, φ y * f i₀ y) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro y hy
      rw [hc y hy]; ring
    rw [hje, hie]
    by_cases hj : j = i₀
    · subst hj; exact le_refl _
    · exact le_of_lt (mul_lt_mul_of_pos_left (hφf j hj) hNpos')
  · intro j hj
    by_contra hne
    have hje : (∑ y ∈ s, (c y : ℚ) * f j y) = (N : ℚ) * (∑ y ∈ s, φ y * f j y) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro y hy
      rw [hc y hy]; ring
    have hie : (∑ y ∈ s, (c y : ℚ) * f i₀ y) = (N : ℚ) * (∑ y ∈ s, φ y * f i₀ y) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro y hy
      rw [hc y hy]; ring
    rw [hje, hie] at hj
    have hlt : (N : ℚ) * (∑ y ∈ s, φ y * f j y) < (N : ℚ) * (∑ y ∈ s, φ y * f i₀ y) :=
      mul_lt_mul_of_pos_left (hφf j hne) hNpos'
    exact absurd hj (ne_of_lt hlt)

end Work.ORLyndon
