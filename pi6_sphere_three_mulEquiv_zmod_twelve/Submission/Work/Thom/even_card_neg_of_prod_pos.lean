import Mathlib

namespace Work.Thom

/-- If a finite family of nonzero reals has positive product, then an even number
of its entries are negative. -/
theorem even_card_neg_of_prod_pos {n : ℕ} (D : Fin n → ℝ) (hD : ∀ i, D i ≠ 0)
    (h : 0 < ∏ i, D i) : Even ((Finset.univ.filter fun i => D i < 0).card) := by
  classical
  set S : Finset (Fin n) := Finset.univ.filter (fun i => D i < 0) with hS
  set T : Finset (Fin n) := Finset.univ.filter (fun i => ¬ D i < 0) with hT
  -- Split the product over `univ` into the negative and nonnegative parts.
  have h1 : ∏ i, D i = (∏ i ∈ S, D i) * (∏ i ∈ T, D i) := by
    have := Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (Fin n))
      (fun i => D i < 0) (fun i => D i)
    rw [hS, hT]
    exact this.symm
  have h2 : ∏ i, |D i| = (∏ i ∈ S, |D i|) * (∏ i ∈ T, |D i|) := by
    have := Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (Fin n))
      (fun i => D i < 0) (fun i => |D i|)
    rw [hS, hT]
    exact this.symm
  -- On `S` each entry equals `-|D i|`, so the product carries a factor `(-1)^|S|`.
  have h3 : ∏ i ∈ S, D i = (-1 : ℝ) ^ S.card * ∏ i ∈ S, |D i| := by
    have hcongr : ∏ i ∈ S, D i = ∏ i ∈ S, -|D i| := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [hS] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [abs_of_neg hi, neg_neg]
    rw [hcongr, Finset.prod_neg]
  -- On `T` each entry is already nonnegative, hence equal to its absolute value.
  have h4 : ∏ i ∈ T, D i = ∏ i ∈ T, |D i| := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [hT] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [abs_of_nonneg (not_lt.mp hi)]
  -- Hence `∏ D i = (-1)^|S| * ∏ |D i|`.
  have key : ∏ i, D i = (-1 : ℝ) ^ S.card * ∏ i, |D i| := by
    rw [h1, h3, h4, h2, mul_assoc]
  have hP : 0 < ∏ i, |D i| := Finset.prod_pos (fun i _ => abs_pos.mpr (hD i))
  have hsign : 0 < (-1 : ℝ) ^ S.card := by
    have hp : 0 < (-1 : ℝ) ^ S.card * ∏ i, |D i| := key ▸ h
    rcases mul_pos_iff.mp hp with ⟨h1', _⟩ | ⟨h1', h2'⟩
    · exact h1'
    · exact absurd hP (not_lt.mpr (le_of_lt h2'))
  have hone : (-1 : ℝ) ^ S.card = 1 := by
    rcases neg_one_pow_eq_or ℝ S.card with h1' | h1'
    · exact h1'
    · rw [h1'] at hsign; norm_num at hsign
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)).mp hone

end Work.Thom
