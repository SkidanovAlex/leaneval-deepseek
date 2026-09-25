import Mathlib

namespace Work.LT

/-- **Weierstrass product inequality.** If every `a x` with `x ∈ s` lies in `[0,1]`,
then `∏_{x∈s} (1 - a x) ≥ 1 - ∑_{x∈s} a x`. -/
lemma one_sub_sum_le_prod {α : Type*} (s : Finset α) (a : α → ℝ)
    (h0 : ∀ x ∈ s, 0 ≤ a x) (h1 : ∀ x ∈ s, a x ≤ 1) :
    1 - ∑ x ∈ s, a x ≤ ∏ x ∈ s, (1 - a x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.prod_insert hx]
    have h0x : 0 ≤ a x := h0 x (Finset.mem_insert_self x s)
    have h1x : a x ≤ 1 := h1 x (Finset.mem_insert_self x s)
    have h0s : ∀ y ∈ s, 0 ≤ a y := fun y hy => h0 y (Finset.mem_insert_of_mem hy)
    have h1s : ∀ y ∈ s, a y ≤ 1 := fun y hy => h1 y (Finset.mem_insert_of_mem hy)
    have ih' := ih h0s h1s
    have hS : 0 ≤ ∑ y ∈ s, a y := Finset.sum_nonneg h0s
    have h1' : 1 - a x - ∑ y ∈ s, a y ≤ (1 - a x) * (1 - ∑ y ∈ s, a y) := by
      nlinarith [mul_nonneg h0x hS]
    have h2' : (1 - a x) * (1 - ∑ y ∈ s, a y) ≤ (1 - a x) * ∏ y ∈ s, (1 - a y) :=
      mul_le_mul_of_nonneg_left ih' (by linarith)
    calc 1 - (a x + ∑ y ∈ s, a y) = 1 - a x - ∑ y ∈ s, a y := by ring
      _ ≤ (1 - a x) * (1 - ∑ y ∈ s, a y) := h1'
      _ ≤ (1 - a x) * ∏ y ∈ s, (1 - a y) := h2'

/-- The geometric tail bound `∑_{j<m} 2^{-(j+3)} ≤ 1/4`. -/
lemma geom_three_sum_le (m : ℕ) : ∑ j ∈ Finset.range m, (1/2:ℝ)^(j+3) ≤ 1/4 := by
  have h : ∑ j ∈ Finset.range m, (1/2:ℝ)^(j+3) = (1/8) * ∑ j ∈ Finset.range m, (1/2:ℝ)^j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [pow_add]
    ring
  rw [h]
  nlinarith [sum_geometric_two_le m]

/-- Reindexing the `Fin k` product into a range product. -/
lemma fin_prod_eq_range_prod (k : ℕ) :
    ∏ i : Fin k, (1 - (1/2:ℝ)^(k - (i:ℕ))) = ∏ j ∈ Finset.range k, (1 - (1/2:ℝ)^(j+1)) := by
  have h1 : ∏ i : Fin k, (1 - (1/2:ℝ)^(k - (i:ℕ))) =
      ∏ j ∈ Finset.range k, (1 - (1/2:ℝ)^(k - j)) := by
    rw [Finset.prod_fin_eq_prod_range]
    apply Finset.prod_congr rfl
    intro j hj
    rw [dite_eq_left (Finset.mem_range.mp hj)]
  rw [h1]
  rw [← Finset.prod_range_reflect (fun j => 1 - (1/2:ℝ)^(j+1)) k]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  congr 1
  congr 1
  omega

/-- The key numerical estimate: every partial product `∏_{j=1}^{k} (1 - 2^{-j})` is `≥ 1/4`. -/
lemma prod_range_one_half_ge (k : ℕ) :
    (1/4:ℝ) ≤ ∏ j ∈ Finset.range k, (1 - (1/2:ℝ)^(j+1)) := by
  match k with
  | 0 => rw [Finset.prod_range_zero]; norm_num
  | 1 => rw [Finset.prod_range_one]; norm_num
  | (m+2) =>
    have htail : (3/4:ℝ) ≤ ∏ j ∈ Finset.range m, (1 - (1/2:ℝ)^(j+3)) := by
      have hw := one_sub_sum_le_prod (Finset.range m) (fun j => (1/2:ℝ)^(j+3))
        (fun j _ => by positivity) (fun j _ => pow_le_one₀ (by norm_num) (by norm_num))
      have hsum : ∑ j ∈ Finset.range m, (1/2:ℝ)^(j+3) ≤ 1/4 := geom_three_sum_le m
      linarith
    have hsplit : ∏ j ∈ Finset.range (m+2), (1 - (1/2:ℝ)^(j+1))
        = (∏ j ∈ Finset.range 2, (1 - (1/2:ℝ)^(j+1))) *
          ∏ j ∈ Finset.range m, (1 - (1/2:ℝ)^(j+3)) := by
      rw [show m+2 = 2+m by omega, Finset.prod_range_add]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      rw [show (2:ℕ) + j + 1 = j + 3 by omega]
    rw [hsplit]
    have h2 : ∏ j ∈ Finset.range 2, (1 - (1/2:ℝ)^(j+1)) = 3/8 := by
      norm_num [Finset.prod_range_succ, Finset.prod_range_one]
    rw [h2]
    nlinarith [htail]

theorem gb_sharp_numprod (k : ℕ) :
    (1 / 4 : ℝ) ≤ ∏ i : Fin k, (1 - (1 / 2 : ℝ) ^ (k - (i : ℕ))) := by
  rw [fin_prod_eq_range_prod]
  exact prod_range_one_half_ge k

end Work.LT
