import Mathlib

namespace Commons.Probability.FinFunction

/-- Partial sums of the geometric series with ratio `1/2` are bounded by `2`. -/
private lemma geom_inv_two_le_two (n : ℕ) :
    ∑ a ∈ Finset.range n, ((2 : ℝ)⁻¹) ^ a ≤ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ']
    have h : ∑ k ∈ Finset.range n, ((2 : ℝ)⁻¹) ^ (k + 1)
        = (2 : ℝ)⁻¹ * ∑ k ∈ Finset.range n, ((2 : ℝ)⁻¹) ^ k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_succ']
    rw [h]
    have hhalf : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    rw [pow_zero]
    nlinarith [ih, hhalf]

/-- Counting bound: the sum of `2 ^ (∑ i, j i)` over all `j : Fin m → Fin (L+1)` whose
entries sum to at most `L` is at most `4 ^ L * 2 ^ m`.

On the filtered set one has `2 ^ s ≤ 4 ^ L * (2⁻¹) ^ s` because `s ≤ L`, and the resulting
weighted sum factorises over the coordinates: the factor contributed by each coordinate is a
partial sum of the geometric series with ratio `1/2`, which is bounded by `2`. -/
theorem sum_pow_two_le {m L : ℕ} :
    ∑ j ∈ (Finset.univ : Finset (Fin m → Fin (L + 1))).filter
        (fun j => ∑ i, ((j i : ℕ)) ≤ L),
      (2 : ℝ) ^ (∑ i, ((j i : ℕ))) ≤ 4 ^ L * 2 ^ m := by
  set F : Finset (Fin m → Fin (L + 1)) :=
    (Finset.univ : Finset (Fin m → Fin (L + 1))).filter
      (fun j => ∑ i, ((j i : ℕ)) ≤ L) with hF
  have hsub : F ⊆ (Finset.univ : Finset (Fin m → Fin (L + 1))) :=
    fun j _ => Finset.mem_univ j
  have hterm : ∀ j ∈ F, (2 : ℝ) ^ (∑ i, ((j i : ℕ)))
      ≤ 4 ^ L * ∏ i, ((2 : ℝ)⁻¹) ^ ((j i : ℕ)) := by
    intro j hj
    have hjL : ∑ i, ((j i : ℕ)) ≤ L := by
      rw [hF] at hj
      exact (Finset.mem_filter.mp hj).2
    have hprod : ∏ i, ((2 : ℝ)⁻¹) ^ ((j i : ℕ))
        = ((2 : ℝ)⁻¹) ^ (∑ i, ((j i : ℕ))) := by
      simpa using Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Fin m))
        (fun i => ((j i : ℕ))) ((2 : ℝ)⁻¹)
    have h2pos : (0 : ℝ) < 2 ^ (∑ i, ((j i : ℕ))) := by positivity
    have h4 : (4 : ℝ) ^ (∑ i, ((j i : ℕ))) ≤ 4 ^ L :=
      pow_le_pow_right₀ (by norm_num) hjL
    have hsq : (2 : ℝ) ^ (∑ i, ((j i : ℕ))) * 2 ^ (∑ i, ((j i : ℕ))) ≤ 4 ^ L := by
      have heq : (2 : ℝ) ^ (∑ i, ((j i : ℕ))) * 2 ^ (∑ i, ((j i : ℕ)))
          = 4 ^ (∑ i, ((j i : ℕ))) := by rw [← mul_pow]; norm_num
      rw [heq]; exact h4
    have key : (2 : ℝ) ^ (∑ i, ((j i : ℕ)))
        ≤ 4 ^ L * ((2 : ℝ)⁻¹) ^ (∑ i, ((j i : ℕ))) := by
      have h1 : (2 : ℝ) ^ (∑ i, ((j i : ℕ))) ≤ 4 ^ L / 2 ^ (∑ i, ((j i : ℕ))) :=
        (le_div_iff₀ h2pos).2 hsq
      rw [div_eq_mul_inv] at h1
      rwa [← inv_pow] at h1
    rw [hprod]; exact key
  calc
    ∑ j ∈ F, (2 : ℝ) ^ (∑ i, ((j i : ℕ)))
        ≤ ∑ j ∈ F, 4 ^ L * ∏ i, ((2 : ℝ)⁻¹) ^ ((j i : ℕ)) :=
          Finset.sum_le_sum hterm
    _ = 4 ^ L * ∑ j ∈ F, ∏ i, ((2 : ℝ)⁻¹) ^ ((j i : ℕ)) := by
          rw [Finset.mul_sum]
    _ ≤ 4 ^ L * ∑ j ∈ (Finset.univ : Finset (Fin m → Fin (L + 1))),
            ∏ i, ((2 : ℝ)⁻¹) ^ ((j i : ℕ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro j _ _; positivity
    _ = 4 ^ L * ∏ i : Fin m, ∑ a : Fin (L + 1), ((2 : ℝ)⁻¹) ^ ((a : ℕ)) := by
          congr 1
          exact (Fintype.prod_sum
            (f := fun (i : Fin m) (a : Fin (L + 1)) => ((2 : ℝ)⁻¹) ^ ((a : ℕ)))).symm
    _ ≤ 4 ^ L * 2 ^ m := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hinner : ∀ _i : Fin m,
              (∑ a : Fin (L + 1), ((2 : ℝ)⁻¹) ^ ((a : ℕ))) ≤ 2 := by
            intro i
            rw [Fin.sum_univ_eq_sum_range]
            exact geom_inv_two_le_two (L + 1)
          calc ∏ i : Fin m, (∑ a : Fin (L + 1), ((2 : ℝ)⁻¹) ^ ((a : ℕ)))
              ≤ ∏ _i : Fin m, (2 : ℝ) := by
                apply Finset.prod_le_prod
                · intro i _; positivity
                · intro i _; exact hinner i
            _ = 2 ^ m := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Commons.Probability.FinFunction
