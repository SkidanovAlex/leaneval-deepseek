import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open scoped BigOperators

theorem sum_norm_bCoeff_le {ι : Type} (s : Finset ι) (γ : ι → ℂ) (nn : ι → ℕ) (N : Finset ℕ)
    (hmem : ∀ i ∈ s, nn i ∈ N) :
    (∑ n ∈ s.image nn, ‖∑ i ∈ s.filter (fun i => nn i = n), γ i * (n : ℂ)⁻¹‖ ^ 2)
      ≤ ∑ n ∈ N, (((s.filter (fun i => nn i = n)).card : ℝ) *
          (∑ i ∈ s.filter (fun i => nn i = n), ‖γ i‖ ^ 2) / (n : ℝ) ^ 2) := by
  -- Pointwise bound on each fibre `n`: Cauchy–Schwarz plus `‖(n:ℂ)⁻¹‖ = 1/n`.
  have key : ∀ n ∈ s.image nn,
      ‖∑ i ∈ s.filter (fun i => nn i = n), γ i * (n : ℂ)⁻¹‖ ^ 2
        ≤ (((s.filter (fun i => nn i = n)).card : ℝ) *
            (∑ i ∈ s.filter (fun i => nn i = n), ‖γ i‖ ^ 2)) / (n : ℝ) ^ 2 := by
    intro n _
    set F := s.filter (fun i => nn i = n) with hF
    have hsum : ∑ i ∈ F, γ i * (n : ℂ)⁻¹ = (∑ i ∈ F, γ i) * (n : ℂ)⁻¹ :=
      (Finset.sum_mul F γ (n : ℂ)⁻¹).symm
    have hna : ‖(n : ℂ)⁻¹‖ ^ 2 = ((n : ℝ) ^ 2)⁻¹ := by
      rw [norm_inv, norm_natCast, inv_pow]
    have hCS : ‖∑ i ∈ F, γ i‖ ^ 2 ≤ (F.card : ℝ) * ∑ i ∈ F, ‖γ i‖ ^ 2 := by
      have h1 : ‖∑ i ∈ F, γ i‖ ≤ ∑ i ∈ F, ‖γ i‖ := norm_sum_le F γ
      have h2 : ‖∑ i ∈ F, γ i‖ ^ 2 ≤ (∑ i ∈ F, ‖γ i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      have h3 : (∑ i ∈ F, ‖γ i‖) ^ 2 ≤ (F.card : ℝ) * ∑ i ∈ F, ‖γ i‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq
      linarith
    calc ‖∑ i ∈ F, γ i * (n : ℂ)⁻¹‖ ^ 2
        = ‖∑ i ∈ F, γ i‖ ^ 2 * ‖(n : ℂ)⁻¹‖ ^ 2 := by rw [hsum, norm_mul, mul_pow]
      _ = ‖∑ i ∈ F, γ i‖ ^ 2 / (n : ℝ) ^ 2 := by rw [hna, div_eq_mul_inv]
      _ ≤ (F.card : ℝ) * (∑ i ∈ F, ‖γ i‖ ^ 2) / (n : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right hCS (by positivity)
  -- `s.image nn ⊆ N` by hypothesis; the extra terms in `N` vanish.
  have hsub : s.image nn ⊆ N := Finset.image_subset_iff.mpr hmem
  have hzero : ∀ n ∈ N, n ∉ s.image nn →
      (((s.filter (fun i => nn i = n)).card : ℝ) *
        (∑ i ∈ s.filter (fun i => nn i = n), ‖γ i‖ ^ 2) / (n : ℝ) ^ 2) = 0 := by
    intro n _ hnimg
    have hempty : s.filter (fun i => nn i = n) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x hx hc
      exact hnimg (Finset.mem_image.mpr ⟨x, hx, hc⟩)
    rw [hempty]
    simp
  calc ∑ n ∈ s.image nn, ‖∑ i ∈ s.filter (fun i => nn i = n), γ i * (n : ℂ)⁻¹‖ ^ 2
      ≤ ∑ n ∈ s.image nn, (((s.filter (fun i => nn i = n)).card : ℝ) *
            (∑ i ∈ s.filter (fun i => nn i = n), ‖γ i‖ ^ 2) / (n : ℝ) ^ 2) :=
          Finset.sum_le_sum key
    _ = ∑ n ∈ N, (((s.filter (fun i => nn i = n)).card : ℝ) *
            (∑ i ∈ s.filter (fun i => nn i = n), ‖γ i‖ ^ 2) / (n : ℝ) ^ 2) :=
          Finset.sum_subset hsub hzero

end Work.BMF.mr_direct
