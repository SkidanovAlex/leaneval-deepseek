import Mathlib

namespace Work.NN.Core.Fleet

/-- Explicit uniform bound on the partial products `∏_{j<J} b_j^{1/m_j}` when `b_j ≤ B L^j`
and `m_j ≥ c p^j` with `p > 1`: the product is at most
`(max 1 B)^{1/(c(1-1/p))} * (max 1 L)^{p/(c(p-1)^2)}`, uniformly in `J`. -/
theorem prodBoundQuant {p c B L : ℝ} (hp : 1 < p) (hc : 0 < c) (hB : 0 < B) (hL : 0 < L)
    {m : ℕ → ℕ} (hm : ∀ j, c * p ^ j ≤ (m j : ℝ)) (hmpos : ∀ j, 1 ≤ m j)
    {b : ℕ → ℝ} (hb : ∀ j, 0 ≤ b j) (hbd : ∀ j, b j ≤ B * L ^ j) :
    ∀ J : ℕ, (∏ j ∈ Finset.range J, b j ^ (1 / (m j : ℝ)))
      ≤ (max 1 B) ^ (1 / (c * (1 - 1 / p))) * (max 1 L) ^ (p / (c * (p - 1) ^ 2)) := by
  intro J
  have hp0 : (0:ℝ) < p := lt_trans zero_lt_one hp
  have hxpos : (0:ℝ) < 1/p := one_div_pos.mpr hp0
  have hxlt : 1/p < 1 := by rw [div_lt_one hp0]; exact hp
  have hr : ‖(1/p : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hxpos]; exact hxlt
  have hmj_pos : ∀ j, (0:ℝ) < (m j : ℝ) := by
    intro j
    have : (1:ℝ) ≤ (m j : ℝ) := by exact_mod_cast hmpos j
    linarith
  have hmaxB : 1 ≤ max 1 B := le_max_left _ _
  have hmaxL : 1 ≤ max 1 L := le_max_left _ _
  have hBle : B ≤ max 1 B := le_max_right _ _
  have hLle : L ≤ max 1 L := le_max_right _ _
  -- each factor is bounded by a product of a `B`-power and an `L`-power
  have hterm : ∀ j, b j ^ (1 / (m j : ℝ))
      ≤ B ^ (1 / (m j : ℝ)) * L ^ ((j:ℝ) * (1 / (m j : ℝ))) := by
    intro j
    have hz : 0 ≤ 1/(m j : ℝ) := le_of_lt (one_div_pos.mpr (hmj_pos j))
    have h1 : b j ^ (1/(m j:ℝ)) ≤ (B * L^j) ^ (1/(m j:ℝ)) :=
      Real.rpow_le_rpow (hb j) (hbd j) hz
    have h2 : (B * L^j) ^ (1/(m j:ℝ)) = B ^ (1/(m j:ℝ)) * (L^j : ℝ) ^ (1/(m j:ℝ)) :=
      Real.mul_rpow hB.le (pow_nonneg hL.le j)
    have h3 : (L^j : ℝ) ^ (1/(m j:ℝ)) = L ^ ((j:ℝ) * (1/(m j:ℝ))) := by
      rw [← Real.rpow_natCast L j, ← Real.rpow_mul hL.le]
    rw [h2, h3] at h1
    exact h1
  -- split the product into the two exponent sums
  have hprod : (∏ j ∈ Finset.range J, b j ^ (1 / (m j : ℝ)))
      ≤ B ^ (∑ j ∈ Finset.range J, 1/(m j:ℝ)) *
        L ^ (∑ j ∈ Finset.range J, (j:ℝ) * (1/(m j:ℝ))) := by
    calc (∏ j ∈ Finset.range J, b j ^ (1/(m j:ℝ)))
        ≤ ∏ j ∈ Finset.range J, B ^ (1/(m j:ℝ)) * L ^ ((j:ℝ)*(1/(m j:ℝ))) :=
          Finset.prod_le_prod₀ (fun j _ => Real.rpow_nonneg (hb j) _) (fun j _ => hterm j)
      _ = (∏ j ∈ Finset.range J, B ^ (1/(m j:ℝ))) *
          (∏ j ∈ Finset.range J, L ^ ((j:ℝ)*(1/(m j:ℝ)))) :=
          Finset.prod_mul_distrib
      _ = B ^ (∑ j ∈ Finset.range J, 1/(m j:ℝ)) *
          L ^ (∑ j ∈ Finset.range J, (j:ℝ)*(1/(m j:ℝ))) := by
          rw [Real.rpow_sum_of_pos hB (fun j => 1/(m j:ℝ)) (Finset.range J),
              Real.rpow_sum_of_pos hL (fun (j:ℕ) => (j:ℝ)*(1/(m j:ℝ))) (Finset.range J)]
  -- bound on the first exponent sum
  have hS1 : (∑ j ∈ Finset.range J, 1/(m j:ℝ)) ≤ 1/(c*(1-1/p)) := by
    have h1 : (∑ j ∈ Finset.range J, 1/(m j:ℝ)) ≤ ∑ j ∈ Finset.range J, 1/(c*p^j) := by
      apply Finset.sum_le_sum
      intro j _
      exact one_div_le_one_div_of_le (mul_pos hc (pow_pos hp0 j)) (hm j)
    have h2 : (∑ j ∈ Finset.range J, 1/(c*p^j)) = (1/c) * ∑ j ∈ Finset.range J, (1/p)^j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [one_div_pow]
      field_simp
    have h3 : (∑ j ∈ Finset.range J, (1/p)^j) ≤ (1-1/p)⁻¹ := by
      have hsum : Summable (fun j : ℕ => (1/p)^j) := summable_geometric_of_norm_lt_one hr
      calc (∑ j ∈ Finset.range J, (1/p)^j) ≤ ∑' j : ℕ, (1/p)^j :=
            Summable.sum_le_tsum (Finset.range J) (fun j _ => pow_nonneg hxpos.le j) hsum
        _ = (1 - 1/p)⁻¹ := tsum_geometric_of_norm_lt_one hr
    have h4 : (1/c) * ((1-1/p)⁻¹) = 1/(c*(1-1/p)) := by field_simp
    calc (∑ j ∈ Finset.range J, 1/(m j:ℝ))
        ≤ ∑ j ∈ Finset.range J, 1/(c*p^j) := h1
      _ = (1/c) * ∑ j ∈ Finset.range J, (1/p)^j := h2
      _ ≤ (1/c) * (1-1/p)⁻¹ := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 1/(c*(1-1/p)) := h4
  -- bound on the second exponent sum
  have hS2 : (∑ j ∈ Finset.range J, (j:ℝ) * (1/(m j:ℝ))) ≤ p/(c*(p-1)^2) := by
    have h1 : (∑ j ∈ Finset.range J, (j:ℝ) * (1/(m j:ℝ)))
        ≤ ∑ j ∈ Finset.range J, (j:ℝ) * (1/(c*p^j)) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (one_div_le_one_div_of_le (mul_pos hc (pow_pos hp0 j)) (hm j)) (Nat.cast_nonneg j)
    have h2 : (∑ j ∈ Finset.range J, (j:ℝ) * (1/(c*p^j)))
        = (1/c) * ∑ j ∈ Finset.range J, (j:ℝ)*(1/p)^j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [one_div_pow]
      field_simp
    have h3 : (∑ j ∈ Finset.range J, (j:ℝ)*(1/p)^j) ≤ (1/p)/(1-1/p)^2 := by
      have hsum : Summable (fun j : ℕ => (j:ℝ)*(1/p)^j) := by
        simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hr
      calc (∑ j ∈ Finset.range J, (j:ℝ)*(1/p)^j) ≤ ∑' j : ℕ, (j:ℝ)*(1/p)^j :=
            Summable.sum_le_tsum (Finset.range J)
              (fun j _ => mul_nonneg (Nat.cast_nonneg j) (pow_nonneg hxpos.le j)) hsum
        _ = (1/p)/(1-1/p)^2 := tsum_coe_mul_geometric_of_norm_lt_one hr
    have h4 : (1/c) * ((1/p)/(1-1/p)^2) = p/(c*(p-1)^2) := by field_simp
    calc (∑ j ∈ Finset.range J, (j:ℝ)*(1/(m j:ℝ)))
        ≤ ∑ j ∈ Finset.range J, (j:ℝ)*(1/(c*p^j)) := h1
      _ = (1/c) * ∑ j ∈ Finset.range J, (j:ℝ)*(1/p)^j := h2
      _ ≤ (1/c) * ((1/p)/(1-1/p)^2) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = p/(c*(p-1)^2) := h4
  have hS1nn : 0 ≤ ∑ j ∈ Finset.range J, 1/(m j:ℝ) :=
    Finset.sum_nonneg (fun j _ => le_of_lt (one_div_pos.mpr (hmj_pos j)))
  have hS2nn : 0 ≤ ∑ j ∈ Finset.range J, (j:ℝ)*(1/(m j:ℝ)) :=
    Finset.sum_nonneg (fun j _ =>
      mul_nonneg (Nat.cast_nonneg j) (le_of_lt (one_div_pos.mpr (hmj_pos j))))
  -- monotonicity of `rpow` in base and exponent
  have hA : B ^ (∑ j ∈ Finset.range J, 1/(m j:ℝ))
      ≤ (max 1 B) ^ (∑ j ∈ Finset.range J, 1/(m j:ℝ)) :=
    Real.rpow_le_rpow hB.le hBle hS1nn
  have hA2 : (max 1 B) ^ (∑ j ∈ Finset.range J, 1/(m j:ℝ)) ≤ (max 1 B) ^ (1/(c*(1-1/p))) :=
    Real.rpow_le_rpow_of_exponent_le hmaxB hS1
  have hC : L ^ (∑ j ∈ Finset.range J, (j:ℝ)*(1/(m j:ℝ)))
      ≤ (max 1 L) ^ (∑ j ∈ Finset.range J, (j:ℝ)*(1/(m j:ℝ))) :=
    Real.rpow_le_rpow hL.le hLle hS2nn
  have hC2 : (max 1 L) ^ (∑ j ∈ Finset.range J, (j:ℝ)*(1/(m j:ℝ)))
      ≤ (max 1 L) ^ (p/(c*(p-1)^2)) :=
    Real.rpow_le_rpow_of_exponent_le hmaxL hS2
  calc (∏ j ∈ Finset.range J, b j ^ (1/(m j:ℝ)))
      ≤ B ^ (∑ j ∈ Finset.range J, 1/(m j:ℝ)) *
        L ^ (∑ j ∈ Finset.range J, (j:ℝ)*(1/(m j:ℝ))) := hprod
    _ ≤ (max 1 B) ^ (1/(c*(1-1/p))) * (max 1 L) ^ (p/(c*(p-1)^2)) :=
        mul_le_mul (le_trans hA hA2) (le_trans hC hC2)
          (Real.rpow_nonneg hL.le _)
          (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one hmaxB)) _)

end Work.NN.Core.Fleet
