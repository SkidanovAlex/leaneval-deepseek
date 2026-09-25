import Mathlib

namespace Work.NN.Core

/-- Uniform bound on the partial products `∏_{j<J} b_j^{1/m_j}`, given that
`b_j ≤ B L^j` and `m_j ≥ c p^j` with `p > 1`. -/
theorem moserProductBound {p c B L : ℝ} (hp : 1 < p) (hc : 0 < c) (hB : 0 < B) (hL : 1 ≤ L)
    {m : ℕ → ℕ} (hm : ∀ j, c * p ^ j ≤ (m j : ℝ)) (hmpos : ∀ j, 1 ≤ m j)
    {b : ℕ → ℝ} (hb : ∀ j, 0 ≤ b j) (hbd : ∀ j, b j ≤ B * L ^ j) :
    ∃ P : ℝ, 0 < P ∧ ∀ J : ℕ, (∏ j ∈ Finset.range J, b j ^ (1 / (m j : ℝ))) ≤ P := by
  have hp0 : (0:ℝ) < p := lt_trans zero_lt_one hp
  have hL0 : (0:ℝ) < L := lt_of_lt_of_le zero_lt_one hL
  have hLlognn : 0 ≤ Real.log L := Real.log_nonneg hL
  set A : ℝ := max (Real.log B) 0 with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; exact le_max_right _ _
  have hlogB : Real.log B ≤ A := by rw [hAdef]; exact le_max_left _ _
  have hcne : c ≠ 0 := ne_of_gt hc
  -- `r = 1/p` lies in `[0,1)`, so `∑ r^j` and `∑ j r^j` converge.
  have hr : ‖(1/p : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1/p)]
    rw [div_lt_one hp0]
    simpa using hp
  have hsum1 : Summable (fun j : ℕ => (A/c) * ((1/p)^j)) :=
    (summable_geometric_of_norm_lt_one hr).mul_left (A/c)
  have hsum2 : Summable (fun j : ℕ => (Real.log L/c) * ((j:ℝ) * (1/p)^j)) := by
    apply Summable.mul_left
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hsum : Summable (fun j : ℕ => (A/c) * ((1/p)^j) + (Real.log L/c) * ((j:ℝ) * (1/p)^j)) :=
    hsum1.add hsum2
  have heq : (fun j : ℕ => (A/c) * ((1/p)^j) + (Real.log L/c) * ((j:ℝ) * (1/p)^j))
      = (fun j : ℕ => (A + (j:ℝ)*Real.log L)/(c*p^j)) := by
    funext j
    rw [one_div, inv_pow]
    field_simp
  have hsumE : Summable (fun j : ℕ => (A + (j:ℝ)*Real.log L)/(c*p^j)) := heq ▸ hsum
  have hE_nonneg : ∀ j : ℕ, 0 ≤ (A + (j:ℝ)*Real.log L)/(c*p^j) := by
    intro j
    apply div_nonneg
    · have : (0:ℝ) ≤ (j:ℝ) * Real.log L := mul_nonneg (Nat.cast_nonneg j) hLlognn
      linarith [hA0]
    · exact le_of_lt (mul_pos hc (pow_pos hp0 j))
  refine ⟨Real.exp (∑' j : ℕ, (A + (j:ℝ)*Real.log L)/(c*p^j)), Real.exp_pos _, fun J => ?_⟩
  -- termwise comparison `b_j^{1/m_j} ≤ exp e_j`
  have hterm : ∀ j, b j ^ (1/(m j:ℝ)) ≤ Real.exp ((A + (j:ℝ)*Real.log L)/(c*p^j)) := by
    intro j
    have hmj_pos : (0:ℝ) < (m j : ℝ) := by
      have : (1:ℝ) ≤ (m j : ℝ) := by exact_mod_cast hmpos j
      linarith
    have hden_pos : (0:ℝ) < c*p^j := mul_pos hc (pow_pos hp0 j)
    have hexp_nonneg : 0 ≤ (1/(m j:ℝ)) := le_of_lt (one_div_pos.mpr hmj_pos)
    have hAj : 0 ≤ A + (j:ℝ)*Real.log L := by
      have : (0:ℝ) ≤ (j:ℝ)*Real.log L := mul_nonneg (Nat.cast_nonneg j) hLlognn
      linarith [hA0]
    have hBL : 0 < B * L^j := mul_pos hB (pow_pos hL0 j)
    have hb_le : b j ^ (1/(m j:ℝ)) ≤ max 1 ((B*L^j)^(1/(m j:ℝ))) := by
      by_cases hbj : (1:ℝ) ≤ b j
      · exact le_trans (Real.rpow_le_rpow (hb j) (hbd j) hexp_nonneg) (le_max_right _ _)
      · exact le_trans (Real.rpow_le_one (hb j) (le_of_lt (not_le.mp hbj)) hexp_nonneg) (le_max_left _ _)
    have hD : (B*L^j)^(1/(m j:ℝ)) ≤ Real.exp ((A + (j:ℝ)*Real.log L)/(c*p^j)) := by
      rw [Real.rpow_def_of_pos hBL]
      apply Real.exp_le_exp.mpr
      rw [Real.log_mul (ne_of_gt hB) (ne_of_gt (pow_pos hL0 j)), Real.log_pow]
      have step1 : (Real.log B + (j:ℝ)*Real.log L) * (1/(m j:ℝ))
          ≤ (A + (j:ℝ)*Real.log L) * (1/(m j:ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ hexp_nonneg
        linarith [hlogB]
      have step2 : (A + (j:ℝ)*Real.log L) * (1/(m j:ℝ))
          ≤ (A + (j:ℝ)*Real.log L) * (1/(c*p^j)) := by
        apply mul_le_mul_of_nonneg_left _ hAj
        exact one_div_le_one_div_of_le hden_pos (hm j)
      calc (Real.log B + (j:ℝ)*Real.log L) * (1/(m j:ℝ))
          ≤ (A + (j:ℝ)*Real.log L) * (1/(m j:ℝ)) := step1
        _ ≤ (A + (j:ℝ)*Real.log L) * (1/(c*p^j)) := step2
        _ = (A + (j:ℝ)*Real.log L)/(c*p^j) := by rw [mul_one_div]
    exact le_trans hb_le (max_le (Real.one_le_exp_iff.mpr (hE_nonneg j)) hD)
  calc (∏ j ∈ Finset.range J, b j ^ (1 / (m j : ℝ)))
      ≤ ∏ j ∈ Finset.range J, Real.exp ((A + (j:ℝ)*Real.log L)/(c*p^j)) :=
        Finset.prod_le_prod₀ (fun j _ => Real.rpow_nonneg (hb j) _) (fun j _ => hterm j)
    _ = Real.exp (∑ j ∈ Finset.range J, (A + (j:ℝ)*Real.log L)/(c*p^j)) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑' j : ℕ, (A + (j:ℝ)*Real.log L)/(c*p^j)) :=
        Real.exp_le_exp.mpr (Summable.sum_le_tsum (Finset.range J) (fun j _ => hE_nonneg j) hsumE)

end Work.NN.Core
