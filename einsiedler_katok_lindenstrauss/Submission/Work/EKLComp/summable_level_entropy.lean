import Mathlib
import Submission.Work.EKLComp.ennreal_tsum_le_one
import Submission.Work.EKLComp.mul_log_inv_le_index
import Submission.Work.EKLComp.summable_exp_neg

namespace Work.EKLComp

/-- The entropy-type quantity `a i * log (N i / a i)` produced by a weight sequence `a`
together with level sizes `N i` is summable, and its total is bounded by
`4 + |log c| + κ + ∑ i * exp (-i)` whenever `∑ a ≤ 1`, `∑ i * a i ≤ 1` and
`N i ≤ c * exp (κ * i)`. -/
theorem summable_level_entropy (a : ℕ → ℝ) (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    (hsum : (∑' i : ℕ, ENNReal.ofReal (a i)) ≤ 1)
    (hkac : (∑' i : ℕ, ENNReal.ofReal ((i : ℝ) * a i)) ≤ 1)
    (N : ℕ → ℕ) (hN1 : ∀ i, 1 ≤ N i)
    (c κ : ℝ) (hc : 0 ≤ c) (hκ : 0 ≤ κ)
    (hN : ∀ i, (N i : ℝ) ≤ c * Real.exp (κ * (i : ℝ))) :
    Summable (fun i : ℕ => a i * Real.log ((N i : ℝ) / a i)) ∧
      (∑' i : ℕ, a i * Real.log ((N i : ℝ) / a i))
        ≤ 4 + |Real.log c| + κ + ∑' i : ℕ, (i : ℝ) * Real.exp (-(i : ℝ)) := by
  obtain ⟨ha_sum, ha_le⟩ := ennreal_tsum_le_one a ha0 hsum
  have hia0 : ∀ i : ℕ, 0 ≤ (i : ℝ) * a i := fun i => mul_nonneg (Nat.cast_nonneg i) (ha0 i)
  obtain ⟨hia_sum, hia_le⟩ := ennreal_tsum_le_one (fun i : ℕ => (i:ℝ) * a i) hia0 hkac
  obtain ⟨hE_sum, hE_le, hD_sum⟩ := summable_exp_neg
  have hc1 : 1 ≤ c := by
    have h := hN 0
    simp only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one] at h
    have : (1:ℝ) ≤ (N 0 : ℝ) := by exact_mod_cast hN1 0
    linarith
  have hcpos : 0 < c := lt_of_le_of_ne hc (by linarith [hc1])
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc1
  have hA_sum : Summable (fun i : ℕ => Real.log c * a i) := ha_sum.mul_left _
  have hB_sum : Summable (fun i : ℕ => κ * ((i:ℝ) * a i)) := hia_sum.mul_left _
  have hpoint : ∀ i : ℕ, a i * Real.log ((N i : ℝ) / a i)
      ≤ Real.log c * a i + κ * ((i : ℝ) * a i)
        + ((i : ℝ) * a i + ((i : ℝ) * Real.exp (-(i : ℝ)) + Real.exp (-(i : ℝ)))) := by
    intro i
    by_cases hai : a i = 0
    · rw [hai]
      simp only [mul_zero, div_zero, Real.log_zero, add_zero, zero_add]
      positivity
    · have hai_pos : 0 < a i := lt_of_le_of_ne (ha0 i) (Ne.symm hai)
      have hNpos : (0:ℝ) < (N i : ℝ) := by
        have : (1:ℝ) ≤ (N i : ℝ) := by exact_mod_cast hN1 i
        linarith
      have hlog_le : Real.log ((N i : ℝ) / a i) ≤ Real.log c + κ * (i:ℝ) + Real.log (1 / a i) := by
        have h1 : Real.log ((N i : ℝ) / a i) ≤ Real.log (c * Real.exp (κ * (i:ℝ)) / a i) := by
          apply Real.log_le_log (div_pos hNpos hai_pos)
          exact div_le_div_of_nonneg_right (hN i) (le_of_lt hai_pos)
        have h2 : Real.log (c * Real.exp (κ * (i:ℝ)) / a i) = Real.log c + κ * (i:ℝ) + Real.log (1 / a i) := by
          rw [Real.log_div (mul_ne_zero (ne_of_gt hcpos) (Real.exp_ne_zero _)) (ne_of_gt hai_pos),
            Real.log_mul (ne_of_gt hcpos) (Real.exp_ne_zero _), Real.log_exp, one_div, Real.log_inv]
          ring
        linarith
      calc a i * Real.log ((N i : ℝ) / a i)
          ≤ a i * (Real.log c + κ * (i:ℝ) + Real.log (1 / a i)) :=
            mul_le_mul_of_nonneg_left hlog_le (ha0 i)
        _ = Real.log c * a i + κ * ((i:ℝ) * a i) + a i * Real.log (1 / a i) := by ring
        _ ≤ Real.log c * a i + κ * ((i : ℝ) * a i)
              + ((i : ℝ) * a i + ((i : ℝ) * Real.exp (-(i : ℝ)) + Real.exp (-(i : ℝ)))) := by
            have hD := mul_log_inv_le_index (a i) (ha0 i) (ha1 i) i
            linarith
  have hfnn : ∀ i : ℕ, 0 ≤ a i * Real.log ((N i : ℝ)/a i) := by
    intro i
    by_cases hai : a i = 0
    · rw [hai]; simp
    · have hai_pos : 0 < a i := lt_of_le_of_ne (ha0 i) (Ne.symm hai)
      have hN1' : (1:ℝ) ≤ (N i : ℝ) := by exact_mod_cast hN1 i
      have hge : (1:ℝ) ≤ (N i:ℝ)/a i := by
        rw [one_le_div hai_pos]
        linarith [ha1 i]
      exact mul_nonneg (ha0 i) (Real.log_nonneg hge)
  have hg_sum : Summable (fun i : ℕ => Real.log c * a i + κ * ((i:ℝ)*a i)
      + ((i:ℝ)*a i + ((i:ℝ)*Real.exp (-(i:ℝ)) + Real.exp (-(i:ℝ))))) :=
    (hA_sum.add hB_sum).add (hia_sum.add (hD_sum.add hE_sum))
  have hf_sum : Summable (fun i : ℕ => a i * Real.log ((N i : ℝ)/a i)) :=
    Summable.of_norm_bounded hg_sum (fun i => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hfnn i)]
      exact hpoint i)
  have hle_tsum : (∑' i : ℕ, a i * Real.log ((N i : ℝ)/a i))
      ≤ ∑' i : ℕ, (Real.log c * a i + κ * ((i:ℝ)*a i)
          + ((i:ℝ)*a i + ((i:ℝ)*Real.exp (-(i:ℝ)) + Real.exp (-(i:ℝ))))) :=
    Summable.tsum_le_tsum hpoint hf_sum hg_sum
  have hg_split : (∑' i : ℕ, (Real.log c * a i + κ * ((i:ℝ)*a i)
        + ((i:ℝ)*a i + ((i:ℝ)*Real.exp (-(i:ℝ)) + Real.exp (-(i:ℝ))))))
      = Real.log c * (∑' i : ℕ, a i) + κ * (∑' i : ℕ, (i:ℝ)*a i)
        + ((∑' i : ℕ, (i:ℝ)*a i) + ((∑' i : ℕ, (i:ℝ)*Real.exp (-(i:ℝ))) + (∑' i : ℕ, Real.exp (-(i:ℝ))))) := by
    have hAB : Summable (fun i : ℕ => Real.log c * a i + κ * ((i:ℝ) * a i)) := hA_sum.add hB_sum
    have hDE : Summable (fun i : ℕ => (i:ℝ) * Real.exp (-(i:ℝ)) + Real.exp (-(i:ℝ))) := hD_sum.add hE_sum
    have hCDE : Summable (fun i : ℕ => (i:ℝ) * a i + ((i:ℝ) * Real.exp (-(i:ℝ)) + Real.exp (-(i:ℝ)))) :=
      hia_sum.add hDE
    simp only [Summable.tsum_add hAB hCDE, Summable.tsum_add hA_sum hB_sum,
      Summable.tsum_add hia_sum hDE, Summable.tsum_add hD_sum hE_sum,
      Summable.tsum_mul_left (Real.log c) ha_sum, Summable.tsum_mul_left κ hia_sum]
  have hbound_g : (∑' i : ℕ, (Real.log c * a i + κ * ((i:ℝ)*a i)
        + ((i:ℝ)*a i + ((i:ℝ)*Real.exp (-(i:ℝ)) + Real.exp (-(i:ℝ))))))
      ≤ 4 + |Real.log c| + κ + ∑' i : ℕ, (i:ℝ) * Real.exp (-(i:ℝ)) := by
    rw [hg_split]
    have hA : Real.log c * (∑' i : ℕ, a i) ≤ |Real.log c| := by
      rw [abs_of_nonneg hlogc]
      calc Real.log c * (∑' i : ℕ, a i) ≤ Real.log c * 1 := mul_le_mul_of_nonneg_left ha_le hlogc
        _ = Real.log c := mul_one _
    have hB : κ * (∑' i : ℕ, (i:ℝ)*a i) ≤ κ := by
      calc κ * (∑' i : ℕ, (i:ℝ)*a i) ≤ κ * 1 := mul_le_mul_of_nonneg_left hia_le hκ
        _ = κ := mul_one _
    linarith [hA, hB, hE_le, hia_le]
  exact ⟨hf_sum, le_trans hle_tsum hbound_g⟩

end Work.EKLComp
