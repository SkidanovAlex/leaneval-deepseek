import Mathlib
import Submission.Commons.Analysis.Normed.norm_prod_one_add_sub_one_sub_sum_le
import Submission.Commons.Algebra.Binomial.pow_one_add_sub_one_sub_mul_le

namespace Commons.Analysis.Complex

open scoped BigOperators

private lemma core (k : ℕ) (x y z : Fin k → ℂ) (ρ : ℝ)
    (hρ0 : 0 < ρ) (hρ2 : ρ ≤ 1 / 2)
    (hx : ∀ j, ‖x j‖ ≤ ρ) (hy : ∀ j, ‖y j‖ ≤ ρ) (hz : ∀ j, ‖z j‖ ≤ ρ) :
    ‖(1 + ∑ j : Fin k, (-(x j) - (y j) + z j)) /
        (∏ j : Fin k, ((1 - x j) * (1 - y j) / (1 - z j))) - 1‖
      ≤ (6:ℝ)^k * (49 * 7^k + 8 * k) * ρ^2 := by
  have hρ1 : (0:ℝ) < 1 - ρ := by linarith
  set u : Fin k → ℂ := fun j => -(x j) - (y j) + (z j) with hu
  set f : Fin k → ℂ := fun j => (1 - x j) * (1 - y j) / (1 - z j) with hf
  set g : Fin k → ℂ := fun j => f j - 1 with hg
  set e : Fin k → ℂ := fun j => (x j * y j - z j * (x j + y j) + z j^2) / (1 - z j) with he
  have hz_ne : ∀ j, 1 - z j ≠ 0 := by
    intro j h
    have h0 : ‖1 - z j‖ = 0 := by rw [h]; simp
    have h1 : (1:ℝ) - ‖z j‖ ≤ ‖1 - z j‖ := by
      have := norm_sub_norm_le (1:ℂ) (z j)
      simp only [norm_one] at this
      exact this
    linarith [hz j]
  -- the algebraic identity f = 1 + u + e
  have hfe : ∀ j, f j = 1 + u j + e j := by
    intro j
    have hj := hz_ne j
    simp only [hf, hu, he]
    field_simp
    ring
  -- bounds
  have hu_bound : ∀ j, ‖u j‖ ≤ 3 * ρ := by
    intro j
    simp only [hu]
    calc ‖-(x j) - y j + z j‖ ≤ ‖-(x j) - y j‖ + ‖z j‖ := norm_add_le _ _
      _ ≤ (‖x j‖ + ‖y j‖) + ‖z j‖ := by
            have h := norm_sub_le (-(x j)) (y j)
            rw [norm_neg] at h
            linarith [norm_nonneg (z j), h]
      _ ≤ 3 * ρ := by linarith [hx j, hy j, hz j]
  have he_bound : ∀ j, ‖e j‖ ≤ 8 * ρ^2 := by
    intro j
    have hnum : ‖x j * y j - z j * (x j + y j) + z j^2‖ ≤ 4 * ρ^2 := by
      have hxy : ‖x j * y j‖ ≤ ρ * ρ := by
        rw [norm_mul]; exact mul_le_mul (hx j) (hy j) (norm_nonneg _) hρ0.le
      have hzxy : ‖z j * (x j + y j)‖ ≤ ρ * (2 * ρ) := by
        rw [norm_mul]
        have hsum : ‖x j + y j‖ ≤ 2 * ρ := by
          calc ‖x j + y j‖ ≤ ‖x j‖ + ‖y j‖ := norm_add_le _ _
            _ ≤ 2 * ρ := by linarith [hx j, hy j]
        exact mul_le_mul (hz j) hsum (norm_nonneg _) hρ0.le
      have hz2 : ‖z j^2‖ ≤ ρ^2 := by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hz j) 2
      calc ‖x j * y j - z j * (x j + y j) + z j^2‖
          ≤ ‖x j * y j - z j * (x j + y j)‖ + ‖z j^2‖ := norm_add_le _ _
        _ ≤ (‖x j * y j‖ + ‖z j * (x j + y j)‖) + ‖z j^2‖ := by
              have h := norm_sub_le (x j * y j) (z j * (x j + y j))
              linarith [norm_nonneg (z j^2), h]
        _ ≤ (ρ * ρ + ρ * (2 * ρ)) + ρ^2 := by linarith [hxy, hzxy, hz2]
        _ = 4 * ρ^2 := by ring
    have hden : (1:ℝ) - ρ ≤ ‖1 - z j‖ := by
      have h := norm_sub_norm_le (1:ℂ) (z j)
      simp only [norm_one] at h
      linarith [hz j]
    simp only [he]
    rw [norm_div]
    calc ‖x j * y j - z j * (x j + y j) + z j^2‖ / ‖1 - z j‖
        ≤ (4 * ρ^2) / (1 - ρ) := div_le_div₀ (by positivity) hnum (by linarith) hden
      _ ≤ 8 * ρ^2 := by
            rw [div_le_iff₀ hρ1]
            nlinarith [hρ0, hρ2]
  have hge : ∀ j, g j = u j + e j := by
    intro j
    simp only [hg, hfe j]
    ring
  have hg_bound : ∀ j, ‖g j‖ ≤ 7 * ρ := by
    intro j
    calc ‖g j‖ = ‖u j + e j‖ := by rw [hge j]
      _ ≤ ‖u j‖ + ‖e j‖ := norm_add_le _ _
      _ ≤ 3 * ρ + 8 * ρ^2 := by linarith [hu_bound j, he_bound j]
      _ ≤ 7 * ρ := by nlinarith [hρ0, hρ2]
  -- denominator lower bound
  have hfj : ∀ j, (1 / 6 : ℝ) ≤ ‖f j‖ := by
    intro j
    have h1 : (1:ℝ) - ρ ≤ ‖1 - x j‖ := by
      have h := norm_sub_norm_le (1:ℂ) (x j)
      simp only [norm_one] at h
      linarith [hx j]
    have h2 : (1:ℝ) - ρ ≤ ‖1 - y j‖ := by
      have h := norm_sub_norm_le (1:ℂ) (y j)
      simp only [norm_one] at h
      linarith [hy j]
    have h3 : ‖1 - z j‖ ≤ 1 + ρ := by
      calc ‖1 - z j‖ ≤ ‖(1:ℂ)‖ + ‖z j‖ := norm_sub_le _ _
        _ = 1 + ‖z j‖ := by rw [norm_one]
        _ ≤ 1 + ρ := by linarith [hz j]
    have hge_z : (1:ℝ) - ρ ≤ ‖1 - z j‖ := by
      have h := norm_sub_norm_le (1:ℂ) (z j)
      simp only [norm_one] at h
      linarith [hz j]
    have hpos : (0:ℝ) < 1 + ρ := by linarith
    have hzpos : (0:ℝ) < ‖1 - z j‖ := by linarith
    have hnum : ((1:ℝ) - ρ) * (1 - ρ) ≤ ‖1 - x j‖ * ‖1 - y j‖ :=
      mul_le_mul h1 h2 hρ1.le (norm_nonneg _)
    have hinv : (1 + ρ)⁻¹ ≤ (‖1 - z j‖)⁻¹ := by
      rw [inv_le_inv₀ hpos hzpos]
      exact h3
    simp only [hf]
    rw [norm_div, norm_mul]
    calc (1 / 6 : ℝ) ≤ ((1:ℝ) - ρ) * (1 - ρ) / (1 + ρ) := by
          rw [le_div_iff₀ hpos]
          nlinarith [hρ0, hρ2]
      _ = ((1:ℝ) - ρ) * (1 - ρ) * (1 + ρ)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ (‖1 - x j‖ * ‖1 - y j‖) * (‖1 - z j‖)⁻¹ :=
            mul_le_mul hnum hinv (by positivity) (by positivity)
      _ = ‖1 - x j‖ * ‖1 - y j‖ / ‖1 - z j‖ := by rw [div_eq_mul_inv]
  have hden : (1 / 6 : ℝ)^k ≤ ‖∏ j : Fin k, f j‖ := by
    rw [norm_prod]
    calc (1 / 6 : ℝ)^k = ∏ j : Fin k, (1 / 6 : ℝ) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ j : Fin k, ‖f j‖ := Finset.prod_le_prod (fun j _ => by norm_num) (fun j _ => hfj j)
  -- numerator bound
  have hP_eq : ∏ j : Fin k, f j = ∏ j : Fin k, (1 + g j) := by
    apply Finset.prod_congr rfl
    intro j _
    simp only [hg]; ring
  have hsum_eq : ∑ j : Fin k, u j = ∑ j : Fin k, g j - ∑ j : Fin k, e j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    show u j = g j - e j
    simp only [hg]
    rw [hfe j]
    ring
  have hnum_eq : 1 + ∑ j : Fin k, u j - ∏ j : Fin k, f j
      = -(∏ j : Fin k, (1 + g j) - 1 - ∑ j : Fin k, g j) - ∑ j : Fin k, e j := by
    rw [hP_eq, hsum_eq]
    ring
  have hprod_bound : ‖∏ j : Fin k, (1 + g j) - 1 - ∑ j : Fin k, g j‖
      ≤ (1 + 7 * ρ)^k - 1 - (k:ℝ) * (7 * ρ) := by
    have h := Commons.Analysis.Normed.norm_prod_one_add_sub_one_sub_sum_le
        (Finset.univ : Finset (Fin k)) g (7 * ρ) (by positivity) (fun j _ => hg_bound j)
    simpa [Finset.card_univ, Fintype.card_fin] using h
  have hbinom : (1 + 7 * ρ)^k - 1 - (k:ℝ) * (7 * ρ) ≤ (7:ℝ)^k * (7 * ρ)^2 :=
    Commons.Algebra.Binomial.pow_one_add_sub_one_sub_mul_le k (7 * ρ) (by positivity) (by linarith)
  have hnume : ‖∑ j : Fin k, e j‖ ≤ (k:ℝ) * (8 * ρ^2) := by
    calc ‖∑ j : Fin k, e j‖ ≤ ∑ j : Fin k, ‖e j‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin k, (8 * ρ^2) := Finset.sum_le_sum (fun j _ => he_bound j)
      _ = (k:ℝ) * (8 * ρ^2) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnum : ‖1 + ∑ j : Fin k, u j - ∏ j : Fin k, f j‖
      ≤ (49 * 7^k + 8 * k) * ρ^2 := by
    rw [hnum_eq]
    calc ‖-(∏ j : Fin k, (1 + g j) - 1 - ∑ j : Fin k, g j) - ∑ j : Fin k, e j‖
        ≤ ‖∏ j : Fin k, (1 + g j) - 1 - ∑ j : Fin k, g j‖ + ‖∑ j : Fin k, e j‖ := by
              have h := norm_sub_le (-(∏ j : Fin k, (1 + g j) - 1 - ∑ j : Fin k, g j))
                (∑ j : Fin k, e j)
              rw [norm_neg] at h
              exact h
      _ ≤ ((1 + 7 * ρ)^k - 1 - (k:ℝ) * (7 * ρ)) + (k:ℝ) * (8 * ρ^2) := by
            linarith [hprod_bound, hnume]
      _ ≤ (49 * 7^k + 8 * k) * ρ^2 := by
            have hb := hbinom
            have h7 : (7:ℝ)^k * (7 * ρ)^2 = 49 * 7^k * ρ^2 := by ring
            rw [h7] at hb
            nlinarith [hb]
  -- final assembly
  have hP_ne : (∏ j : Fin k, f j) ≠ 0 := by
    intro h0
    have hz0 : ‖∏ j : Fin k, f j‖ = 0 := by rw [h0]; simp
    have hpos : (0:ℝ) < (1 / 6 : ℝ)^k := by positivity
    linarith [hden, hz0]
  rw [div_sub_one hP_ne, norm_div]
  calc ‖1 + ∑ j : Fin k, u j - ∏ j : Fin k, f j‖ / ‖∏ j : Fin k, f j‖
      ≤ ((49 * 7^k + 8 * k) * ρ^2) / ((1 / 6 : ℝ)^k) :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = (6:ℝ)^k * (49 * 7^k + 8 * k) * ρ^2 := by
        have h6 : (((1:ℝ) / 6)^k)⁻¹ = 6^k := by rw [one_div, inv_pow, inv_inv]
        rw [div_eq_mul_inv, h6]
        ring

theorem norm_ratio_sub_one_le (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 / 2 → ∀ (x y z : Fin k → ℂ),
      (∀ j, ‖x j‖ ≤ ρ) → (∀ j, ‖y j‖ ≤ ρ) → (∀ j, ‖z j‖ ≤ ρ) →
      ‖(1 + ∑ j : Fin k, (-(x j) - (y j) + z j)) /
          (∏ j : Fin k, ((1 - x j) * (1 - y j) / (1 - z j))) - 1‖ ≤ C * ρ ^ 2 := by
  refine ⟨(6:ℝ)^k * (49 * 7^k + 8 * k), ?_, ?_⟩
  · positivity
  · intro ρ hρ0 hρ2 x y z hx hy hz
    exact core k x y z ρ hρ0 hρ2 hx hy hz

end Commons.Analysis.Complex
