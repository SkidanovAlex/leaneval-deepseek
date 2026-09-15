import Mathlib

namespace Commons.Measure.EuclideanSpace

open MeasureTheory Metric

/-- On `Fin d → ℂ` (with the product sup norm) the norm is attained by some coordinate. -/
private lemma exists_norm_eq_fin (d : ℕ) (hd : 1 ≤ d) (z : Fin d → ℂ) :
    ∃ j : Fin d, ‖z‖ = ‖z j‖ := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d))
    ⟨⟨0, hd⟩, Finset.mem_univ _⟩ (fun b => ‖z b‖₊)
  exact ⟨j, by rw [Pi.norm_def, hj]; simp⟩

/-- `∑ j, ‖z j‖ ^ 2` is at most `d` times `‖z‖ ^ 2`. -/
private lemma sum_normSq_le (d : ℕ) (z : Fin d → ℂ) :
    ∑ j, ‖z j‖ ^ 2 ≤ (d : ℝ) * ‖z‖ ^ 2 := by
  calc ∑ j, ‖z j‖ ^ 2 ≤ ∑ _j : Fin d, ‖z‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm z j) 2
    _ = (d : ℝ) * ‖z‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]

/-- `‖z‖ ^ 2` is at most `∑ j, ‖z j‖ ^ 2`. -/
private lemma normSq_le_sum_normSq (d : ℕ) (hd : 1 ≤ d) (z : Fin d → ℂ) :
    ‖z‖ ^ 2 ≤ ∑ j, ‖z j‖ ^ 2 := by
  obtain ⟨j, hj⟩ := exists_norm_eq_fin d hd z
  calc ‖z‖ ^ 2 = ‖z j‖ ^ 2 := by rw [hj]
    _ ≤ ∑ b, ‖z b‖ ^ 2 :=
        Finset.single_le_sum (fun i _ => sq_nonneg (‖z i‖)) (Finset.mem_univ j)

/-- Pointwise two-sided logarithmic bound:
`|log (∑ j, ‖z j‖ ^ 2)| ≤ log d + 2 * |log ‖z‖|` for `z ≠ 0`. -/
private lemma abs_log_sum_normSq_le (d : ℕ) (hd : 1 ≤ d) (z : Fin d → ℂ) (hz : z ≠ 0) :
    |Real.log (∑ j, ‖z j‖ ^ 2)| ≤ Real.log d + 2 * |Real.log ‖z‖| := by
  have hs_pos : 0 < ‖z‖ ^ 2 := pow_pos (norm_pos_iff.mpr hz) 2
  have hs_ne : ‖z‖ ^ 2 ≠ 0 := ne_of_gt hs_pos
  have hr_ge : ‖z‖ ^ 2 ≤ ∑ j, ‖z j‖ ^ 2 := normSq_le_sum_normSq d hd z
  have hr_le : ∑ j, ‖z j‖ ^ 2 ≤ (d : ℝ) * ‖z‖ ^ 2 := sum_normSq_le d z
  have hr_pos : 0 < ∑ j, ‖z j‖ ^ 2 := lt_of_lt_of_le hs_pos hr_ge
  have hratio_lo : 1 ≤ (∑ j, ‖z j‖ ^ 2) / ‖z‖ ^ 2 :=
    (le_div_iff₀ hs_pos).mpr (by rw [one_mul]; exact hr_ge)
  have hratio_hi : (∑ j, ‖z j‖ ^ 2) / ‖z‖ ^ 2 ≤ (d : ℝ) := by
    rw [div_le_iff₀ hs_pos]; exact hr_le
  have hlogr0 : 0 ≤ Real.log ((∑ j, ‖z j‖ ^ 2) / ‖z‖ ^ 2) := Real.log_nonneg hratio_lo
  have hlogr_le : Real.log ((∑ j, ‖z j‖ ^ 2) / ‖z‖ ^ 2) ≤ Real.log (d : ℝ) :=
    Real.log_le_log (by positivity) hratio_hi
  have habs : |Real.log ((∑ j, ‖z j‖ ^ 2) / ‖z‖ ^ 2)| ≤ Real.log (d : ℝ) := by
    rw [abs_of_nonneg hlogr0]; exact hlogr_le
  have hlog : Real.log (∑ j, ‖z j‖ ^ 2)
      = Real.log ((∑ j, ‖z j‖ ^ 2) / ‖z‖ ^ 2) + Real.log (‖z‖ ^ 2) := by
    rw [Real.log_div (ne_of_gt hr_pos) hs_ne]; ring
  have hlog_s : Real.log (‖z‖ ^ 2) = 2 * Real.log ‖z‖ := by
    rw [Real.log_pow]; norm_num
  calc |Real.log (∑ j, ‖z j‖ ^ 2)|
      = |Real.log ((∑ j, ‖z j‖ ^ 2) / ‖z‖ ^ 2) + Real.log (‖z‖ ^ 2)| := by rw [hlog]
    _ ≤ |Real.log ((∑ j, ‖z j‖ ^ 2) / ‖z‖ ^ 2)| + |Real.log (‖z‖ ^ 2)| := abs_add_le _ _
    _ = |Real.log ((∑ j, ‖z j‖ ^ 2) / ‖z‖ ^ 2)| + 2 * |Real.log ‖z‖| := by
        rw [hlog_s, abs_mul]; norm_num
    _ ≤ Real.log d + 2 * |Real.log ‖z‖| := by linarith

/-- There is a nonnegative constant `C` with `A + B * |log t| ≤ C * t⁻¹` for all
`t ∈ (0, R]`. -/
private lemma exists_inv_bound_abs_log (A B R : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Set.Ioc (0 : ℝ) R, A + B * |Real.log t| ≤ C * t⁻¹ := by
  have hcont : Continuous fun t : ℝ => A * t + B * |t * Real.log t| :=
    ((continuous_const.mul continuous_id).add
      ((Real.continuous_mul_log.abs).const_mul B))
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
  intro t ht
  have ht0 : 0 < t := ht.1
  have hmem : t ∈ Set.Icc (0 : ℝ) R := ⟨ht0.le, ht.2⟩
  have hb : ‖A * t + B * |t * Real.log t|‖ ≤ C₀ := hC₀ t hmem
  have hval : A * t + B * |t * Real.log t| = t * (A + B * |Real.log t|) := by
    rw [abs_mul, abs_of_nonneg ht0.le]; ring
  have hnn : 0 ≤ A * t + B * |t * Real.log t| := by
    have h1 : 0 ≤ A * t := mul_nonneg hA ht0.le
    have h2 : 0 ≤ B * |t * Real.log t| := mul_nonneg hB (abs_nonneg _)
    linarith
  have hle : t * (A + B * |Real.log t|) ≤ max C₀ 0 := by
    rw [← hval]
    calc A * t + B * |t * Real.log t| = ‖A * t + B * |t * Real.log t|‖ :=
          (Real.norm_of_nonneg hnn).symm
      _ ≤ C₀ := hb
      _ ≤ max C₀ 0 := le_max_left _ _
  calc A + B * |Real.log t|
      = t⁻¹ * (t * (A + B * |Real.log t|)) := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt ht0), one_mul]
    _ ≤ t⁻¹ * max C₀ 0 := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr ht0.le)
    _ = max C₀ 0 * t⁻¹ := by ring

theorem integrable_log_sum_sq_mul {d : ℕ} (hd : 1 ≤ d) (ψ : (Fin d → ℂ) → ℝ)
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) :
    MeasureTheory.Integrable (fun z : Fin d → ℂ => Real.log (∑ j, ‖z j‖ ^ 2) * ψ z)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) := by
  obtain ⟨M, hM⟩ := hψs.exists_bound_of_continuous hψc
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  obtain ⟨R, hRpos, hR⟩ := hψs.isCompact.isBounded.exists_pos_norm_lt
  obtain ⟨Cg, hCgnn, hCg⟩ :=
    exists_inv_bound_abs_log (Real.log d) 2 R (Real.log_nonneg (by exact_mod_cast hd))
      (by norm_num)
  have hfin : Module.finrank ℝ (Fin d → ℂ) = 2 * d := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, Finset.sum_const, Nat.mul_comm]
  have hfin1 : 1 ≤ Module.finrank ℝ (Fin d → ℂ) := by rw [hfin]; omega
  have hα : (1 : ℝ) < (Module.finrank ℝ (Fin d → ℂ) : ℝ) := by
    rw [hfin]
    exact_mod_cast (by omega : 1 < 2 * d)
  have hmeas : AEStronglyMeasurable
      (fun z : Fin d → ℂ => Real.log (∑ j, ‖z j‖ ^ 2) * ψ z) volume := by
    have hcont : Continuous fun z : Fin d → ℂ => ∑ j, ‖z j‖ ^ 2 := by
      apply continuous_finsetSum
      intro j _
      exact ((continuous_apply j : Continuous fun z : Fin d → ℂ => z j).norm).pow 2
    exact ((Real.measurable_log.comp hcont.measurable).mul hψc.measurable).aestronglyMeasurable
  have hdecay : ∀ᵐ z ∂volume.restrict (ball (0 : Fin d → ℂ) R),
      ‖Real.log (∑ j, ‖z j‖ ^ 2) * ψ z‖ ≤ (M * Cg) * ‖z‖ ^ (-1 : ℝ) := by
    filter_upwards [self_mem_ae_restrict measurableSet_ball] with z hz
    have hzR : ‖z‖ < R := by simpa [dist_eq_norm] using hz
    by_cases hz0 : z = 0
    · subst hz0
      rw [norm_zero, Real.zero_rpow (by norm_num : (-1 : ℝ) ≠ 0), mul_zero]
      simp [Real.log_zero]
    · have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      have hbound := abs_log_sum_normSq_le d hd z hz0
      have hCz : Real.log d + 2 * |Real.log ‖z‖| ≤ Cg * ‖z‖ ^ (-1 : ℝ) := by
        simpa [Real.rpow_neg_one] using hCg ‖z‖ ⟨hzpos, hzR.le⟩
      calc ‖Real.log (∑ j, ‖z j‖ ^ 2) * ψ z‖
          = |Real.log (∑ j, ‖z j‖ ^ 2)| * |ψ z| := by rw [Real.norm_eq_abs, abs_mul]
        _ ≤ |Real.log (∑ j, ‖z j‖ ^ 2)| * M := mul_le_mul_of_nonneg_left (hM z) (abs_nonneg _)
        _ ≤ (Real.log d + 2 * |Real.log ‖z‖|) * M := mul_le_mul_of_nonneg_right hbound hM0
        _ ≤ (Cg * ‖z‖ ^ (-1 : ℝ)) * M := mul_le_mul_of_nonneg_right hCz hM0
        _ = (M * Cg) * ‖z‖ ^ (-1 : ℝ) := by ring
  have hsupp : Function.support
      (fun z : Fin d → ℂ => Real.log (∑ j, ‖z j‖ ^ 2) * ψ z) ⊆ ball (0 : Fin d → ℂ) R := by
    intro z hz
    by_contra hznot
    have hzge : R ≤ ‖z‖ := by
      rw [mem_ball, not_lt, dist_eq_norm, sub_zero] at hznot
      exact hznot
    have hzpsi : ψ z = 0 := by
      by_contra hzpsi
      have hzt : z ∈ tsupport ψ := subset_tsupport ψ (Function.mem_support.mpr hzpsi)
      exact absurd (hR z hzt) (not_lt.mpr hzge)
    exact (Function.mem_support.mp hz) (by rw [hzpsi, mul_zero])
  exact (integrableOn_iff_integrable_of_support_subset hsupp).mp
    (integrableOn_ball_of_norm_le_rpow hfin1 hα hdecay hmeas)

end Commons.Measure.EuclideanSpace
