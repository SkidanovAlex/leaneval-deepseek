import Mathlib
import Submission.Work.FIArea7.sum_abs_inv_le
import Submission.Work.FIArea7.sum_inv_sq_le

namespace Work.FIArea7

theorem finset_sum_coeff_le (R : ℕ) (hR : 2 ≤ R) (M : ℝ) (hM0 : 0 ≤ M)
    (ĉ : ℤ → ℂ)
    (h0 : ‖ĉ 0‖ ≤ 1)
    (h1 : ∀ k : ℤ, k ≠ 0 → ‖ĉ k‖ ≤ M / |(k : ℝ)|)
    (h2 : ∀ k : ℤ, k ≠ 0 → ‖ĉ k‖ ≤ 3 * M * (R : ℝ) / (2 * (k : ℝ) ^ 2))
    (s : Finset ℤ) :
    ∑ k ∈ s, ‖ĉ k‖ ≤ (7 * M + 1) * Real.log (2 * (R : ℝ)) := by
  classical
  have hR1 : 1 ≤ R := by omega
  have hRpos : (0:ℝ) < (R:ℝ) := by positivity
  have hR2 : (2:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
  set A : Finset ℤ := s.filter (fun k => |(k:ℝ)| ≤ (R:ℝ)) with hA
  set B : Finset ℤ := s.filter (fun k => ¬ (|(k:ℝ)| ≤ (R:ℝ))) with hB
  have hsplit : ∑ k ∈ s, ‖ĉ k‖ = ∑ k ∈ A, ‖ĉ k‖ + ∑ k ∈ B, ‖ĉ k‖ := by
    rw [hA, hB]
    exact (Finset.sum_filter_add_sum_filter_not s (fun k => |(k:ℝ)| ≤ (R:ℝ)) (fun k => ‖ĉ k‖)).symm
  set A0 : Finset ℤ := A.filter (fun k => k = 0) with hA0
  set A1 : Finset ℤ := A.filter (fun k => ¬ (k = 0)) with hA1
  have hA_split : ∑ k ∈ A, ‖ĉ k‖ = ∑ k ∈ A0, ‖ĉ k‖ + ∑ k ∈ A1, ‖ĉ k‖ := by
    rw [hA0, hA1]
    exact (Finset.sum_filter_add_sum_filter_not A (fun k => k = 0) (fun k => ‖ĉ k‖)).symm
  have hA0le : ∑ k ∈ A0, ‖ĉ k‖ ≤ 1 := by
    have hsub : A0 ⊆ ({0} : Finset ℤ) := by
      intro k hk
      rw [Finset.mem_singleton]
      rw [hA0] at hk
      exact (Finset.mem_filter.mp hk).2
    calc ∑ k ∈ A0, ‖ĉ k‖ ≤ ∑ k ∈ ({0} : Finset ℤ), ‖ĉ k‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro i _ _; exact norm_nonneg _)
      _ = ‖ĉ 0‖ := by simp
      _ ≤ 1 := h0
  have hA1_hyp : ∀ k ∈ A1, (k:ℝ) ≠ 0 ∧ |(k:ℝ)| ≤ (R:ℝ) := by
    intro k hk
    rw [hA1] at hk
    have hkA : k ∈ A := (Finset.mem_filter.mp hk).1
    have hkne : ¬ (k = 0) := (Finset.mem_filter.mp hk).2
    rw [hA] at hkA
    have hp : |(k:ℝ)| ≤ (R:ℝ) := (Finset.mem_filter.mp hkA).2
    refine ⟨?_, hp⟩
    intro hc
    exact hkne (by exact_mod_cast hc)
  have hA1le : ∑ k ∈ A1, ‖ĉ k‖ ≤ 2 * M * (1 + Real.log (R:ℝ)) := by
    have step1 : ∑ k ∈ A1, ‖ĉ k‖ ≤ ∑ k ∈ A1, M * (1 / |(k:ℝ)|) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [hA1] at hk
      have hkne : k ≠ 0 := by
        intro hc; exact (Finset.mem_filter.mp hk).2 hc
      have h := h1 k hkne
      rwa [div_eq_mul_one_div] at h
    have step2 : ∑ k ∈ A1, M * (1 / |(k:ℝ)|) = M * ∑ k ∈ A1, 1 / |(k:ℝ)| := by
      rw [Finset.mul_sum]
    have step3 : M * ∑ k ∈ A1, 1 / |(k:ℝ)| ≤ M * (2 * (1 + Real.log (R:ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ hM0
      exact sum_abs_inv_le R A1 hA1_hyp
    calc ∑ k ∈ A1, ‖ĉ k‖ ≤ ∑ k ∈ A1, M * (1 / |(k:ℝ)|) := step1
      _ = M * ∑ k ∈ A1, 1 / |(k:ℝ)| := step2
      _ ≤ M * (2 * (1 + Real.log (R:ℝ))) := step3
      _ = 2 * M * (1 + Real.log (R:ℝ)) := by ring
  have hhead : ∑ k ∈ A, ‖ĉ k‖ ≤ 1 + 2 * M * (1 + Real.log (R:ℝ)) := by
    rw [hA_split]; linarith
  have hB_hyp : ∀ k ∈ B, (R:ℝ) < |(k:ℝ)| := by
    intro k hk
    have h := (Finset.mem_filter.mp (hB ▸ hk)).2
    exact not_le.mp h
  have hB_ne : ∀ k ∈ B, k ≠ 0 := by
    intro k hk hk0
    have h := hB_hyp k hk
    rw [hk0] at h
    simp at h
    linarith [hRpos]
  have htail : ∑ k ∈ B, ‖ĉ k‖ ≤ 3 * M := by
    have step1 : ∑ k ∈ B, ‖ĉ k‖ ≤ ∑ k ∈ B, (3 * M * (R:ℝ) / 2) * (1 / (k:ℝ)^2) := by
      apply Finset.sum_le_sum
      intro k hk
      have h := h2 k (hB_ne k hk)
      rwa [show 3 * M * (R:ℝ) / (2 * (k:ℝ)^2) = (3 * M * (R:ℝ) / 2) * (1 / ((k:ℝ)^2)) from by ring_nf] at h
    have step2 : ∑ k ∈ B, (3 * M * (R:ℝ) / 2) * (1 / (k:ℝ)^2)
        = (3 * M * (R:ℝ) / 2) * ∑ k ∈ B, 1 / (k:ℝ)^2 := by
      rw [Finset.mul_sum]
    have hCnn : (0:ℝ) ≤ 3 * M * (R:ℝ) / 2 := by positivity
    have step3 : (3 * M * (R:ℝ) / 2) * ∑ k ∈ B, 1 / (k:ℝ)^2
        ≤ (3 * M * (R:ℝ) / 2) * (2 / (R:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hCnn
      exact sum_inv_sq_le R hR1 B hB_hyp
    have step4 : (3 * M * (R:ℝ) / 2) * (2 / (R:ℝ)) = 3 * M := by field_simp
    calc ∑ k ∈ B, ‖ĉ k‖ ≤ ∑ k ∈ B, (3 * M * (R:ℝ) / 2) * (1 / (k:ℝ)^2) := step1
      _ = (3 * M * (R:ℝ) / 2) * ∑ k ∈ B, 1 / (k:ℝ)^2 := step2
      _ ≤ (3 * M * (R:ℝ) / 2) * (2 / (R:ℝ)) := step3
      _ = 3 * M := step4
  have hfinal : 1 + 2 * M * (1 + Real.log (R:ℝ)) + 3 * M ≤ (7 * M + 1) * Real.log (2 * (R:ℝ)) := by
    have hL : (1:ℝ)/2 ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
      norm_num at h; linarith
    have hLR : Real.log 2 ≤ Real.log (R:ℝ) := Real.log_le_log (by norm_num) hR2
    rw [Real.log_mul (by norm_num) (ne_of_gt hRpos)]
    have h1' : 1 + 5*M ≤ (12*M+2) * Real.log 2 := by nlinarith [hL, hM0]
    have hm : (0:ℝ) ≤ 5*M + 1 := by linarith
    have h3 : (5*M+1) * Real.log 2 ≤ (5*M+1) * Real.log (R:ℝ) :=
      mul_le_mul_of_nonneg_left hLR hm
    nlinarith [h1', h3]
  calc ∑ k ∈ s, ‖ĉ k‖ = ∑ k ∈ A, ‖ĉ k‖ + ∑ k ∈ B, ‖ĉ k‖ := hsplit
    _ ≤ (1 + 2 * M * (1 + Real.log (R:ℝ))) + 3 * M := by linarith [hhead, htail]
    _ ≤ (7 * M + 1) * Real.log (2 * (R:ℝ)) := hfinal

end Work.FIArea7
