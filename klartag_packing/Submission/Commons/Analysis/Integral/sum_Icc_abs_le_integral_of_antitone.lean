import Mathlib
import Submission.Commons.Algebra.BigOperators.sum_Icc_even_int

namespace Commons.Analysis.Integral

open MeasureTheory intervalIntegral Finset

theorem sum_Icc_abs_le_integral_of_antitone {F : ℝ → ℝ} (hcont : Continuous F)
    (hnonneg : ∀ x, 0 ≤ x → 0 ≤ F x) (hF : ∀ a b, 0 ≤ a → a ≤ b → F b ≤ F a) {T : ℝ}
    (hT : 0 ≤ T) :
    (∑ k ∈ Finset.Icc (-⌊T⌋) ⌊T⌋, F |(k : ℝ)|) ≤ F 0 + 2 * ∫ x in (0:ℝ)..T, F x := by
  set Q : ℤ := ⌊T⌋ with hQdef
  have hQ0 : (0:ℤ) ≤ Q := by rw [hQdef]; exact Int.floor_nonneg.mpr hT
  have hQT : (Q:ℝ) ≤ T := by rw [hQdef]; exact Int.floor_le T
  set m : ℕ := Q.toNat with hmdef
  have hmQ : (m:ℤ) = Q := by rw [hmdef]; exact Int.toNat_of_nonneg hQ0
  have hmR : (m:ℝ) = (Q:ℝ) := by
    rw [← hmQ]; push_cast; ring
  have hmT : (m:ℝ) ≤ T := by rw [hmR]; exact hQT
  have hQ0R : (0:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ0
  -- Symmetric decomposition of the sum via the evenness of `k ↦ F |k|`.
  have heven := Commons.Algebra.BigOperators.sum_Icc_even_int Q hQ0
      (fun k : ℤ => F |(k:ℝ)|) (fun j => by simp [Int.cast_neg])
  -- Termwise comparison of `F (k+1)` with the integral over `[k, k+1]`.
  have hterm : ∀ k ∈ Finset.range m, F (((k+1:ℕ):ℝ)) ≤ ∫ x in (k:ℝ)..((k+1:ℕ):ℝ), F x := by
    intro k _
    have hle : (k:ℝ) ≤ ((k+1:ℕ):ℝ) := by simp only [Nat.cast_add, Nat.cast_one]; linarith
    have hc : IntervalIntegrable (fun _ : ℝ => F (((k+1:ℕ):ℝ))) volume (k:ℝ) ((k+1:ℕ):ℝ) :=
      intervalIntegrable_const
    have hf : IntervalIntegrable F volume (k:ℝ) ((k+1:ℕ):ℝ) := hcont.intervalIntegrable _ _
    have hmono := intervalIntegral.integral_mono_on hle hc hf (fun x hx => by
      rw [Set.mem_Icc] at hx
      exact hF x (((k+1:ℕ):ℝ)) (le_trans (Nat.cast_nonneg k) hx.1) hx.2)
    calc F (((k+1:ℕ):ℝ))
          = ∫ x in (k:ℝ)..((k+1:ℕ):ℝ), (fun _ : ℝ => F (((k+1:ℕ):ℝ))) x := by
            rw [intervalIntegral.integral_const]; simp
      _ ≤ ∫ x in (k:ℝ)..((k+1:ℕ):ℝ), F x := hmono
  have hB : (∑ k ∈ Finset.range m, F (((k+1:ℕ):ℝ))) ≤ ∫ x in (0:ℝ)..(m:ℝ), F x := by
    calc (∑ k ∈ Finset.range m, F (((k+1:ℕ):ℝ)))
          ≤ ∑ k ∈ Finset.range m, ∫ x in (k:ℝ)..((k+1:ℕ):ℝ), F x :=
            Finset.sum_le_sum hterm
      _ = ∫ x in (0:ℝ)..(m:ℝ), F x := by
            rw [intervalIntegral.sum_integral_adjacent_intervals]
            · simp
            · intro k _
              exact hcont.intervalIntegrable _ _
  have hIntFinal : ∫ x in (0:ℝ)..(m:ℝ), F x ≤ ∫ x in (0:ℝ)..T, F x := by
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (hcont.intervalIntegrable (0:ℝ) (m:ℝ)) (hcont.intervalIntegrable (m:ℝ) T)
    have hnn : 0 ≤ ∫ x in (m:ℝ)..T, F x :=
      intervalIntegral.integral_nonneg hmT
        (fun u hu => hnonneg u (le_trans (Nat.cast_nonneg m) hu.1))
    linarith [hsplit]
  have hAB : (∑ k ∈ Finset.range m, F ((k:ℝ))) + F (m:ℝ)
      = (∑ k ∈ Finset.range m, F (((k+1:ℕ):ℝ))) + F 0 := by
    have h1 := Finset.sum_range_succ (fun k : ℕ => F ((k:ℝ))) m
    have h2 := Finset.sum_range_succ' (fun k : ℕ => F ((k:ℝ))) m
    rw [h1] at h2
    simpa only [Nat.cast_zero] using h2
  calc (∑ k ∈ Finset.Icc (-Q) Q, F |(k:ℝ)|)
        = 2 * (∑ k ∈ Finset.range Q.toNat, F |((k:ℤ):ℝ)|) - F |((0:ℤ):ℝ)| + 2 * F |(Q:ℝ)| := heven
    _ = 2 * (∑ k ∈ Finset.range m, F ((k:ℝ))) - F 0 + 2 * F (m:ℝ) := by
          have eq1 : (∑ k ∈ Finset.range Q.toNat, F |((k:ℤ):ℝ)|)
              = ∑ k ∈ Finset.range m, F ((k:ℝ)) := by
            rw [← hmdef]
            apply Finset.sum_congr rfl
            intro k _
            congr 1
            rw [show ((k:ℤ):ℝ) = (k:ℝ) by norm_num]
            exact abs_of_nonneg (Nat.cast_nonneg k)
          have eq2 : F |((0:ℤ):ℝ)| = F 0 := by norm_num
          have eq3 : F |(Q:ℝ)| = F (m:ℝ) := by
            rw [abs_of_nonneg hQ0R, ← hmR]
          rw [eq1, eq2, eq3]
    _ = F 0 + 2 * (∑ k ∈ Finset.range m, F (((k+1:ℕ):ℝ))) := by linarith [hAB]
    _ ≤ F 0 + 2 * ∫ x in (0:ℝ)..T, F x := by linarith [hB, hIntFinal]

end Commons.Analysis.Integral
