import Mathlib
import Submission.Work.KMTPlan.A6.HHBasic

namespace Work.KMTPlan.A6

open MeasureTheory

/-- **Cauchy–Schwarz for a series supported on `Pm`.**

If the squares of `φ` (resp. `ψ`) have finite sums bounded by `(Bφ * u)^2` (resp. `(Bψ * v)^2`)
over every finite set contained in `Pm`, then the series `∑_{n : Pm n} φ n * ψ n` is at most
`Bφ * Bψ * u * v`. -/
theorem tsum_mul_le_of_finset_sq_le (φ ψ : ℕ → ENNReal) (Pm : ℕ → Prop) [DecidablePred Pm]
    (Bφ Bψ u v : ENNReal)
    (hφ : ∀ s : Finset ℕ, (∀ n ∈ s, Pm n) → (∑ n ∈ s, (φ n) ^ 2) ≤ Bφ ^ 2 * u ^ 2)
    (hψ : ∀ s : Finset ℕ, (∀ n ∈ s, Pm n) → (∑ n ∈ s, (ψ n) ^ 2) ≤ Bψ ^ 2 * v ^ 2) :
    (∑' n : ℕ, if Pm n then φ n * ψ n else 0) ≤ Bφ * Bψ * u * v := by
  classical
  -- Cauchy–Schwarz (Hölder at `p = q = 2`) for the counting measure on `ℕ`.
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have key : (∑' n : ℕ, (if Pm n then φ n else 0) * (if Pm n then ψ n else 0))
      ≤ (∑' n : ℕ, (if Pm n then φ n else 0) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
        * (∑' n : ℕ, (if Pm n then ψ n else 0) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq
      (MeasureTheory.Measure.count : MeasureTheory.Measure ℕ) hpq
      (measurable_of_countable (fun n : ℕ => if Pm n then φ n else 0)).aemeasurable
      (measurable_of_countable (fun n : ℕ => if Pm n then ψ n else 0)).aemeasurable
    simpa [MeasureTheory.lintegral_count, Pi.mul_apply] using h
  have hsq : ∀ n : ℕ, (if Pm n then φ n else 0) ^ (2 : ℝ) = if Pm n then φ n ^ 2 else 0 := by
    intro n; by_cases h : Pm n <;> simp [h]
  have hsq' : ∀ n : ℕ, (if Pm n then ψ n else 0) ^ (2 : ℝ) = if Pm n then ψ n ^ 2 else 0 := by
    intro n; by_cases h : Pm n <;> simp [h]
  -- The finite-square hypotheses bound the series of squares.
  have hA2 : (∑' n : ℕ, (if Pm n then φ n else 0) ^ (2 : ℝ)) ≤ Bφ ^ 2 * u ^ 2 := by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    simp only [hsq]
    rw [← Finset.sum_filter]
    exact hφ (s.filter Pm) (fun n hn => (Finset.mem_filter.mp hn).2)
  have hB2 : (∑' n : ℕ, (if Pm n then ψ n else 0) ^ (2 : ℝ)) ≤ Bψ ^ 2 * v ^ 2 := by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    simp only [hsq']
    rw [← Finset.sum_filter]
    exact hψ (s.filter Pm) (fun n hn => (Finset.mem_filter.mp hn).2)
  -- The square root of a square is the base.
  have hsqrt_sq : ∀ x : ENNReal, (x ^ 2) ^ (1 / 2 : ℝ) = x := by
    intro x
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hA' : (∑' n : ℕ, (if Pm n then φ n else 0) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤ Bφ * u := by
    have h := ENNReal.rpow_le_rpow hA2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rwa [← mul_pow, hsqrt_sq] at h
  have hB' : (∑' n : ℕ, (if Pm n then ψ n else 0) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤ Bψ * v := by
    have h := ENNReal.rpow_le_rpow hB2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rwa [← mul_pow, hsqrt_sq] at h
  have hsplit : (fun n : ℕ => if Pm n then φ n * ψ n else 0)
      = fun n => (if Pm n then φ n else 0) * (if Pm n then ψ n else 0) := by
    funext n; by_cases h : Pm n <;> simp [h]
  rw [hsplit]
  calc (∑' n : ℕ, (if Pm n then φ n else 0) * (if Pm n then ψ n else 0))
      ≤ (∑' n : ℕ, (if Pm n then φ n else 0) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
        * (∑' n : ℕ, (if Pm n then ψ n else 0) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := key
    _ ≤ (Bφ * u) * (Bψ * v) := mul_le_mul' hA' hB'
    _ = Bφ * Bψ * u * v := by ac_rfl

end Work.KMTPlan.A6
