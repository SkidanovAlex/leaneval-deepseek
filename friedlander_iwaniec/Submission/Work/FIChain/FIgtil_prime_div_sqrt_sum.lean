import Mathlib
import Submission.Work.FIChain.S3plusC_route_defs

namespace Work.FIChain

/-- For a prime `p`, `p · √p = p^{3/2}`. -/
private lemma prime_mul_sqrt_eq_rpow {p : ℕ} (hp : p.Prime) :
    (p : ℝ) * Real.sqrt (p : ℝ) = (p : ℝ) ^ ((3 : ℝ) / 2) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have h1 : (p : ℝ) ^ (1 : ℝ) * (p : ℝ) ^ ((1 : ℝ) / 2)
      = (p : ℝ) ^ ((1 : ℝ) + 1 / 2) := (Real.rpow_add hp0 1 (1 / 2)).symm
  have h2 : (p : ℝ) ^ (1 : ℝ) = (p : ℝ) := Real.rpow_one _
  have h3 : ((1 : ℝ) + 1 / 2) = (3 : ℝ) / 2 := by norm_num
  calc (p : ℝ) * Real.sqrt (p : ℝ)
      = (p : ℝ) * (p : ℝ) ^ ((1 : ℝ) / 2) := by rw [Real.sqrt_eq_rpow]
    _ = (p : ℝ) ^ (1 : ℝ) * (p : ℝ) ^ ((1 : ℝ) / 2) := by rw [h2]
    _ = (p : ℝ) ^ ((1 : ℝ) + 1 / 2) := h1
    _ = (p : ℝ) ^ ((3 : ℝ) / 2) := by rw [h3]

theorem FIgtil_prime_div_sqrt_sum :
    ∃ K : ℝ, ∀ D : ℕ,
      (∑ p ∈ (Finset.Icc 1 D).filter Nat.Prime,
          Submission.ASP.FIgtil p / Real.sqrt (p : ℝ)) ≤ K := by
  obtain ⟨C, hCpos, hC⟩ := Submission.ASP.FIgtil_bound
  refine ⟨C * ∑' n : ℕ, ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹, fun D => ?_⟩
  have hSummable : Summable (fun n : ℕ => ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  calc (∑ p ∈ (Finset.Icc 1 D).filter Nat.Prime,
          Submission.ASP.FIgtil p / Real.sqrt (p : ℝ))
      ≤ ∑ p ∈ (Finset.Icc 1 D).filter Nat.Prime,
          C * ((p : ℝ) ^ ((3 : ℝ) / 2))⁻¹ := by
        apply Finset.sum_le_sum
        intro p hp
        rw [Finset.mem_filter] at hp
        have hterm : Submission.ASP.FIgtil p / Real.sqrt (p : ℝ)
            ≤ (C / (p : ℝ)) / Real.sqrt (p : ℝ) :=
          div_le_div_of_nonneg_right (hC p hp.2) (Real.sqrt_nonneg _)
        have heq : (C / (p : ℝ)) / Real.sqrt (p : ℝ)
            = C * ((p : ℝ) ^ ((3 : ℝ) / 2))⁻¹ := by
          rw [div_div, prime_mul_sqrt_eq_rpow hp.2, div_eq_mul_inv]
        exact hterm.trans_eq heq
    _ = C * ∑ p ∈ (Finset.Icc 1 D).filter Nat.Prime,
          ((p : ℝ) ^ ((3 : ℝ) / 2))⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ C * ∑' n : ℕ, ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹ :=
        mul_le_mul_of_nonneg_left
          (hSummable.sum_le_tsum _
            (fun i _ => inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg i) _)))
          hCpos.le

end Work.FIChain
