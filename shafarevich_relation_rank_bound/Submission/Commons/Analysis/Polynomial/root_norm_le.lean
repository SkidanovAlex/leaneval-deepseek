import Mathlib.Analysis.Polynomial.Norm
import Submission.Commons.Analysis.Polynomial.geom_sum_range_le
import Submission.Commons.Analysis.Polynomial.norm_smul_eq_of_norm_algebraMap

namespace Commons.Analysis.Polynomial

open Finset

lemma root_norm_le {K L : Type*} [NormedField K] [NormedField L] [Algebra K L]
    (h_ext : ∀ k : K, ‖algebraMap K L k‖ = ‖k‖)
    (f : Polynomial K) (hd : 1 ≤ f.natDegree) {α : L} (hα : Polynomial.aeval α f = 0) :
    ‖α‖ ≤ max 1 ((f.natDegree : ℝ) * f.supNorm / ‖f.coeff f.natDegree‖) := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [Polynomial.natDegree_zero] at hd
    omega
  set n := f.natDegree with hn
  have hcpos : 0 < ‖f.coeff n‖ := by
    rw [hn, Polynomial.coeff_natDegree]
    exact norm_pos_iff.mpr ((Polynomial.leadingCoeff_ne_zero).mpr hf0)
  -- expand `aeval α f = 0` as a finite sum
  have hsum : ∑ i ∈ range (n + 1), f.coeff i • α ^ i = 0 := by
    rw [hn, ← Polynomial.aeval_eq_sum_range (x := α), hα]
  -- isolate the top-degree term
  have htop : f.coeff n • α ^ n = - ∑ i ∈ range n, f.coeff i • α ^ i := by
    have h := hsum
    rw [sum_range_succ] at h
    exact eq_neg_of_add_eq_zero_right h
  have hnorm_g : ∀ i : ℕ, ‖f.coeff i • α ^ i‖ = ‖f.coeff i‖ * ‖α‖ ^ i := by
    intro i
    rw [norm_smul_eq_of_norm_algebraMap h_ext, norm_pow]
  -- triangle inequality + supNorm bound
  have hlower : ‖f.coeff n • α ^ n‖ ≤ f.supNorm * ∑ i ∈ range n, ‖α‖ ^ i := by
    rw [htop, norm_neg]
    calc ‖∑ i ∈ range n, f.coeff i • α ^ i‖
        ≤ ∑ i ∈ range n, ‖f.coeff i • α ^ i‖ := norm_sum_le _ _
      _ = ∑ i ∈ range n, ‖f.coeff i‖ * ‖α‖ ^ i := by
            apply sum_congr rfl; intro i _; rw [hnorm_g i]
      _ ≤ ∑ i ∈ range n, f.supNorm * ‖α‖ ^ i := by
            apply sum_le_sum; intro i _
            exact mul_le_mul_of_nonneg_right (Polynomial.le_supNorm f i) (by positivity)
      _ = f.supNorm * ∑ i ∈ range n, ‖α‖ ^ i := by rw [mul_sum]
  have hmain : ‖f.coeff n‖ * ‖α‖ ^ n ≤ f.supNorm * ∑ i ∈ range n, ‖α‖ ^ i := by
    have h := hlower
    rw [hnorm_g n] at h
    exact h
  rw [le_max_iff]
  by_cases hx : ‖α‖ ≤ 1
  · exact Or.inl hx
  · refine Or.inr ?_
    have hx1 : 1 ≤ ‖α‖ := le_of_lt (not_le.mp hx)
    have hαpos : 0 < ‖α‖ := lt_trans one_pos (not_le.mp hx)
    have hppos : 0 < ‖α‖ ^ (n - 1) := pow_pos hαpos _
    have hgeo : ∑ i ∈ range n, ‖α‖ ^ i ≤ (n : ℝ) * ‖α‖ ^ (n - 1) :=
      geom_sum_range_le hx1 n
    have hmain2 : ‖f.coeff n‖ * ‖α‖ ^ n ≤ f.supNorm * ((n : ℝ) * ‖α‖ ^ (n - 1)) := by
      calc ‖f.coeff n‖ * ‖α‖ ^ n ≤ f.supNorm * ∑ i ∈ range n, ‖α‖ ^ i := hmain
        _ ≤ f.supNorm * ((n : ℝ) * ‖α‖ ^ (n - 1)) :=
              mul_le_mul_of_nonneg_left hgeo (Polynomial.supNorm_nonneg f)
    have hpow : ‖α‖ ^ n = ‖α‖ ^ (n - 1) * ‖α‖ := by
      conv_lhs => rw [← Nat.sub_add_cancel hd]
      rw [pow_succ]
    have hkey : ‖f.coeff n‖ * ‖α‖ ≤ f.supNorm * (n : ℝ) := by
      have hmul := hmain2
      rw [hpow] at hmul
      have hmul' : (‖f.coeff n‖ * ‖α‖) * ‖α‖ ^ (n - 1) ≤
          (f.supNorm * (n : ℝ)) * ‖α‖ ^ (n - 1) := by
        calc (‖f.coeff n‖ * ‖α‖) * ‖α‖ ^ (n - 1)
            = ‖f.coeff n‖ * (‖α‖ ^ (n - 1) * ‖α‖) := by ring
          _ ≤ f.supNorm * ((n : ℝ) * ‖α‖ ^ (n - 1)) := hmul
          _ = (f.supNorm * (n : ℝ)) * ‖α‖ ^ (n - 1) := by ring
      exact le_of_mul_le_mul_right hmul' hppos
    have hfin : ‖α‖ ≤ (f.supNorm * (n : ℝ)) / ‖f.coeff n‖ := by
      rw [le_div_iff₀ hcpos]
      simpa [mul_comm] using hkey
    calc ‖α‖ ≤ (f.supNorm * (n : ℝ)) / ‖f.coeff n‖ := hfin
      _ = (n : ℝ) * f.supNorm / ‖f.coeff n‖ := by ring

end Commons.Analysis.Polynomial