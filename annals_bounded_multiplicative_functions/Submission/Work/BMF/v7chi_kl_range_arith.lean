import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- The logarithmic-range term of the Kusmin–Landau block sum is uniformly bounded. -/
lemma v7chi_kl_range_arith : ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, 3 ≤ |t| →
    (Real.log (((Nat.ceil |t| * Nat.ceil |t| + 1 : ℕ) : ℝ)) / Real.log 2 + 2) *
      (24 * Real.pi * ((Nat.ceil |t| * Nat.ceil |t| + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ) / |t|) ≤ A := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2r : (0:ℝ) < (2:ℝ)^(1/3:ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have h3r : (0:ℝ) < 9 / Real.log 2 + 2 := by
    have : (0:ℝ) < 9 / Real.log 2 := div_pos (by norm_num) hlog2
    linarith
  refine ⟨36 * Real.pi * (2:ℝ) ^ (1/3:ℝ) * (9 / Real.log 2 + 2),
    mul_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) h2r) h3r, ?_⟩
  intro t ht
  set s : ℝ := |t| with hs
  set n : ℕ := Nat.ceil s with hn
  set c : ℝ := ((n * n + 1 : ℕ) : ℝ) with hc
  have hs3 : 3 ≤ s := by rw [hs]; exact ht
  have hspos : 0 < s := by linarith
  have hnR : (3:ℝ) ≤ (n:ℝ) := by
    have h := Nat.le_ceil s
    rw [← hn] at h
    linarith
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith
  have hs_gt : (n:ℝ) - 1 < s := by
    have h := Nat.ceil_lt_add_one (show (0:ℝ) ≤ s by linarith)
    rw [← hn] at h
    linarith
  have hnm1_pos : (0:ℝ) < (n:ℝ) - 1 := by linarith
  have hnm1_le : (n:ℝ) - 1 ≤ s := le_of_lt hs_gt
  have hc_pos : 0 < c := by rw [hc]; push_cast; positivity
  have hc_nonneg : 0 ≤ c := le_of_lt hc_pos
  -- Bound on the logarithmic factor:  log c / log 2 + 2 ≤ (9/log 2 + 2) * n^{1/3}.
  have hA_log : Real.log c ≤ 9 * (n:ℝ)^(1/3:ℝ) := by
    rw [hc]
    have hcl : ((n*n+1 : ℕ) : ℝ) ≤ (n:ℝ)^3 := by push_cast; nlinarith [hnR]
    have hlog_c : Real.log ((n*n+1 : ℕ) : ℝ) ≤ Real.log ((n:ℝ)^3) :=
      Real.log_le_log (by push_cast; positivity) hcl
    have hlog_pow : Real.log ((n:ℝ)^3) = 3 * Real.log (n:ℝ) := by rw [Real.log_pow]; norm_num
    have hn3b : Real.log (n:ℝ) ≤ 3 * (n:ℝ)^(1/3:ℝ) := by
      have hu : 0 < (n:ℝ)^(1/3:ℝ) := Real.rpow_pos_of_pos hnpos _
      have h1 : Real.log (n:ℝ) = 3 * Real.log ((n:ℝ)^(1/3:ℝ)) := by
        have := Real.log_rpow hnpos (1/3:ℝ); linarith
      have h2 : Real.log ((n:ℝ)^(1/3:ℝ)) ≤ (n:ℝ)^(1/3:ℝ) - 1 := Real.log_le_sub_one_of_pos hu
      linarith
    calc Real.log ((n*n+1 : ℕ) : ℝ) ≤ Real.log ((n:ℝ)^3) := hlog_c
      _ = 3 * Real.log (n:ℝ) := hlog_pow
      _ ≤ 3 * (3 * (n:ℝ)^(1/3:ℝ)) := by linarith
      _ = 9 * (n:ℝ)^(1/3:ℝ) := by ring
  have hB : Real.log c / Real.log 2 + 2 ≤ (9 / Real.log 2 + 2) * (n:ℝ)^(1/3:ℝ) := by
    have hnR1 : (1:ℝ) ≤ (n:ℝ) := by linarith
    have hroot1 : (1:ℝ) ≤ (n:ℝ)^(1/3:ℝ) := by
      have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hnR1 (by norm_num : (0:ℝ) ≤ (1/3:ℝ))
      rwa [Real.one_rpow] at h
    have step1 : Real.log c / Real.log 2 ≤ (9 * (n:ℝ)^(1/3:ℝ)) / Real.log 2 :=
      div_le_div_of_nonneg_right hA_log (le_of_lt hlog2)
    have step2 : (2:ℝ) ≤ 2 * (n:ℝ)^(1/3:ℝ) := by linarith
    calc Real.log c / Real.log 2 + 2 ≤ (9 * (n:ℝ)^(1/3:ℝ)) / Real.log 2 + 2 * (n:ℝ)^(1/3:ℝ) :=
          add_le_add step1 step2
      _ = (9 / Real.log 2 + 2) * (n:ℝ)^(1/3:ℝ) := by ring
  -- Bound on the power factor:  c^{1/3} ≤ 2^{1/3} * n^{2/3}.
  have hC : c^(1/3:ℝ) ≤ (2:ℝ)^(1/3:ℝ) * (n:ℝ)^(2/3:ℝ) := by
    rw [hc]
    have h1 : (1:ℝ) ≤ (n:ℝ) := by linarith
    have h2 : (1:ℝ) ≤ (n:ℝ)*(n:ℝ) := by
      have := mul_le_mul h1 h1 (by norm_num : (0:ℝ) ≤ 1) (by linarith : (0:ℝ) ≤ (n:ℝ))
      simpa using this
    have hc_le : ((n*n+1 : ℕ) : ℝ) ≤ 2 * (n:ℝ)^2 := by push_cast; nlinarith [h2, sq_nonneg ((n:ℝ))]
    have hc_nonneg' : (0:ℝ) ≤ ((n*n+1 : ℕ) : ℝ) := by push_cast; positivity
    have step1 : ((n*n+1 : ℕ) : ℝ)^(1/3:ℝ) ≤ (2 * (n:ℝ)^2)^(1/3:ℝ) :=
      Real.rpow_le_rpow hc_nonneg' hc_le (by norm_num)
    have step3 : ((n:ℝ)^2)^(1/3:ℝ) = (n:ℝ)^(2/3:ℝ) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (le_of_lt hnpos)]
      norm_num
    calc ((n*n+1 : ℕ) : ℝ)^(1/3:ℝ) ≤ (2 * (n:ℝ)^2)^(1/3:ℝ) := step1
      _ = (2:ℝ)^(1/3:ℝ) * ((n:ℝ)^2)^(1/3:ℝ) := Real.mul_rpow (by norm_num) (sq_nonneg _)
      _ = (2:ℝ)^(1/3:ℝ) * (n:ℝ)^(2/3:ℝ) := by rw [step3]
  have hD_pos : (0:ℝ) < (2:ℝ)^(1/3:ℝ) * (n:ℝ)^(2/3:ℝ) :=
    mul_pos h2r (Real.rpow_pos_of_pos hnpos _)
  have hP : 24 * Real.pi * c^(1/3:ℝ) / s ≤
      24 * Real.pi * ((2:ℝ)^(1/3:ℝ) * (n:ℝ)^(2/3:ℝ)) / ((n:ℝ)-1) := by
    have h2 : c^(1/3:ℝ) / s ≤ ((2:ℝ)^(1/3:ℝ) * (n:ℝ)^(2/3:ℝ)) / s :=
      div_le_div_of_nonneg_right hC (le_of_lt hspos)
    have h3 : ((2:ℝ)^(1/3:ℝ) * (n:ℝ)^(2/3:ℝ)) / s ≤
        ((2:ℝ)^(1/3:ℝ) * (n:ℝ)^(2/3:ℝ)) / ((n:ℝ)-1) := by
      have hinv : (1:ℝ)/s ≤ 1/((n:ℝ)-1) := one_div_le_one_div_of_le hnm1_pos hnm1_le
      have hh := mul_le_mul_of_nonneg_left hinv (le_of_lt hD_pos)
      have e1 : ((2:ℝ)^(1/3:ℝ) * (n:ℝ)^(2/3:ℝ)) / s =
          ((2:ℝ)^(1/3:ℝ) * (n:ℝ)^(2/3:ℝ)) * (1/s) := div_eq_mul_one_div _ _
      have e2 : ((2:ℝ)^(1/3:ℝ) * (n:ℝ)^(2/3:ℝ)) / ((n:ℝ)-1) =
          ((2:ℝ)^(1/3:ℝ) * (n:ℝ)^(2/3:ℝ)) * (1/((n:ℝ)-1)) := div_eq_mul_one_div _ _
      rw [e1, e2]
      exact hh
    calc 24 * Real.pi * c^(1/3:ℝ) / s = 24 * Real.pi * (c^(1/3:ℝ) / s) := by ring
      _ ≤ 24 * Real.pi * (((2:ℝ)^(1/3:ℝ) * (n:ℝ)^(2/3:ℝ)) / ((n:ℝ)-1)) :=
            mul_le_mul_of_nonneg_left (le_trans h2 h3) (by positivity)
      _ = 24 * Real.pi * ((2:ℝ)^(1/3:ℝ) * (n:ℝ)^(2/3:ℝ)) / ((n:ℝ)-1) := by ring
  have hP_nonneg : (0:ℝ) ≤ 24 * Real.pi * c^(1/3:ℝ) / s :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt Real.pi_pos))
      (Real.rpow_nonneg hc_nonneg _)) (le_of_lt hspos)
  have hB1_nonneg : (0:ℝ) ≤ (9 / Real.log 2 + 2) * (n:ℝ)^(1/3:ℝ) :=
    mul_nonneg (le_of_lt h3r) (Real.rpow_nonneg (le_of_lt hnpos) _)
  have hBE : (9 / Real.log 2 + 2) * (n:ℝ)^(1/3:ℝ) *
      (24 * Real.pi * ((2:ℝ)^(1/3:ℝ) * (n:ℝ)^(2/3:ℝ)) / ((n:ℝ)-1)) ≤
      36 * Real.pi * (2:ℝ)^(1/3:ℝ) * (9 / Real.log 2 + 2) := by
    have hroot : (n:ℝ)^(1/3:ℝ) * (n:ℝ)^(2/3:ℝ) = (n:ℝ) := by
      rw [← Real.rpow_add hnpos, show (1:ℝ)/3 + 2/3 = 1 by norm_num, Real.rpow_one]
    have hratio : (n:ℝ) / ((n:ℝ)-1) ≤ 3/2 := by
      rw [div_le_iff₀ hnm1_pos]
      nlinarith [hnR]
    have hK : (0:ℝ) ≤ 24 * Real.pi * (2:ℝ)^(1/3:ℝ) * (9/Real.log 2 + 2) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt Real.pi_pos)) (le_of_lt h2r)) (le_of_lt h3r)
    calc (9 / Real.log 2 + 2) * (n:ℝ)^(1/3:ℝ) *
          (24 * Real.pi * ((2:ℝ)^(1/3:ℝ) * (n:ℝ)^(2/3:ℝ)) / ((n:ℝ)-1))
        = 24 * Real.pi * (2:ℝ)^(1/3:ℝ) * (9/Real.log 2 + 2) *
            ((n:ℝ)^(1/3:ℝ) * (n:ℝ)^(2/3:ℝ) / ((n:ℝ)-1)) := by ring
      _ = 24 * Real.pi * (2:ℝ)^(1/3:ℝ) * (9/Real.log 2 + 2) * ((n:ℝ) / ((n:ℝ)-1)) := by rw [hroot]
      _ ≤ 24 * Real.pi * (2:ℝ)^(1/3:ℝ) * (9/Real.log 2 + 2) * (3/2) :=
            mul_le_mul_of_nonneg_left hratio hK
      _ = 36 * Real.pi * (2:ℝ)^(1/3:ℝ) * (9 / Real.log 2 + 2) := by ring
  exact le_trans (mul_le_mul hB hP hP_nonneg hB1_nonneg) hBE

end Work.BMF
