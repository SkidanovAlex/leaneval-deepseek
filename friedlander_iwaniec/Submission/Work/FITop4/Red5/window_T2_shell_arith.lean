import Mathlib

set_option linter.unusedVariables false

namespace Work.FITop4.Red5

/-- The elementary arithmetic inequality underlying the `T2` shell bound.

Writing `M = Mn`, `N` for the two scales and `P = (M N)^{3/4}`, the two terms on the
left are bounded by `2θP`, `θP` and `2θP` respectively, using
`1 ≤ θM` (which follows from `2N ≤ θ²M`, `N ≥ 1`, `θ ≤ 1/4`) and `N ≤ θ²M`
(which gives `√N ≤ θ√M`). -/
theorem window_T2_shell_arith (Mn N : ℕ) (θ : ℝ)
    (hMn : 1 ≤ Mn) (hN : 1 ≤ N) (hθ0 : 0 < θ) (hθ14 : θ ≤ 1 / 4)
    (hθsq : 1 ≤ θ * (N : ℝ) ^ ((1 : ℝ) / 2))
    (h2N : 2 * (N : ℝ) ≤ θ ^ (2 : ℕ) * (Mn : ℝ)) :
    (2 * θ * (Mn : ℝ) + 1) * (Mn : ℝ) ^ (-(1 : ℝ) / 4) * (N : ℝ) ^ ((3 : ℝ) / 4)
      + (2 * (Mn : ℝ)) ^ ((1 : ℝ) / 4) * (N : ℝ) ^ ((5 : ℝ) / 4)
      ≤ 10 * θ * ((Mn : ℝ) * (N : ℝ)) ^ ((3 : ℝ) / 4) := by
  set M : ℝ := (Mn : ℝ) with hMdef
  set K : ℝ := (N : ℝ) with hKdef
  have hM1 : (1:ℝ) ≤ M := by rw [hMdef]; exact_mod_cast hMn
  have hK1 : (1:ℝ) ≤ K := by rw [hKdef]; exact_mod_cast hN
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  -- `θ²M ≥ 2` and hence `θM ≥ 8 ≥ 1`
  have h2 : (2:ℝ) ≤ θ^2 * M := by nlinarith [h2N, hK1]
  have hθM1 : (1:ℝ) ≤ θ*M := by
    have ha : 2/θ ≤ θ*M := by rw [div_le_iff₀ hθ0]; nlinarith [h2]
    have hb : (8:ℝ) ≤ 2/θ := by rw [le_div_iff₀ hθ0]; nlinarith [hθ14]
    linarith
  have hKM : K ≤ θ^2 * M := by nlinarith [h2N, hK0.le]
  -- rpow rewriting helpers
  have hM34 : M^((3:ℝ)/4) = M * M^(-(1:ℝ)/4) := by
    have h := Real.rpow_add hM0 (1:ℝ) (-(1:ℝ)/4)
    rw [show (1:ℝ) + (-(1:ℝ)/4) = (3:ℝ)/4 by norm_num, Real.rpow_one] at h
    exact h
  have hP : (M*K)^((3:ℝ)/4) = M^((3:ℝ)/4) * K^((3:ℝ)/4) :=
    Real.mul_rpow hM0.le hK0.le
  have hK34nn : 0 ≤ K^((3:ℝ)/4) := Real.rpow_nonneg hK0.le _
  -- `M^{-1/4} ≤ θ M^{3/4}` from `1 ≤ θM`
  have hMq_le : M^(-(1:ℝ)/4) ≤ θ * M^((3:ℝ)/4) := by
    have hq1 : 0 < M^((1:ℝ)/4) := Real.rpow_pos_of_pos hM0 _
    apply (mul_le_mul_iff_of_pos_right hq1).mp
    have e1 : M^(-(1:ℝ)/4)*M^((1:ℝ)/4) = 1 := by
      rw [← Real.rpow_add hM0, show (-(1:ℝ)/4) + (1:ℝ)/4 = 0 by norm_num, Real.rpow_zero]
    have e2 : (θ*M^((3:ℝ)/4))*M^((1:ℝ)/4) = θ*M := by
      rw [mul_assoc, ← Real.rpow_add hM0, show (3:ℝ)/4 + (1:ℝ)/4 = 1 by norm_num, Real.rpow_one]
    rw [e1, e2]; exact hθM1
  -- term 1, split off the `2θM·M^{-1/4}N^{3/4} = 2θP` part
  have hT1 : (2*θ*M+1)*M^(-(1:ℝ)/4)*K^((3:ℝ)/4)
      = 2*θ*((M*K)^((3:ℝ)/4)) + M^(-(1:ℝ)/4)*K^((3:ℝ)/4) := by
    rw [hP, hM34]; ring
  have hT1b : M^(-(1:ℝ)/4)*K^((3:ℝ)/4) ≤ θ*((M*K)^((3:ℝ)/4)) := by
    have h := mul_le_mul_of_nonneg_right hMq_le hK34nn
    calc M^(-(1:ℝ)/4)*K^((3:ℝ)/4) ≤ (θ*M^((3:ℝ)/4))*K^((3:ℝ)/4) := h
      _ = θ*((M*K)^((3:ℝ)/4)) := by rw [hP]; ring
  -- term 2
  have h2pow : (2:ℝ)^((1:ℝ)/4) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 2 by norm_num) (show (1:ℝ)/4 ≤ 1 by norm_num)
    rwa [Real.rpow_one] at h
  have h2M4 : (2*M)^((1:ℝ)/4) ≤ 2*M^((1:ℝ)/4) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hM0.le]
    calc (2:ℝ)^((1:ℝ)/4)*M^((1:ℝ)/4) = M^((1:ℝ)/4)*2^((1:ℝ)/4) := by ring
      _ ≤ M^((1:ℝ)/4)*2 := mul_le_mul_of_nonneg_left h2pow (Real.rpow_nonneg hM0.le _)
      _ = 2*M^((1:ℝ)/4) := by ring
  -- `√K ≤ θ√M`
  have hsqrtK : K^((1:ℝ)/2) ≤ θ*M^((1:ℝ)/2) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    calc Real.sqrt K ≤ Real.sqrt (θ^2*M) := Real.sqrt_le_sqrt hKM
      _ = θ*Real.sqrt M := by rw [Real.sqrt_mul (sq_nonneg θ), Real.sqrt_sq hθ0.le]
  have hM12 : M^((1:ℝ)/2)*M^((1:ℝ)/4) = M^((3:ℝ)/4) := by
    rw [← Real.rpow_add hM0, show (1:ℝ)/2+(1:ℝ)/4 = (3:ℝ)/4 by norm_num]
  have hK12 : K^((1:ℝ)/2)*K^((3:ℝ)/4) = K^((5:ℝ)/4) := by
    rw [← Real.rpow_add hK0, show (1:ℝ)/2+(3:ℝ)/4 = (5:ℝ)/4 by norm_num]
  have hT2step : M^((1:ℝ)/4)*K^((5:ℝ)/4) ≤ θ*((M*K)^((3:ℝ)/4)) := by
    have hM14nn : 0 ≤ M^((1:ℝ)/4) := Real.rpow_nonneg hM0.le _
    have h := mul_le_mul_of_nonneg_right hsqrtK (mul_nonneg hM14nn hK34nn)
    calc M^((1:ℝ)/4)*K^((5:ℝ)/4) = K^((1:ℝ)/2)*(M^((1:ℝ)/4)*K^((3:ℝ)/4)) := by
          rw [← hK12]; ring
      _ ≤ (θ*M^((1:ℝ)/2))*(M^((1:ℝ)/4)*K^((3:ℝ)/4)) := h
      _ = θ*((M*K)^((3:ℝ)/4)) := by rw [hP, ← hM12]; ring
  have hT2 : (2*M)^((1:ℝ)/4)*K^((5:ℝ)/4) ≤ 2*θ*((M*K)^((3:ℝ)/4)) := by
    have hK54nn : 0 ≤ K^((5:ℝ)/4) := Real.rpow_nonneg hK0.le _
    calc (2*M)^((1:ℝ)/4)*K^((5:ℝ)/4) ≤ (2*M^((1:ℝ)/4))*K^((5:ℝ)/4) :=
          mul_le_mul_of_nonneg_right h2M4 hK54nn
      _ = 2*(M^((1:ℝ)/4)*K^((5:ℝ)/4)) := by ring
      _ ≤ 2*(θ*((M*K)^((3:ℝ)/4))) := mul_le_mul_of_nonneg_left hT2step (by norm_num)
      _ = 2*θ*((M*K)^((3:ℝ)/4)) := by ring
  -- combine
  have hPnn : 0 ≤ (M*K)^((3:ℝ)/4) := Real.rpow_nonneg (mul_nonneg hM0.le hK0.le) _
  have h5 : 5*θ*((M*K)^((3:ℝ)/4)) ≤ 10*θ*((M*K)^((3:ℝ)/4)) := by
    have hh : (5:ℝ)*θ ≤ 10*θ := by linarith
    calc 5*θ*((M*K)^((3:ℝ)/4)) = (5*θ)*((M*K)^((3:ℝ)/4)) := by ring
      _ ≤ (10*θ)*((M*K)^((3:ℝ)/4)) := mul_le_mul_of_nonneg_right hh hPnn
      _ = 10*θ*((M*K)^((3:ℝ)/4)) := by ring
  calc (2*θ*M+1)*M^(-(1:ℝ)/4)*K^((3:ℝ)/4) + (2*M)^((1:ℝ)/4)*K^((5:ℝ)/4)
      = (2*θ*((M*K)^((3:ℝ)/4)) + M^(-(1:ℝ)/4)*K^((3:ℝ)/4)) + (2*M)^((1:ℝ)/4)*K^((5:ℝ)/4) := by
        rw [hT1]
    _ ≤ (2*θ*((M*K)^((3:ℝ)/4)) + θ*((M*K)^((3:ℝ)/4))) + 2*θ*((M*K)^((3:ℝ)/4)) :=
        add_le_add (add_le_add (le_refl _) hT1b) hT2
    _ = 5*θ*((M*K)^((3:ℝ)/4)) := by ring
    _ ≤ 10*θ*((M*K)^((3:ℝ)/4)) := h5

end Work.FITop4.Red5
