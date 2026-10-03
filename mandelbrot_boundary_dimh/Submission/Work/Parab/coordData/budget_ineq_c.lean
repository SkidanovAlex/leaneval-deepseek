import Mathlib

namespace Work.Parab.coordData

/-- Explicit constants for `budget_ineq_c`.

`M` is the threshold `max N (2R+1) + 5` and `T` is a level dominating all the
quantities that the running variable `D ≥ c/2` has to beat.  Everything is kept
opaque on purpose: the local definitions would otherwise be unfolded by
`linarith` in the main proof. -/
private lemma budget_const {K C N R : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hN : 0 ≤ N) :
    ∃ c M T : ℝ,
      0 < c ∧ 2 ≤ c ∧ 2 * (N + 1) ≤ c ∧ 10 * (K * C) ≤ c ∧ 20 * (K * C) ≤ c ∧
      20 * K ≤ c ∧ 5 ≤ M ∧ M = max N (2 * R + 1) + 5 ∧
      20 * K ≤ T ∧ 10 * (K * C) * (1 + Real.log 5) ≤ T ∧
      10 * (K * C) * Real.log M ≤ T ∧ 400 * (K * C) ^ 2 ≤ T ∧ c / 2 = T + 1 := by
  set M := max N (2 * R + 1) + 5 with hM
  have hM5 : 5 ≤ M := by
    rw [hM]
    have h : (0:ℝ) ≤ max N (2*R+1) := le_max_of_le_left hN
    linarith
  have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg (by linarith)
  set T := 1 + (N + 1) + 20 * K + 10 * (K * C) + 10 * (K * C) * (1 + Real.log 5)
      + 10 * (K * C) * Real.log M + 400 * (K * C) ^ 2 with hT
  have t1 : (0:ℝ) ≤ 10 * (K*C) * Real.log M := by positivity
  have t2 : (0:ℝ) ≤ 10 * (K*C) * (1 + Real.log 5) := by positivity
  have t3 : (0:ℝ) ≤ 400 * (K*C) ^ 2 := by positivity
  have t4 : (0:ℝ) ≤ 10 * (K*C) := by positivity
  have t5 : (0:ℝ) ≤ 20 * K := by linarith
  have t6 : (0:ℝ) ≤ N + 1 := by linarith
  have hTpos : 0 < T := by rw [hT]; nlinarith [t1, t2, t3, t4, t5, t6]
  have hT_N : N + 1 ≤ T := by rw [hT]; nlinarith [t1, t2, t3, t4, t5]
  have hT_20K : 20*K ≤ T := by rw [hT]; nlinarith [t1, t2, t3, t4, t6]
  have hT_10KC : 10*(K*C) ≤ T := by rw [hT]; nlinarith [t1, t2, t3, t5, t6]
  have hT_10KC1 : 10*(K*C)*(1+Real.log 5) ≤ T := by rw [hT]; nlinarith [t1, t3, t4, t5, t6]
  have hT_10KClogM : 10*(K*C)*Real.log M ≤ T := by rw [hT]; nlinarith [t2, t3, t4, t5, t6]
  have hT_400 : 400*(K*C)^2 ≤ T := by rw [hT]; nlinarith [t1, t2, t4, t5, t6]
  refine ⟨2*T+2, M, T, ?_, ?_, ?_, ?_, ?_, ?_, hM5, hM, hT_20K, hT_10KC1,
    hT_10KClogM, hT_400, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · rw [show (2*T+2)/2 = T+1 from by ring, hT]

theorem budget_ineq_c {K C N R : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hN : 0 ≤ N) (hR : 0 ≤ R) :
    ∃ c : ℝ, 2 ≤ c ∧ 2 * (N + 1) ≤ c ∧ 10 * (K * C) ≤ c ∧
      ∀ (S x k D : ℝ), 1 ≤ S → D = c / 2 * S → 0 ≤ k → Real.log (2 + |x|) ≤ S →
        k ≤ max N (2 * R + 1) + 3 + |x| + D →
        K * (C * (1 + Real.log (2 + |x| + k + D)) + 4 * D / c + 4) ≤ D := by
  obtain ⟨c, M, T, hcpos, hc2, hcN, hcKC, hc20KC, hc20K, hM5, hMdef,
    hT20K, hT10A1, hT10AlogM, hT400A2, hcT⟩ := budget_const hK hC hN
  refine ⟨c, hc2, hcN, hcKC, ?_⟩
  intro S x k D hS hD hk0 hlog hkbd
  have hA0 : 0 ≤ K * C := mul_nonneg hK hC
  have hM0 : (0:ℝ) < M := by linarith
  -- basic bounds on D
  have hDge : c/2 ≤ D := by rw [hD]; nlinarith [hS, hcpos]
  have hDge' : T + 1 ≤ D := by linarith
  have hDpos : 0 < D := by linarith
  have hD0 : 0 ≤ D := le_of_lt hDpos
  have hD1 : 1 ≤ D := by linarith
  have hD_20K : 20*K ≤ D := by linarith
  have hD_10A1 : 10*(K*C)*(1+Real.log 5) ≤ D := by linarith
  have hD_10AlogM : 10*(K*C)*Real.log M ≤ D := by linarith
  have hD_400A2 : 400*(K*C)^2 ≤ D := by linarith
  -- express S as 2D/c
  have hS_eq : S = 2*D/c := by
    have h2 : 2*D = c*S := by rw [hD]; ring
    rw [eq_div_iff (ne_of_gt hcpos)]
    linarith
  have hlog2x : Real.log (2 + |x|) ≤ 2*D/c := by rw [hS_eq] at hlog; exact hlog
  have h2xpos : 0 < 2 + |x| := by positivity
  have hEx : 2 + |x| ≤ Real.exp (2*D/c) := by
    rw [← Real.exp_log h2xpos]
    exact Real.exp_le_exp.mpr hlog2x
  have hxle : |x| ≤ Real.exp (2*D/c) - 2 := by linarith
  have hM2 : M - 2 = max N (2*R+1) + 3 := by rw [hMdef]; ring
  have hk' : k ≤ M - 2 + |x| + D := by linarith
  have hL_le : 2 + |x| + k + D ≤ M + 2*Real.exp (2*D/c) + 2*D := by linarith
  have hE1 : 1 ≤ Real.exp (2*D/c) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  have hE0 : 0 < Real.exp (2*D/c) := Real.exp_pos _
  have hMED : 0 ≤ M*Real.exp (2*D/c)*D := by positivity
  -- bound the argument of the logarithm by a product
  have hL_bound : 2 + |x| + k + D ≤ 5*M*Real.exp (2*D/c)*D := by
    have e1 : M ≤ M*Real.exp (2*D/c)*D := by
      have h1 : (1:ℝ) ≤ Real.exp (2*D/c)*D := by nlinarith only [hE1, hD1]
      calc M = M*1 := by ring
        _ ≤ M*(Real.exp (2*D/c)*D) := mul_le_mul_of_nonneg_left h1 hM0.le
        _ = M*Real.exp (2*D/c)*D := by ring
    have e2 : 2*Real.exp (2*D/c) ≤ M*Real.exp (2*D/c)*D := by
      have h2 : (2:ℝ) ≤ M*D := by nlinarith only [hM5, hD1]
      calc 2*Real.exp (2*D/c) = Real.exp (2*D/c)*2 := by ring
        _ ≤ Real.exp (2*D/c)*(M*D) := mul_le_mul_of_nonneg_left h2 hE0.le
        _ = M*Real.exp (2*D/c)*D := by ring
    have e3 : 2*D ≤ M*Real.exp (2*D/c)*D := by
      have h3 : (2:ℝ) ≤ M*Real.exp (2*D/c) := by nlinarith only [hM5, hE1]
      calc 2*D = D*2 := by ring
        _ ≤ D*(M*Real.exp (2*D/c)) := mul_le_mul_of_nonneg_left h3 hD0
        _ = M*Real.exp (2*D/c)*D := by ring
    linarith only [hL_le, e1, e2, e3, hMED]
  -- logarithm of a product
  have hLpos : 0 < 2 + |x| + k + D := by positivity
  have hlogL : Real.log (2+|x|+k+D) ≤ Real.log 5 + Real.log M + 2*D/c + Real.log D := by
    have h1 : Real.log (5*M*Real.exp (2*D/c)*D)
        = Real.log (5*M*Real.exp (2*D/c)) + Real.log D :=
      Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt hDpos)
    have h2 : Real.log (5*M*Real.exp (2*D/c))
        = Real.log (5*M) + Real.log (Real.exp (2*D/c)) :=
      Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt hE0)
    have h3 : Real.log (5*M) = Real.log 5 + Real.log M :=
      Real.log_mul (by norm_num) (ne_of_gt hM0)
    calc Real.log (2+|x|+k+D) ≤ Real.log (5*M*Real.exp (2*D/c)*D) :=
          Real.log_le_log hLpos hL_bound
      _ = Real.log 5 + Real.log M + 2*D/c + Real.log D := by
          rw [h1, h2, h3, Real.log_exp]
  -- four logarithmic budgets, each at most D/10
  have hcount : (K*C)*(1 + Real.log (2+|x|+k+D))
      ≤ (K*C)*(1 + (Real.log 5 + Real.log M + 2*D/c + Real.log D)) :=
    mul_le_mul_of_nonneg_left (by linarith only [hlogL]) hA0
  have hexp : (K*C)*(1 + (Real.log 5 + Real.log M + 2*D/c + Real.log D))
      = (K*C)*(1+Real.log 5) + (K*C)*Real.log M + (K*C)*(2*D/c) + (K*C)*Real.log D := by
    ring
  have ta1 : (K*C)*(1+Real.log 5) ≤ D/10 := by linarith only [hD_10A1]
  have ta2 : (K*C)*Real.log M ≤ D/10 := by linarith only [hD_10AlogM]
  have ta3 : (K*C)*(2*D/c) ≤ D/10 := by
    have h2 : 2*(K*C)/c ≤ 1/10 := by rw [div_le_iff₀ hcpos]; nlinarith only [hc20KC]
    calc (K*C)*(2*D/c) = D*(2*(K*C)/c) := by ring
      _ ≤ D*(1/10) := mul_le_mul_of_nonneg_left h2 hD0
      _ = D/10 := by ring
  have ta4 : (K*C)*Real.log D ≤ D/10 := by
    have hsqrt : 20*(K*C) ≤ Real.sqrt D := by
      rw [Real.le_sqrt (by linarith only [hA0]) hD0]; nlinarith only [hD_400A2]
    have hlogD : Real.log D ≤ 2*Real.sqrt D := by
      calc Real.log D ≤ D^(1/2)/(1/2) := Real.log_le_rpow_div hD0 (by norm_num)
        _ = 2*Real.sqrt D := by rw [Real.sqrt_eq_rpow]; ring
    calc (K*C)*Real.log D ≤ (K*C)*(2*Real.sqrt D) := mul_le_mul_of_nonneg_left hlogD hA0
      _ = 2*(K*C)*Real.sqrt D := by ring
      _ ≤ (Real.sqrt D/10)*Real.sqrt D := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg D); linarith only [hsqrt]
      _ = D/10 := by
          rw [show (Real.sqrt D/10)*Real.sqrt D = (Real.sqrt D)^2/10 from by ring,
              Real.sq_sqrt hD0]
  have hA1 : (K*C)*(1 + Real.log (2+|x|+k+D)) ≤ 2*D/5 := by
    linarith only [hcount, hexp, ta1, ta2, ta3, ta4]
  -- the K-budgets
  have tK : 4*K*D/c ≤ D/5 := by
    have h2 : 4*K/c ≤ 1/5 := by rw [div_le_iff₀ hcpos]; nlinarith only [hc20K]
    calc 4*K*D/c = D*(4*K/c) := by ring
      _ ≤ D*(1/5) := mul_le_mul_of_nonneg_left h2 hD0
      _ = D/5 := by ring
  have tK2 : 4*K ≤ D/5 := by linarith only [hD_20K]
  calc K*(C*(1+Real.log (2+|x|+k+D)) + 4*D/c + 4)
      = (K*C)*(1+Real.log (2+|x|+k+D)) + 4*K*D/c + 4*K := by ring
    _ ≤ 2*D/5 + D/5 + D/5 := by linarith only [hA1, tK, tK2]
    _ ≤ D := by linarith only [hD0]

end Work.Parab.coordData
