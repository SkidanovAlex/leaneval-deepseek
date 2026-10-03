import Mathlib
import Submission.Work.FIArea7.NCBasic

namespace Work.FIArea7

/-- Bound for the `E`-term of the numerical core: the factor `E2v` is at most
`1000 (θN + √N + 1) (log (N+2))^3` while `K` dominates `X³ (log (N+2))²⁰`, so the whole
term is `≪ X⁻¹ N² log N`. -/
theorem nc_termE (C_E : ℝ) (hCE : 0 < C_E) :
    ∃ N₀ M : ℝ, 0 < M ∧ ∀ {N X θ E2v : ℝ} {K : ℕ},
      3 ≤ N → N₀ ≤ N → 1 ≤ X → 0 < θ → θ ≤ 1 → 1 ≤ (K : ℝ) →
      X ^ 3 * (Real.log (N + 2)) ^ 20 ≤ (K : ℝ) →
      0 ≤ E2v → E2v ≤ 1000 * (θ * N + Real.sqrt N + 1) * (Real.log (N + 2)) ^ 3 →
      C_E * (X + 1) * (N + 1) * (Real.log (N + 2)) ^ 4 * E2v / (K : ℝ)
        ≤ M * X⁻¹ * N ^ 2 * Real.log N := by
  refine ⟨0, 12000 * C_E, by positivity, ?_⟩
  intro N X θ E2v K hN3 hN0 hX1 hθ0 hθ1 hK1 hKbig hE2v0 hE2v
  have hXpos : (0:ℝ) < X := by linarith
  have hNpos : (0:ℝ) < N := by linarith
  have hKpos : (0:ℝ) < (K:ℝ) := by linarith
  have hLpos : (0:ℝ) < Real.log (N + 2) := Real.log_pos (by linarith)
  have hLge1 : (1:ℝ) ≤ Real.log (N + 2) := one_le_log_of_three_le (by linarith : (3:ℝ) ≤ N + 2)
  have hlogNge1 : (1:ℝ) ≤ Real.log N := one_le_log_of_three_le hN3
  have hlogNpos : (0:ℝ) < Real.log N := by linarith
  have hsqrt : Real.sqrt N ≤ N := by
    have h1 : Real.sqrt N ≤ Real.sqrt (N^2) := Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by linarith : (0:ℝ) ≤ N)] at h1
  -- elementary product bounds
  have hA : X + 1 ≤ 2*X := by linarith
  have hB : N + 1 ≤ 2*N := by linarith
  have hC : θ*N + Real.sqrt N + 1 ≤ 3*N := by
    have h1 : θ*N ≤ N := by nlinarith [hθ1, hNpos]
    linarith
  have h12 : (X+1)*(N+1) ≤ (2*X)*(2*N) :=
    mul_le_mul hA hB (by linarith) (by linarith)
  have hprod : (X+1)*(N+1)*(θ*N + Real.sqrt N + 1) ≤ 12*X*N^2 := by
    calc (X+1)*(N+1)*(θ*N + Real.sqrt N + 1)
        = ((X+1)*(N+1))*(θ*N + Real.sqrt N + 1) := by ring
      _ ≤ ((2*X)*(2*N))*(3*N) := mul_le_mul h12 hC (by positivity) (by positivity)
      _ = 12*X*N^2 := by ring
  -- the reduced inequality, after dividing by the positive factor 1000 * C_E * X * L^7
  have hL13 : (1:ℝ) ≤ (Real.log (N+2))^13 := one_le_pow₀ hLge1
  have hu : (1:ℝ) ≤ (Real.log (N+2))^13 * Real.log N := by
    have := mul_le_mul hL13 hlogNge1 (show (0:ℝ) ≤ 1 by norm_num)
      (show (0:ℝ) ≤ (Real.log (N+2))^13 by linarith)
    simpa using this
  have hred : (X+1)*(N+1)*(θ*N + Real.sqrt N + 1)
      ≤ 12*N^2*X^2*(Real.log (N+2))^13*Real.log N := by
    calc (X+1)*(N+1)*(θ*N + Real.sqrt N + 1) ≤ 12*X*N^2 := hprod
      _ ≤ 12*N^2*X^2 := by nlinarith [hX1, sq_nonneg (X-1), hXpos, hNpos]
      _ ≤ 12*N^2*X^2*(Real.log (N+2))^13*Real.log N := by
            have hnn : (0:ℝ) ≤ 12*N^2*X^2 := by positivity
            have h2 : 12*N^2*X^2*1 ≤ 12*N^2*X^2*((Real.log (N+2))^13 * Real.log N) :=
              mul_le_mul_of_nonneg_left hu hnn
            calc 12*N^2*X^2 = 12*N^2*X^2*1 := by ring
              _ ≤ 12*N^2*X^2*((Real.log (N+2))^13 * Real.log N) := h2
              _ = 12*N^2*X^2*(Real.log (N+2))^13*Real.log N := by ring
  -- the cross-multiplied inequality
  have key : C_E*(X+1)*(N+1)*(Real.log (N+2))^4*E2v*X
      ≤ 12000*C_E*N^2*Real.log N*(K:ℝ) := by
    have hstep : C_E*(X+1)*(N+1)*(Real.log (N+2))^4*E2v
        ≤ C_E*(X+1)*(N+1)*(Real.log (N+2))^4*(1000*(θ*N+Real.sqrt N+1)*(Real.log (N+2))^3) :=
      mul_le_mul_of_nonneg_left hE2v (by positivity)
    have hstep2 : C_E*(X+1)*(N+1)*(Real.log (N+2))^4*E2v*X
        ≤ C_E*(X+1)*(N+1)*(Real.log (N+2))^4*(1000*(θ*N+Real.sqrt N+1)*(Real.log (N+2))^3)*X := by
      calc C_E*(X+1)*(N+1)*(Real.log (N+2))^4*E2v*X
          = (C_E*(X+1)*(N+1)*(Real.log (N+2))^4*E2v)*X := by ring
        _ ≤ (C_E*(X+1)*(N+1)*(Real.log (N+2))^4*(1000*(θ*N+Real.sqrt N+1)*(Real.log (N+2))^3))*X :=
              mul_le_mul_of_nonneg_right hstep hXpos.le
        _ = C_E*(X+1)*(N+1)*(Real.log (N+2))^4*(1000*(θ*N+Real.sqrt N+1)*(Real.log (N+2))^3)*X := by ring
    calc C_E*(X+1)*(N+1)*(Real.log (N+2))^4*E2v*X
        ≤ C_E*(X+1)*(N+1)*(Real.log (N+2))^4*(1000*(θ*N+Real.sqrt N+1)*(Real.log (N+2))^3)*X := hstep2
      _ = 1000*C_E*(X+1)*(N+1)*X*(θ*N+Real.sqrt N+1)*(Real.log (N+2))^7 := by ring
      _ ≤ 12000*C_E*N^2*X^3*(Real.log (N+2))^20*Real.log N := by
            have hm := mul_le_mul_of_nonneg_left hred (by positivity : (0:ℝ) ≤ 1000*C_E*X*(Real.log (N+2))^7)
            calc 1000*C_E*(X+1)*(N+1)*X*(θ*N+Real.sqrt N+1)*(Real.log (N+2))^7
                = 1000*C_E*X*(Real.log (N+2))^7*((X+1)*(N+1)*(θ*N+Real.sqrt N+1)) := by ring
              _ ≤ 1000*C_E*X*(Real.log (N+2))^7*(12*N^2*X^2*(Real.log (N+2))^13*Real.log N) := hm
              _ = 12000*C_E*N^2*X^3*(Real.log (N+2))^20*Real.log N := by ring
      _ ≤ 12000*C_E*N^2*Real.log N*(K:ℝ) := by
            have hm2 := mul_le_mul_of_nonneg_left hKbig (by positivity : (0:ℝ) ≤ 12000*C_E*N^2*Real.log N)
            calc 12000*C_E*N^2*X^3*(Real.log (N+2))^20*Real.log N
                = 12000*C_E*N^2*Real.log N*(X^3*(Real.log (N+2))^20) := by ring
              _ ≤ 12000*C_E*N^2*Real.log N*(K:ℝ) := hm2
  -- divide the cross-multiplied inequality by the positive number K * X
  have hfin : C_E*(X+1)*(N+1)*(Real.log (N+2))^4*E2v/(K:ℝ)
      ≤ 12000*C_E*N^2*Real.log N/X := by
    have hXeq : C_E*(X+1)*(N+1)*(Real.log (N+2))^4*E2v/(K:ℝ)*X
        = C_E*(X+1)*(N+1)*(Real.log (N+2))^4*E2v*X/(K:ℝ) := by ring
    rw [le_div_iff₀ hXpos, hXeq, div_le_iff₀ hKpos]
    exact key
  rw [show 12000*C_E*X⁻¹*N^2*Real.log N = 12000*C_E*N^2*Real.log N/X from by ring]
  exact hfin

end Work.FIArea7
