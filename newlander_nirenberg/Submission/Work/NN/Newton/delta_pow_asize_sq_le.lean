import Mathlib
import Submission.Work.NN.Newton.C1smallSetup
import Submission.Work.NN.Newton.C1smallSumBounds
import Submission.Work.NN.Newton.C1smallRadBounds

namespace Work.NN.Newton

theorem delta_pow_asize_sq_le {C ε : ℝ} {N : ℕ} (hC : 0 < C) (hN : 3 ≤ N) (hε0 : 0 ≤ ε)
    (hε : C * ε * (2:ℝ)^(5*N) ≤ 1) (m : ℕ) :
    C / delta m ^ N * (asize ε N m)^2 ≤ asize ε N (m+1) := by
  have ha0 : (0:ℝ) ≤ (1/2:ℝ) := by norm_num
  have ha1 : (1/2:ℝ) ≤ 1 := by norm_num
  -- bound on `C * ε`
  have hCε : C * ε ≤ (1/2:ℝ)^(5*N) := by
    rw [one_div_pow, le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^(5*N))]
    exact hε
  -- the key bound `C ε 2^{-Nm} ≤ 2^{-5N}`
  have hkey : C * ε * (1/2:ℝ)^(N*m) ≤ (1/2:ℝ)^(5*N) := by
    calc C * ε * (1/2:ℝ)^(N*m) = (C * ε) * (1/2:ℝ)^(N*m) := by ring
      _ ≤ (C * ε) * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ ha0 ha1) (mul_nonneg hC.le hε0)
      _ = C * ε := by ring
      _ ≤ (1/2:ℝ)^(5*N) := hCε
  have hδpos : 0 < delta m ^ N := pow_pos (deltaPos m) N
  have hnn : 0 ≤ ε * (1/2:ℝ)^(3*N*m) := mul_nonneg hε0 (pow_nonneg ha0 _)
  -- right-hand side in closed form
  have hRHS : asize ε N (m+1) * delta m ^ N = ε * (1/2:ℝ)^(3*N*m + 5*N) := by
    rw [asize, delta_pow, mul_assoc, ← pow_add,
        show 2*N*(m+1) + (m+3)*N = 3*N*m + 5*N from by ring]
  -- left-hand side factored
  have hLHS : C * (asize ε N m)^2
      = (C * ε * (1/2:ℝ)^(N*m)) * (ε * (1/2:ℝ)^(3*N*m)) := by
    rw [asize]
    have e2 : (2:ℕ) * N * m = N * m + N * m := by ring
    have e3 : (3:ℕ) * N * m = N * m + N * m + N * m := by ring
    rw [e2, e3, pow_add, pow_add, pow_add]
    ring
  rw [div_mul_eq_mul_div, div_le_iff₀ hδpos]
  calc C * (asize ε N m)^2
      = (C * ε * (1/2:ℝ)^(N*m)) * (ε * (1/2:ℝ)^(3*N*m)) := hLHS
    _ ≤ (1/2:ℝ)^(5*N) * (ε * (1/2:ℝ)^(3*N*m)) := mul_le_mul_of_nonneg_right hkey hnn
    _ = ε * ((1/2:ℝ)^(5*N) * (1/2:ℝ)^(3*N*m)) := by ring
    _ = ε * (1/2:ℝ)^(5*N + 3*N*m) := by rw [← pow_add]
    _ = ε * (1/2:ℝ)^(3*N*m + 5*N) := by
          rw [show (5:ℕ)*N + 3*N*m = 3*N*m + 5*N from by ring]
    _ = asize ε N (m+1) * delta m ^ N := hRHS.symm

end Work.NN.Newton
