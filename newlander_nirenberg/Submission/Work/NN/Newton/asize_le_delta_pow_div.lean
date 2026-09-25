import Mathlib
import Submission.Work.NN.Newton.C1smallSetup

/-!
# The stage sizes `a_m = ε 2^{-2Nm}` are bounded by `δ_m^N / C`

For the Newton iteration of `Work.NN.Newton.exists_holFrame_of_C1small` one needs
that, under the smallness hypothesis `C ε 2^{5N} ≤ 1`, every stage size
`asize ε N m = ε 2^{-2 N m}` is bounded by `delta m ^ N / C = 2^{-N(m+3)} / C`.

The proof is elementary. From `C ε 2^{5N} ≤ 1` one gets `C ε ≤ 2^{-5N}`; multiplying
by the nonnegative factor `2^{-2Nm}` and using the law of exponents gives

  `C · asize ε N m ≤ 2^{-(5N + 2Nm)} ≤ 2^{-N(m+3)} = delta m ^ N`,

because `N(m+3) ≤ 5N + 2Nm`. Dividing by `C > 0` concludes. Note that neither `N ≥ 3`
nor `ε ≥ 0` is needed for this particular estimate.
-/

namespace Work.NN.Newton

theorem asize_le_delta_pow_div {C ε : ℝ} {N : ℕ} (hC : 0 < C) (hN : 3 ≤ N) (hε0 : 0 ≤ ε)
    (hε : C * ε * (2:ℝ)^(5*N) ≤ 1) (m : ℕ) :
    asize ε N m ≤ delta m ^ N / C := by
  -- `C ε ≤ 2^{-5N}`, obtained by multiplying `C ε 2^{5N} ≤ 1` by `2^{-5N}`.
  have hCe : C * ε ≤ (1/2:ℝ)^(5*N) := by
    have h2 : (0:ℝ) < (2:ℝ)^(5*N) := by positivity
    have hkey : (1/2:ℝ)^(5*N) * (2:ℝ)^(5*N) = 1 := by
      rw [mul_comm, ← mul_pow]; norm_num
    have h : C * ε * (2:ℝ)^(5*N) ≤ (1/2:ℝ)^(5*N) * (2:ℝ)^(5*N) := by
      rw [hkey]; exact hε
    exact (mul_le_mul_iff_left₀ h2).mp h
  -- `C · asize ε N m = (C ε) · 2^{-2Nm}`.
  have hstep1 : C * asize ε N m = (C * ε) * (1/2:ℝ)^(2*N*m) := by
    simp only [asize]; ring
  have hmono : (C*ε) * (1/2:ℝ)^(2*N*m) ≤ (1/2:ℝ)^(5*N) * (1/2:ℝ)^(2*N*m) :=
    mul_le_mul_of_nonneg_right hCe (by positivity)
  have hmul : (1/2:ℝ)^(5*N) * (1/2:ℝ)^(2*N*m) = (1/2:ℝ)^(5*N + 2*N*m) := by
    rw [← pow_add]
  -- the exponent comparison `N(m+3) ≤ 5N + 2Nm`
  have hexp : N*(m+3) ≤ 5*N + 2*N*m := by
    have h1 : N*(m+3) = N*m + 3*N := by ring
    have h2 : 2*N*m = 2*(N*m) := by ring
    rw [h1, h2]; omega
  -- `2^{-k}` is antitone in `k`
  have hdec : (1/2:ℝ)^(5*N + 2*N*m) ≤ (1/2:ℝ)^(N*(m+3)) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hexp
  have h5 : delta m ^ N = (1/2:ℝ)^(N*(m+3)) := by
    simp only [delta]
    rw [← pow_mul, Nat.mul_comm (m+3) N]
  have hmain : C * asize ε N m ≤ delta m ^ N := by
    rw [hstep1, h5]
    exact hmono.trans (hmul.trans_le hdec)
  rw [le_div_iff₀ hC]
  rwa [mul_comm] at hmain

end Work.NN.Newton
