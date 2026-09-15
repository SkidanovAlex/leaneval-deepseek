import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Asymptotics

-- Arithmetic of an induction on scales: if `L > 1`, `T ≥ 1`, `0 < γ < 1` and `m` is such that
-- `L ^ (m * T + 1) ≤ N < L ^ ((m + 1) * T + 1)`, then `(1 - γ) ^ (m + 1) ≤ C * N ^ (-β)` with
-- `β = -log (1 - γ) / (T * log L) > 0` and `C = (1 - γ) ^ (-(1 / T)) > 0` (both independent of
-- `N` and `m`).
-- Proof: take logarithms; `N < L^((m+1)T+1)` gives `(m+1) > (log N / log L - 1) / T`, and
-- multiplying by `log (1 - γ) < 0` gives
-- `(m+1) log (1-γ) < -β log N - log(1-γ)/T`, i.e. `(1-γ)^(m+1) < N^(-β) * (1-γ)^(-1/T)`.
theorem pow_one_sub_le_rpow_neg {L T : ℕ} (hL : 1 < L) (hT : 0 < T) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ1 : γ < 1) :
    ∃ (β C : ℝ), 0 < β ∧ 0 < C ∧ ∀ (N : ℝ) (m : ℕ), 1 ≤ N →
      (L : ℝ) ^ (m * T + 1) ≤ N → N < (L : ℝ) ^ ((m + 1) * T + 1) →
        (1 - γ) ^ (m + 1) ≤ C * N ^ (-β) := by
  set s : ℝ := 1 - γ with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  have hs1 : s < 1 := by rw [hs]; linarith
  have hlogs : Real.log s < 0 := Real.log_neg hs0 hs1
  have hL1 : (1 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < (L : ℝ) := lt_trans zero_lt_one hL1
  have hlogL : 0 < Real.log (L : ℝ) := Real.log_pos hL1
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  set β : ℝ := -Real.log s / ((T : ℝ) * Real.log (L : ℝ)) with hβ
  set C : ℝ := s ^ (-(1 / (T : ℝ))) with hC
  have hβpos : 0 < β := by
    rw [hβ]
    exact div_pos (by linarith) (mul_pos hTpos hlogL)
  have hCpos : 0 < C := by
    rw [hC]
    exact Real.rpow_pos_of_pos hs0 _
  refine ⟨β, C, hβpos, hCpos, ?_⟩
  intro N m hN hle hlt
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hlogN_lt : Real.log N < ((m : ℝ) + 1) * (T : ℝ) * Real.log (L : ℝ) + Real.log (L : ℝ) := by
    have h := Real.log_lt_log hNpos hlt
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hW : Real.log N - (((m : ℝ) + 1) * (T : ℝ) + 1) * Real.log (L : ℝ) < 0 := by linarith
  have hlhs_pos : 0 < s ^ (m + 1) := pow_pos hs0 _
  have hrhs_pos : 0 < C * N ^ (-β) := mul_pos hCpos (Real.rpow_pos_of_pos hNpos _)
  rw [← Real.log_le_log_iff hlhs_pos hrhs_pos]
  rw [Real.log_pow]
  rw [Real.log_mul (ne_of_gt hCpos) (ne_of_gt (Real.rpow_pos_of_pos hNpos _))]
  rw [hC, Real.log_rpow hs0, Real.log_rpow hNpos, hβ]
  have hTne : (T : ℝ) ≠ 0 := ne_of_gt hTpos
  have hTLne : (T : ℝ) * Real.log (L : ℝ) ≠ 0 := ne_of_gt (mul_pos hTpos hlogL)
  have hprod : 0 ≤ Real.log s * (Real.log N - (((m : ℝ) + 1) * (T : ℝ) + 1) * Real.log (L : ℝ)) :=
    mul_nonneg_of_nonpos_of_nonpos (le_of_lt hlogs) (le_of_lt hW)
  push_cast
  field_simp
  nlinarith [hprod]

end Commons.Analysis.Asymptotics