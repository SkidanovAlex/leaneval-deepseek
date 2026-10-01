import Mathlib
import Submission.Work.ZeroFreeTables.Rep9.principalSigmaDiff
import Submission.Work.ZeroFreeTables.Rep9.primeFactorSum_le_sqrt_log_proof

namespace Work.ZeroFreeTables.Engine6

/-- Algebraic rearrangement used at the end of `principalSigmaDiff_gen`. -/
private lemma combine_eq {L : ℝ} (hL : L ≠ 0) (a Dm T : ℝ) :
    (12 / L) * ((a * (Dm * T)) + ((a ^ 2 / L) * (Dm * T)) + ((a ^ 3 / L ^ 2) * (Dm * T)))
      = (a / L) * (12 * Dm) * T * (1 + a / L + (a / L) ^ 2) := by
  field_simp

theorem principalSigmaDiff_gen {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {L lam₁ : ℝ}, 0 < L → Real.log (q : ℝ) ≤ L →
      0 ≤ lam₁ → lam₁ ≤ M → ∀ s : ℂ, s.re = 1 + a / L →
        |Work.ZeroFreeTables.SigmaP3L q L (1 : DirichletCharacter ℂ q) s a lam₁
            - Work.ZeroFreeTables.SigmaP3L 1 L 1 s a lam₁|
          ≤ ((a + lam₁) / L) * C * (1 + Real.sqrt (Real.log (q : ℝ)))
              * (1 + (a + lam₁) / L + ((a + lam₁) / L) ^ 2) := by
  obtain ⟨D1, hD1pos, hD1⟩ := Work.ZeroFreeTables.Rep9.primeFactorSum_le_sqrt_log_proof 1 (by norm_num)
  obtain ⟨D2, hD2pos, hD2⟩ := Work.ZeroFreeTables.Rep9.primeFactorSum_le_sqrt_log_proof 2 (by norm_num)
  obtain ⟨D3, hD3pos, hD3⟩ := Work.ZeroFreeTables.Rep9.primeFactorSum_le_sqrt_log_proof 3 (by norm_num)
  have hD12 : 0 < max D1 D2 := lt_of_lt_of_le hD1pos (le_max_left D1 D2)
  have hDmpos : 0 < max (max D1 D2) D3 := lt_of_lt_of_le hD12 (le_max_left (max D1 D2) D3)
  refine ⟨12 * max (max D1 D2) D3, mul_pos (by norm_num) hDmpos, ?_⟩
  intro q _ L lam₁ hL hlog hlam₁ hMle s hs
  have hq1 : 1 ≤ q := by have := NeZero.ne q; omega
  have hTnn : 0 ≤ 1 + Real.sqrt (Real.log (q : ℝ)) := by
    have h : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq1)
    positivity
  have hsre : 1 < s.re := by
    rw [hs]
    have h : 0 < a / L := div_pos ha hL
    linarith
  have hα : 0 ≤ a + lam₁ := by linarith
  have hDm_le_1 : D1 ≤ max (max D1 D2) D3 :=
    le_trans (le_max_left D1 D2) (le_max_left (max D1 D2) D3)
  have hDm_le_2 : D2 ≤ max (max D1 D2) D3 :=
    le_trans (le_max_right D1 D2) (le_max_left (max D1 D2) D3)
  have hDm_le_3 : D3 ≤ max (max D1 D2) D3 := le_max_right (max D1 D2) D3
  have hkey := Work.ZeroFreeTables.Rep9.principalDiff_bound (q := q) hL hsre ha hlam₁
  have hS1 : (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
      ≤ max (max D1 D2) D3 * (1 + Real.sqrt (Real.log (q : ℝ))) := by
    have h := hD1 q hq1
    simp only [pow_one] at h
    exact h.trans (mul_le_mul_of_nonneg_right hDm_le_1 hTnn)
  have hS2 : (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
      ≤ max (max D1 D2) D3 * (1 + Real.sqrt (Real.log (q : ℝ))) :=
    (hD2 q hq1).trans (mul_le_mul_of_nonneg_right hDm_le_2 hTnn)
  have hS3 : (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ))
      ≤ max (max D1 D2) D3 * (1 + Real.sqrt (Real.log (q : ℝ))) :=
    (hD3 q hq1).trans (mul_le_mul_of_nonneg_right hDm_le_3 hTnn)
  have hA1 : (a + lam₁) * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
      ≤ (a + lam₁) * (max (max D1 D2) D3 * (1 + Real.sqrt (Real.log (q : ℝ)))) :=
    mul_le_mul_of_nonneg_left hS1 hα
  have hA2 : ((a + lam₁) ^ 2 / L) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
      ≤ ((a + lam₁) ^ 2 / L)
        * (max (max D1 D2) D3 * (1 + Real.sqrt (Real.log (q : ℝ)))) :=
    mul_le_mul_of_nonneg_left hS2 (by positivity)
  have hA3 : ((a + lam₁) ^ 3 / L ^ 2)
        * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ))
      ≤ ((a + lam₁) ^ 3 / L ^ 2)
        * (max (max D1 D2) D3 * (1 + Real.sqrt (Real.log (q : ℝ)))) :=
    mul_le_mul_of_nonneg_left hS3 (by positivity)
  have hsum : (a + lam₁) * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
        + ((a + lam₁) ^ 2 / L) * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
        + ((a + lam₁) ^ 3 / L ^ 2)
            * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ))
      ≤ (a + lam₁) * (max (max D1 D2) D3 * (1 + Real.sqrt (Real.log (q : ℝ))))
        + ((a + lam₁) ^ 2 / L)
            * (max (max D1 D2) D3 * (1 + Real.sqrt (Real.log (q : ℝ))))
        + ((a + lam₁) ^ 3 / L ^ 2)
            * (max (max D1 D2) D3 * (1 + Real.sqrt (Real.log (q : ℝ)))) := by
    linarith [hA1, hA2, hA3]
  have hmain : |Work.ZeroFreeTables.SigmaP3L q L (1 : DirichletCharacter ℂ q) s a lam₁
        - Work.ZeroFreeTables.SigmaP3L 1 L 1 s a lam₁|
      ≤ (12 / L)
        * ((a + lam₁) * (max (max D1 D2) D3 * (1 + Real.sqrt (Real.log (q : ℝ))))
          + ((a + lam₁) ^ 2 / L)
              * (max (max D1 D2) D3 * (1 + Real.sqrt (Real.log (q : ℝ))))
          + ((a + lam₁) ^ 3 / L ^ 2)
              * (max (max D1 D2) D3 * (1 + Real.sqrt (Real.log (q : ℝ))))) :=
    hkey.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  have heq := combine_eq (L := L) (ne_of_gt hL) (a + lam₁) (max (max D1 D2) D3)
    (1 + Real.sqrt (Real.log (q : ℝ)))
  rw [heq] at hmain
  exact hmain

end Work.ZeroFreeTables.Engine6
