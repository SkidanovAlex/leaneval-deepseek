import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.Analysis.Sigma2.pairSum_sq

namespace Commons.Analysis.Sigma2

/-! Lower bound for the eigenvalues `f_i = sigma_1 - lambda_i` of the linearized operator at the NON-largest eigenvalues in dimension 4 (Corollary 1.3 of Shankar--Yuan, case `i ≥ 2` 1-based): if `lam` is the decreasingly sorted eigenvalue tuple with sigma_2 = 1 and sigma_1 > 0, then for every `i : Fin 4` with `i ≠ 0` (i.e. not the largest eigenvalue), `(1 - 1 / Real.sqrt 2) * sigma_1 ≤ sigma_1 - lam i`.  Proof: if `lam i ≤ 0` then `f_i = sigma_1 - lam i ≥ sigma_1`; else (lam i > 0, so all of lam 0,...,lam i are positive and lam 0 ≥ ... ≥ lam i > 0), use `lam i ≤ Real.sqrt ((lam 0^2 + ... + lam i^2) / (i.val + 1))` (mean of squares) and `sigma_1 = Real.sqrt (2 + |lam|^2) > Real.sqrt (lam 0^2 + ... + lam i^2)` to get `f_i > sigma_1 * (1 - 1 / Real.sqrt (i.val + 1)) ≥ (1 - 1 / Real.sqrt 2) * sigma_1`. -/
open scoped BigOperators

theorem linearized_lower_large_four (lam : Fin 4 → ℝ)
    (hmono : ∀ ⦃i j : Fin 4⦄, i ≤ j → lam j ≤ lam i)
    (hσ2 : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then lam i * lam j else 0) = 1)
    (hσ1 : 0 < ∑ i : Fin 4, lam i) :
    ∀ i : Fin 4, i ≠ 0 →
      (1 - 1 / Real.sqrt 2) * (∑ j : Fin 4, lam j) ≤ (∑ j : Fin 4, lam j) - lam i := by
  intro i hi0
  let s1 : ℝ := ∑ j : Fin 4, lam j
  let S : ℝ := ∑ j : Fin 4, (lam j) ^ 2
  have hs1pos : 0 < s1 := by simpa [s1] using hσ1
  -- key identity: s1^2 = S + 2 (sigma_2 = 1)
  have hsq : s1 ^ 2 = S + 2 := by
    have h := pairSum_sq (a := lam)
    rw [hσ2] at h
    dsimp [s1, S] at h ⊢
    linarith
  -- S < s1^2
  have hS_lt : S < s1 ^ 2 := by
    nlinarith [hsq]
  -- the crucial case i = 1 (the second-largest eigenvalue):
  have hmain : (1 - 1 / Real.sqrt 2) * s1 ≤ s1 - lam (1 : Fin 4) := by
    by_cases hle : lam (1 : Fin 4) ≤ 0
    · have hcoef : (1 - 1 / Real.sqrt 2) ≤ (1 : ℝ) := by
        have h : (0 : ℝ) ≤ 1 / Real.sqrt 2 := by positivity
        linarith
      have h1 : (1 - 1 / Real.sqrt 2) * s1 ≤ s1 := by
        simpa using (mul_le_mul_of_nonneg_right hcoef hs1pos.le)
      have h2 : s1 ≤ s1 - lam (1 : Fin 4) := by linarith
      exact le_trans h1 h2
    · have hpos : 0 < lam (1 : Fin 4) := lt_of_not_ge hle
      -- lam 0 ≥ lam 1 > 0, so (lam 1)^2 ≤ (lam 0)^2
      have h01 : lam (1 : Fin 4) ≤ lam (0 : Fin 4) := hmono (by decide : (0 : Fin 4) ≤ (1 : Fin 4))
      have hpos0 : 0 < lam (0 : Fin 4) := lt_of_lt_of_le hpos h01
      have hsq01 : (lam (1 : Fin 4)) ^ 2 ≤ (lam (0 : Fin 4)) ^ 2 :=
        (sq_le_sq₀ (le_of_lt hpos) (le_of_lt hpos0)).2 h01
      -- expand S and use nonnegativity of the remaining squares
      have hS_exp : S = (lam (0 : Fin 4)) ^ 2 + (lam (1 : Fin 4)) ^ 2 +
          (lam (2 : Fin 4)) ^ 2 + (lam (3 : Fin 4)) ^ 2 := by
        dsimp [S]
        rw [Fin.sum_univ_four]
      have htwo_le_S : 2 * (lam (1 : Fin 4)) ^ 2 ≤ S := by
        rw [hS_exp]
        nlinarith [hsq01, sq_nonneg (lam (2 : Fin 4)), sq_nonneg (lam (3 : Fin 4))]
      have htwo_lt : 2 * (lam (1 : Fin 4)) ^ 2 < s1 ^ 2 := lt_of_le_of_lt htwo_le_S hS_lt
      have hsq_lt : (lam (1 : Fin 4)) ^ 2 < (s1 / Real.sqrt 2) ^ 2 := by
        have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
        have hsqdiv : (s1 / Real.sqrt 2) ^ 2 = s1 ^ 2 / 2 := by
          rw [div_pow, hsqrt]
        rw [hsqdiv]
        nlinarith
      have hlam_lt : lam (1 : Fin 4) < s1 / Real.sqrt 2 :=
        (sq_lt_sq₀ (le_of_lt hpos) (div_nonneg hs1pos.le (Real.sqrt_nonneg _))).mp hsq_lt
      have hgt : (1 - 1 / Real.sqrt 2) * s1 < s1 - lam (1 : Fin 4) := by
        calc
          (1 - 1 / Real.sqrt 2) * s1 = s1 - s1 / Real.sqrt 2 := by ring
          _ < s1 - lam (1 : Fin 4) := by linarith
      exact le_of_lt hgt
  -- reduce the arbitrary index i ≥ 1 to the case i = 1 by monotonicity
  have hred : lam i ≤ lam (1 : Fin 4) := by
    apply hmono (i := (1 : Fin 4)) (j := i)
    have hival : (1 : Fin 4).val ≤ i.val := by
      have hne : i.val ≠ 0 := by
        intro h
        exact hi0 (Fin.ext h)
      omega
    exact hival
  have htail : s1 - lam (1 : Fin 4) ≤ s1 - lam i := by linarith
  exact le_trans hmain htail

end Commons.Analysis.Sigma2