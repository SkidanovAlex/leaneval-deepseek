import Mathlib
import Submission.Commons.Analysis.Sigma2.jacobi_q_det_nonneg_four
import Submission.Commons.Analysis.Sigma2.jacobi_det_scaled_id
import Submission.Commons.Analysis.Sigma2.linearized_pos_four
import Submission.Commons.Analysis.Sigma2.sigma1_sq_ge_two

namespace Commons.Analysis.Sigma2

open scoped BigOperators in
theorem jacobi_det_nonneg_four (lam : Fin 4 → ℝ)
    (hmono : ∀ ⦃i j : Fin 4⦄, i ≤ j → lam j ≤ lam i)
    (hσ2 : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then lam i * lam j else 0) = 1)
    (hσ1 : 0 < ∑ i : Fin 4, lam i) (i : Fin 4) :
    let S : ℝ := ∑ k : Fin 4, lam k
    let f : ℝ := S - lam i
    let eps : ℝ := (2 / 9 : ℝ) * (1 / 2 + lam 3 / S)
    let δ : ℝ := 1 + eps
    let D : ℝ := 3 * S ^ 2 - 2
    let η : ℝ := 1 + δ * f / S
    0 ≤ 9 - 6 * (1 - f ^ 2 / D) - 3 * η * (1 - 6 / D) +
      2 * η * ((1 - f ^ 2 / D) * (1 - 6 / D) - (1 - 3 * S * f / D) ^ 2) := by
  classical
  -- expand all the `let`s of the goal, then re-introduce the abbreviations
  dsimp
  set S : ℝ := ∑ k : Fin 4, lam k with hSdef
  set f : ℝ := S - lam i with hfdef
  set eps : ℝ := (2 / 9 : ℝ) * (1 / 2 + lam 3 / S) with hepsdef
  set δ : ℝ := 1 + eps with hδdef
  set D : ℝ := 3 * S ^ 2 - 2 with hDdef
  set η : ℝ := 1 + δ * f / S with hηdef
  -- positivity of the denominator factors
  have hSpos : 0 < S := by
    simpa [S] using hσ1
  have hSne : S ≠ 0 := ne_of_gt hSpos
  have hfpos : 0 < f := by
    simpa [S, f] using (linearized_pos_four lam hmono hσ2 hσ1 i)
  have hDpos : 0 < D := by
    have h2 : 2 ≤ S ^ 2 := by
      simpa [S] using (sigma1_sq_ge_two lam hσ2)
    dsimp [D]
    nlinarith
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hepspos : 0 < eps := by
    have h := (jacobi_eps_range_four lam hmono hσ2 hσ1).1
    simpa [S, eps] using h
  have hδpos : 0 < δ := by
    dsimp [δ]
    nlinarith
  -- the normalized variable `y = f / S` lies in the admissible interval [0, (S - lam 3)/S]
  let y : ℝ := f / S
  have hy0 : 0 ≤ y := by
    dsimp [y]
    exact div_nonneg (le_of_lt hfpos) (le_of_lt hSpos)
  have hy : y ≤ (S - lam 3) / S := by
    dsimp [y]
    have hmin : lam 3 ≤ lam i := hmono (Fin.le_last i)
    have hle : S - lam i ≤ S - lam 3 := by
      nlinarith
    exact div_le_div_of_nonneg_right hle (le_of_lt hSpos)
  -- the quadratic in y is nonnegative on that interval
  have hQy : 0 ≤ (12 - 9 * δ) + (12 * δ - 2) * y - 8 * δ * y ^ 2 := by
    have hq := jacobi_q_det_nonneg_four lam hmono hσ2 hσ1 y hy0 hy
    simpa [S, eps, δ] using hq
  -- multiply by S^2 (clearing the denominator) to get a polynomial inequality in f
  have hQf : 0 ≤ (12 - 9 * δ) * S ^ 2 + (12 * δ - 2) * S * f - 8 * δ * f ^ 2 := by
    have hSsq : 0 ≤ S ^ 2 := sq_nonneg S
    have hmul : 0 ≤ S ^ 2 * ((12 - 9 * δ) + (12 * δ - 2) * y - 8 * δ * y ^ 2) :=
      mul_nonneg hSsq hQy
    have hEq : S ^ 2 * ((12 - 9 * δ) + (12 * δ - 2) * y - 8 * δ * y ^ 2) =
        (12 - 9 * δ) * S ^ 2 + (12 * δ - 2) * S * f - 8 * δ * f ^ 2 := by
      dsimp [y]
      field_simp [hSne]
    rwa [hEq] at hmul
  -- the scaled RHS (numerator) is a sum of nonnegative terms
  let num : ℝ :=
    f * ((12 - 9 * δ) * S ^ 2 + (12 * δ - 2) * S * f - 8 * δ * f ^ 2) + 6 * S + 12 * δ * f
  have hnum : 0 ≤ num := by
    have hterm1 : 0 ≤ f * ((12 - 9 * δ) * S ^ 2 + (12 * δ - 2) * S * f - 8 * δ * f ^ 2) :=
      mul_nonneg (le_of_lt hfpos) hQf
    have hterm2 : 0 ≤ 6 * S := mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) (le_of_lt hSpos)
    have hterm3 : 0 ≤ 12 * (δ * f) := by
      have hδf : 0 < δ * f := mul_pos hδpos hfpos
      exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) (le_of_lt hδf)
    dsimp [num]
    nlinarith
  -- scaling identity: T * (D * S) = num
  let T : ℝ :=
    9 - 6 * (1 - f ^ 2 / D) - 3 * η * (1 - 6 / D) +
      2 * η * ((1 - f ^ 2 / D) * (1 - 6 / D) - (1 - 3 * S * f / D) ^ 2)
  have hEqT : T * (D * S) = num := by
    have hsc := jacobi_det_scaled_id S f δ hSne hDne
    calc
      T * (D * S) = (T * D) * S := by ring
      _ = num := by
        simpa [T, η, D, num] using hsc
  have hDS : 0 < D * S := mul_pos hDpos hSpos
  have hTDS : 0 ≤ T * (D * S) := by
    rw [hEqT]
    exact hnum
  change 0 ≤ T
  exact (mul_nonneg_iff_of_pos_right hDS).mp hTDS

end Commons.Analysis.Sigma2
