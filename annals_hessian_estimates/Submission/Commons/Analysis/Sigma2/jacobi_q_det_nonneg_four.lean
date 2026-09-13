import Mathlib
import Submission.Commons.Analysis.Sigma2.jacobi_eps_range_four
import Submission.Commons.Analysis.Sigma2.linearized_upper_four

namespace Commons.Analysis.Sigma2

open scoped BigOperators

/-- Core quadratic nonnegativity in the normalized variable `x = lam 3 / sigma_1`.  For
`-1/2 ≤ x ≤ 1/4` and `0 ≤ y ≤ 1 - x` the quadratic
`Q(y) = (12 - 9*(1+eps)) + (12*(1+eps)-2)*y - 8*(1+eps)*y^2`, `eps := (2/9)*(1/2 + x)`,
is nonnegative.  The quadratic is concave in `y` (coefficient of `y^2` is `-8(1+eps) < 0`),
so we chord-decompose it over the interval `[0, 1-x]`:
`(1-x) * Q(y) = (b-y)*Q(0) + y*Q(b) + 8(1+eps)*b*y*(b-y)`, `b := 1-x`, and the endpoint
values factor as `Q(0) = 2(1-x)` and `Q(1-x) = (8/9)(1-x)(1+2x)(5+x)`, each a product of
nonnegative factors. -/
private lemma jacobi_q_det_core_four (x y : ℝ) (hxlo : -1 / 2 ≤ x) (hxhi : x ≤ 1 / 4)
    (hy0 : 0 ≤ y) (hy : y ≤ 1 - x) :
    0 ≤ (12 - 9 * (1 + (2 / 9 : ℝ) * (1 / 2 + x))) +
        (12 * (1 + (2 / 9 : ℝ) * (1 / 2 + x)) - 2) * y -
        8 * (1 + (2 / 9 : ℝ) * (1 / 2 + x)) * y ^ 2 := by
  let eps : ℝ := (2 / 9 : ℝ) * (1 / 2 + x)
  let b : ℝ := 1 - x
  let A : ℝ := 12 - 9 * (1 + eps)
  let B : ℝ := 12 * (1 + eps) - 2
  let C : ℝ := 8 * (1 + eps)
  change 0 ≤ A + B * y - C * y ^ 2
  have hA : A = 2 * b := by
    dsimp [A, eps, b]
    ring
  have hb0 : 0 < b := by
    dsimp [b]
    nlinarith
  have hb_nonneg : 0 ≤ b := le_of_lt hb0
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hb_nonneg
  have heps0 : 0 ≤ eps := by
    dsimp [eps]
    nlinarith
  have hC0 : 0 ≤ C := by
    dsimp [C]
    nlinarith
  have h12x : 0 ≤ 1 + 2 * x := by nlinarith
  have h1x : 0 ≤ 1 - x := by nlinarith
  have h5x : 0 ≤ 5 + x := by nlinarith
  let Qb : ℝ := A + B * b - C * b ^ 2
  have hQb : Qb = (8 / 9 : ℝ) * (1 - x) * (1 + 2 * x) * (5 + x) := by
    dsimp [Qb, A, B, C, eps, b]
    ring
  have hQb0 : 0 ≤ Qb := by
    rw [hQb]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8 / 9) h1x) h12x) h5x
  have hchord : b * (A + B * y - C * y ^ 2) =
      (b - y) * A + y * Qb + b * C * y * (b - y) := by
    dsimp [Qb]
    ring
  have hby : 0 ≤ b - y := by nlinarith
  have hsum : 0 ≤ (b - y) * A + y * Qb + b * C * y * (b - y) := by
    positivity
  have hbQ : 0 ≤ b * (A + B * y - C * y ^ 2) := by
    rw [hchord]
    exact hsum
  exact (mul_nonneg_iff_of_pos_left hb0).mp hbQ

open scoped BigOperators in
theorem jacobi_q_det_nonneg_four (lam : Fin 4 → ℝ)
    (hmono : ∀ ⦃i j : Fin 4⦄, i ≤ j → lam j ≤ lam i)
    (hσ2 : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then lam i * lam j else 0) = 1)
    (hσ1 : 0 < ∑ i : Fin 4, lam i) (y : ℝ) (hy0 : 0 ≤ y)
    (hy : y ≤ ((∑ k : Fin 4, lam k) - lam 3) / (∑ k : Fin 4, lam k)) :
    let S : ℝ := ∑ k : Fin 4, lam k
    let eps : ℝ := (2 / 9 : ℝ) * (1 / 2 + lam 3 / S)
    0 ≤ (12 - 9 * (1 + eps)) + (12 * (1 + eps) - 2) * y - 8 * (1 + eps) * y ^ 2 := by
  classical
  let s : ℝ := ∑ k : Fin 4, lam k
  let z : ℝ := lam 3
  let x : ℝ := z / s
  have hspos : 0 < s := by
    simpa [s] using hσ1
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hz : 4 * z ≤ s := by
    dsimp [z, s]
    have hle : (∑ _i : Fin 4, lam 3) ≤ (∑ i : Fin 4, lam i) := by
      exact Finset.sum_le_sum fun i _hi => hmono (Fin.le_last i)
    simpa [mul_comm] using hle
  have hxhi : x ≤ 1 / 4 := by
    dsimp [x]
    rw [div_le_iff₀ hspos]
    dsimp [z]
    nlinarith
  have hxlo : -1 / 2 ≤ x := by
    have hE : 0 < (2 / 9 : ℝ) * (1 / 2 + lam 3 / s) := by
      simpa [s] using (jacobi_eps_range_four lam hmono hσ2 hσ1).1
    have h12 : 0 < 1 / 2 + lam 3 / s := by
      exact (mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 2 / 9)).mp hE
    dsimp [x]
    nlinarith
  have hyb : y ≤ 1 - x := by
    have hhy : y ≤ (s - z) / s := by
      simpa [s, z] using hy
    have hEq : (s - z) / s = 1 - z / s := by
      field_simp [hsne]
    rw [hEq] at hhy
    simpa [x] using hhy
  dsimp
  exact jacobi_q_det_core_four x y hxlo hxhi hy0 hyb

end Commons.Analysis.Sigma2
