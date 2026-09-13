import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Star.Real

namespace Commons.Analysis.Sigma2

/-! Lemma 1.2 ("sharp" minimum-eigenvalue control) of Shankar--Yuan, Hessian estimates for the sigma-2 equation in dimension four, in dimension n = 4.

Let `lam : Fin 4 → ℝ` be the (antitone/decreasingly sorted) eigenvalue list of a symmetric operator with sigma_2 = 1 and sigma_1 > 0.  Then `sigma_1 > 2 * |lam 3|`, where `lam 3` is the smallest eigenvalue (antitone hypothesis: `lam 3 ≤ lam i` for all i).

Proof outline (from the paper): if `lam 3 ≥ 0` then `sigma_1 ≥ 4 * lam 3 ≥ 0` handles it; otherwise set `lam' : Fin 3 → ℝ` to the first three entries.  From `sigma_2(lam) = 1` and `lam 3 < 0` one gets `sigma_2(lam') > 1`, and writing `lam 3 = (1 - sigma_2(lam')) / sigma_1(lam')` plus the identity `sigma_1(lam')^2 = (3/2) * (2 * sigma_2(lam') + |traceless part|^2) ≥ 3 * sigma_2(lam')` yields `sigma_1(lam)/(-lam 3) > 2`. -/
open scoped BigOperators

/-- The sigma_1 (trace) of a length-four tuple, expanded. -/
lemma sumFin4 (a : Fin 4 → ℝ) : (∑ i : Fin 4, a i) = a 0 + a 1 + a 2 + a 3 := by
  simp [Fin.sum_univ_four]

/-- The unordered pair sum (sigma_2) of a length-four tuple, expanded. -/
lemma pairSumFin4 (a : Fin 4 → ℝ) :
    (∑ j : Fin 4, ∑ i : Fin 4, if i < j then a i * a j else 0) =
      a 0 * a 1 + a 0 * a 2 + a 0 * a 3 + a 1 * a 2 + a 1 * a 3 + a 2 * a 3 := by
  simp [Fin.sum_univ_succ]
  ring

/-- `(a+b+c)^2 ≥ 3(ab+ac+bc)`: twice the trace dominates three times sigma_2 of a triple. -/
lemma sq_sum3_ge (a b c : ℝ) : (a + b + c)^2 ≥ 3 * (a * b + a * c + b * c) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

theorem sharp_minEigen_four (lam : Fin 4 → ℝ)
    (hmono : ∀ ⦃i j : Fin 4⦄, i ≤ j → lam j ≤ lam i)
    (hσ2 : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then lam i * lam j else 0) = 1)
    (hσ1 : 0 < ∑ i : Fin 4, lam i) :
    (∑ i : Fin 4, lam i) > 2 * |lam 3| := by
  -- Expand sigma_1 into the four entries and name them A, B, C, D.
  rw [sumFin4] at hσ1 ⊢
  have hDleA0 : lam 3 ≤ lam 0 := hmono (show (0 : Fin 4) ≤ (3 : Fin 4) by decide)
  have hDleB0 : lam 3 ≤ lam 1 := hmono (show (1 : Fin 4) ≤ (3 : Fin 4) by decide)
  have hDleC0 : lam 3 ≤ lam 2 := hmono (show (2 : Fin 4) ≤ (3 : Fin 4) by decide)
  set A : ℝ := lam 0
  set B : ℝ := lam 1
  set C : ℝ := lam 2
  set D : ℝ := lam 3
  -- sigma_2(lam) = 1, expanded: (AB+AC+BC) + D*(A+B+C) = 1.
  have hσ2A : A * B + A * C + A * D + B * C + B * D + C * D = 1 := by
    simpa [pairSumFin4] using hσ2
  have hσ2g : (A * B + A * C + B * C) + D * (A + B + C) = 1 := by
    nlinarith [hσ2A]
  by_cases hDnn : 0 ≤ D
  · -- Case lam 3 ≥ 0: every entry is ≥ lam 3, so sigma_1 ≥ 4·lam 3 ≥ 2·lam 3
    rw [abs_of_nonneg hDnn]
    rcases lt_or_eq_of_le hDnn with hDpos | hDzero
    · nlinarith [hDleA0, hDleB0, hDleC0, hDpos]
    · have hD0 : D = 0 := hDzero.symm
      nlinarith [hσ1, hD0]
  · -- Case lam 3 < 0: put S = A+B+C, P = AB+AC+BC.
    -- sigma_2 = 1 gives P + D·S = 1, and (A+B+C)^2 ≥ 3P forces
    -- sigma_1 = S + D > -2D = 2·|lam 3|.
    have hDneg : D < 0 := not_le.mp hDnn
    rw [abs_of_neg hDneg]
    have hsq : (A + B + C)^2 ≥ 3 * (A * B + A * C + B * C) := sq_sum3_ge A B C
    nlinarith [hσ1, hDneg, hσ2g, hsq]

end Commons.Analysis.Sigma2