import Mathlib
import Submission.Commons.MeasureTheory.Integral.simplex_integral_scaled
import Submission.Commons.MeasureTheory.Integral.simplex_integral_shifted

open MeasureTheory
open scoped BigOperators

namespace Commons.MeasureTheory.Integral

theorem marginal_simplex_integral {k : ℕ} (eps : ℝ) (heps0 : 0 < eps) (heps1 : eps < 1)
    (A A' : ℕ) (a a' : Fin (k + 1) → ℕ) :
    ∫ t : Fin k → ℝ in {u | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1 - eps},
        (1 + eps - ∑ i, t i) ^ (A + A' + a 0 + a' 0 + 2) *
          ∏ i : Fin k, (t i) ^ (a (Fin.succ i) + a' (Fin.succ i))
      = ∑ j ∈ Finset.range (A + A' + a 0 + a' 0 + 3),
          ((Nat.choose (A + A' + a 0 + a' 0 + 2) j : ℕ) : ℝ) * (2 * eps) ^ j *
            ((1 - eps) ^ (k + (A + A' + a 0 + a' 0 + 2 - j) + ∑ i : Fin k, (a (Fin.succ i) + a' (Fin.succ i))) *
              ((((Nat.factorial (A + A' + a 0 + a' 0 + 2 - j)) *
                    ∏ i : Fin k, Nat.factorial (a (Fin.succ i) + a' (Fin.succ i)) : ℕ) : ℝ) /
                ((Nat.factorial ((A + A' + a 0 + a' 0 + 2 - j) + ∑ i : Fin k, (a (Fin.succ i) + a' (Fin.succ i)) + k) : ℕ) : ℝ))) := by
  have hc : (0:ℝ) < 1 - eps := by linarith
  have hd : (1 + eps) - (1 - eps) = 2 * eps := by ring
  rw [simplex_integral_shifted (1 - eps) (1 + eps) hc (A + A' + a 0 + a' 0 + 2)
      (fun i : Fin k => a (Fin.succ i) + a' (Fin.succ i))]
  have hN : (A + A' + a 0 + a' 0 + 2 + 1) = A + A' + a 0 + a' 0 + 3 := by omega
  simp only [hd, hN, mul_div_assoc]

end Commons.MeasureTheory.Integral
