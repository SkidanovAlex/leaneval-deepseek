import Mathlib
import Submission.Work.ZeroFreeTables.Rep9.vonMangoldtComplCoprimeEqSum_proof

namespace Work.ZeroFreeTables.Rep9

theorem vonMangoldtComplCoprimeEqSum {q : ℕ} (hq : q ≠ 0) {σ : ℝ} (j : ℕ) (n : ℕ) :
    (if Nat.Coprime n q then (0:ℝ) else 1) * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j
      = ∑ p ∈ q.primeFactors, (if IsPrimePow n ∧ n.minFac = p then (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j else (0:ℝ)) :=
  vonMangoldtComplCoprimeEqSum_proof hq j n

end Work.ZeroFreeTables.Rep9
