import Mathlib
import Submission.Work.LinnikAreas.Density4.selTheta_asymptotic

namespace Work.LinnikAreas.Density4

open Finset
open scoped BigOperators

noncomputable section

/-- `κ(n) = n · ∏_{p | n} (1 + 1/p)`, the weight appearing in An's Lemma 11/12
(Graham's (11)/(12)) and in the density-4 part of Linnik's theorem. -/
def kappaR (n : ℕ) : ℝ := (n : ℝ) * ∏ p ∈ n.primeFactors, (1 + (1 : ℝ) / (p : ℝ))

/-- The log-weighted `κ`-sum `Σ_{(n,r)=1, n ≤ ⌊z⌋} μ(n)/κ(n) · log(z/n)`
(An's Lemma 11 for `k = Q`). -/
def kappaLogSum (z : ℝ) (r : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 ⌊z⌋₊).filter (fun n => Nat.Coprime n r),
    (ArithmeticFunction.moebius n : ℝ) / kappaR n * Real.log (z / (n : ℝ))

/-- The unweighted `κ`-sum `Σ_{(n,r)=1, n ≤ N} μ(n)/κ(n)` (An's Lemma 12 for `k = Q`). -/
def kappaSum (N : ℕ) (r : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime n r),
    (ArithmeticFunction.moebius n : ℝ) / kappaR n

end

end Work.LinnikAreas.Density4
