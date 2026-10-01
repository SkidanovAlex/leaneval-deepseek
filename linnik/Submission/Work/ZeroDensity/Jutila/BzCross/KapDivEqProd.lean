import Mathlib
import Submission.Work.ZeroDensity.Jutila.Bz3Defs

namespace Work.ZeroDensity.Jutila.BzCross

open Finset

/-- For squarefree `t`, `κ(t)/t = ∏_{p ∣ t} (p+1)/p`, where `κ = kap` is
`∏_{p ∣ t} (p+1)`: since `t = ∏_{p ∣ t} p` is squarefree. -/
lemma KapDivEqProd (t : ℕ) (ht : Squarefree t) :
    Work.ZeroDensity.Jutila.kap t / (t : ℝ)
      = ∏ p ∈ t.primeFactors, ((p : ℝ) + 1) / (p : ℝ) := by
  have hprod : (∏ p ∈ t.primeFactors, (p : ℝ)) = (t : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree ht]
  rw [Finset.prod_div_distrib, hprod]
  simp [Work.ZeroDensity.Jutila.kap]

end Work.ZeroDensity.Jutila.BzCross
