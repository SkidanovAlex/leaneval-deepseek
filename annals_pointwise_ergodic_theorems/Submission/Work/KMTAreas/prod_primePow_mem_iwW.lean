import Mathlib
import Submission.Work.Analysis.IonescuWainger.Pset

namespace Work.KMTAreas

theorem prod_primePow_mem_iwW {ρ : ℝ} {l : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Work.Analysis.IonescuWainger.iwPrimeRange ρ l)
    (hcard : S.card ≤ Work.Analysis.IonescuWainger.iwD ρ) :
    S.prod (fun p => p ^ Work.Analysis.IonescuWainger.iwD ρ) ∈ Work.Analysis.IonescuWainger.iwW ρ l := by
  rw [Work.Analysis.IonescuWainger.mem_iwW]
  have hD : Work.Analysis.IonescuWainger.iwD ρ ≠ 0 := by
    rw [Work.Analysis.IonescuWainger.iwD]; exact Nat.succ_ne_zero _
  have hpr : ∀ p ∈ S, Nat.Prime p := fun p hp => (Finset.mem_filter.mp (hS hp)).2
  have hprod : S.prod (fun p => p ^ Work.Analysis.IonescuWainger.iwD ρ)
      = (S.prod fun p => p) ^ Work.Analysis.IonescuWainger.iwD ρ := Finset.prod_pow S _ _
  refine ⟨Finset.prod_dvd_prod_of_subset S (Work.Analysis.IonescuWainger.iwPrimeRange ρ l)
      (fun p => p ^ Work.Analysis.IonescuWainger.iwD ρ) hS, ?_⟩
  rw [hprod, Nat.support_factorization, Nat.primeFactors_pow _ hD, Nat.primeFactors_prod hpr]
  exact hcard

end Work.KMTAreas
