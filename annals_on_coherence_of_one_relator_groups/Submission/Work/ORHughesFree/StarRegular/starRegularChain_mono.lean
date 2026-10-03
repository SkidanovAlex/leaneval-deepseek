import Mathlib
import Submission.Work.ORHughesFree.StarRegular

namespace Work.ORHughesFree.StarRegular

open Work.ORHughesFree

/-- One step of the approximating chain: `Rₙ ⊆ Rₙ₊₁`. -/
theorem starRegularChain_le_succ {U : Type*} [Ring U] [StarRing U] (R : StarSubring U) (n : ℕ) :
    (starRegularChain R n : Set U) ⊆ (starRegularChain R (n + 1) : Set U) := by
  intro x hx
  exact subset_starSubringClosure _ (Or.inl hx)

theorem starRegularChain_mono {U : Type*} [Ring U] [StarRing U] (R : StarSubring U) {m n : ℕ}
    (h : m ≤ n) : (starRegularChain R m : Set U) ⊆ (starRegularChain R n : Set U) :=
  monotone_nat_of_le_succ (fun k => starRegularChain_le_succ R k) h

end Work.ORHughesFree.StarRegular
