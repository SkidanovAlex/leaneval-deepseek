import Mathlib
import Submission.Work.Peluse.SwapC.concatCore

namespace Work.Peluse.SwapC

open Work.Peluse

/-- `weight` is the number of `true` entries, written as a sum of indicators. -/
private lemma weight_eq_sum {t : ℕ} (ω : Fin t → Bool) :
    weight ω = ∑ i : Fin t, (if ω i = true then 1 else 0 : ℕ) := by
  simp only [weight, Finset.card_filter]

/-- Splitting a sign pattern into its two halves splits the weight: the first `m` slots and the
last `n` slots of `Fin (m + n)`. -/
private lemma weight_split_general (m n : ℕ) (ω : Fin (m + n) → Bool) :
    weight ω = weight (fun j : Fin m => ω (Fin.castAdd n j))
      + weight (fun j : Fin n => ω (Fin.natAdd m j)) := by
  rw [weight_eq_sum, weight_eq_sum, weight_eq_sum, Fin.sum_univ_add]

/-- `weight` is invariant under relabelling the index type along an equality of lengths. -/
private lemma weight_cast {m n : ℕ} (h : m = n) (ω : Fin n → Bool) :
    weight (fun i : Fin m => ω (Fin.cast h i)) = weight ω := by
  cases h
  rfl

theorem weightSplit (s : ℕ) (ω : Fin (2 * s) → Bool) :
    Work.Peluse.weight ω = Work.Peluse.weight (Work.Peluse.SwapC.cL s ω)
      + Work.Peluse.weight (Work.Peluse.SwapC.cR s ω) := by
  have hcast : (s + s) = 2 * s := (Nat.two_mul s).symm
  have key := weight_split_general s s (fun i : Fin (s + s) => ω (Fin.cast hcast i))
  rw [weight_cast hcast ω] at key
  have hL : (fun j : Fin s => ω (Fin.cast hcast (Fin.castAdd s j))) = cL s ω := by
    funext j
    simp only [cL]
    congr 1
  have hR : (fun j : Fin s => ω (Fin.cast hcast (Fin.natAdd s j))) = cR s ω := by
    funext j
    simp only [cR]
    congr 1
  rw [hL, hR] at key
  exact key

end Work.Peluse.SwapC
