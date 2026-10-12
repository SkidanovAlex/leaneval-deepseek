import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Star
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Interval.Finset.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs3.MatLoc.Interval` — ℤ-interval sum bookkeeping

Elementary reindexing lemmas for sums over `Finset.Icc a b ⊆ ℤ`, used throughout the
Lieb–Solovej localisation (the index set is `ℤ` and the profile is translated).

* `sum_Icc_shift` — translation invariance `Σ_{t∈[a-k,b-k]} f(t+k) = Σ_{t∈[a,b]} f t`;
* `sum_Icc_congr_of_eq_zero_outside` — a sum over a larger interval equals the sum over a
  smaller one when the summand vanishes outside the smaller one.
-/

noncomputable section

open scoped BigOperators
open Finset

namespace Work.UBBInputs3

/-- **Translating an interval sum.** `Σ_{t ∈ [a-k, b-k]} f (t+k) = Σ_{t ∈ [a,b]} f t`. -/
theorem sum_Icc_shift {M : Type*} [AddCommMonoid M] (f : ℤ → M) (a b k : ℤ) :
    ∑ t ∈ Finset.Icc (a - k) (b - k), f (t + k) = ∑ t ∈ Finset.Icc a b, f t := by
  have h1 : ∑ t ∈ Finset.Icc (a - k) (b - k), f (t + k)
      = ∑ t ∈ (Finset.Icc (a - k) (b - k)).map (addRightEmbedding k), f t := by
    rw [Finset.sum_map]
    exact Finset.sum_congr rfl (fun x _ => by simp [addRightEmbedding])
  rw [h1, Finset.map_add_right_Icc]
  simp only [sub_add_cancel]

/-- **A sum over a larger interval with a summand vanishing outside a smaller one.** -/
theorem sum_Icc_congr_of_eq_zero_outside {M : Type*} [AddCommMonoid M] (f : ℤ → M)
    {a b c d : ℤ} (hac : a ≤ c) (hdb : d ≤ b)
    (hf : ∀ t, t ∉ Finset.Icc c d → f t = 0) :
    ∑ t ∈ Finset.Icc a b, f t = ∑ t ∈ Finset.Icc c d, f t := by
  have hsub : Finset.Icc c d ⊆ Finset.Icc a b := by
    intro t ht
    simp only [Finset.mem_Icc] at ht ⊢
    exact ⟨le_trans hac ht.1, le_trans ht.2 hdb⟩
  exact (Finset.sum_subset hsub (fun t _ htc => hf t htc)).symm

end Work.UBBInputs3
