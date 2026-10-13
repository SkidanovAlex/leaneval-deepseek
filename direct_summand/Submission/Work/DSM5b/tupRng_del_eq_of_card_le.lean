import Mathlib
import Submission.Work.DSM5b.honestVanishingDefs

namespace Work.DSM5b

universe a

lemma tupRng_del_eq_of_card_le {ι : Type a} [DecidableEq ι] {m j : ℕ} {τ : Fin (m + 2) → ι}
    (hτ : (tupRng τ).card ≤ j) {S : Finset ι} (hS : S.card = j) (i : Fin (m + 2))
    (h : tupRng (tupDel i τ) = S) : tupRng τ = S := by
  have hsub : S ⊆ tupRng τ := by
    rw [← h]
    exact tupRng_del_subset i τ
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hS]; exact hτ)).symm

end Work.DSM5b
