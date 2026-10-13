import Mathlib
import Submission.Work.DSM5b.honestVanishingDefs

universe a

namespace Work.DSM5b

/-- Combinatorial core of the block vanishing.  If `S` has `j` elements and the range of `τ` has at
most `j` elements but is *not* `S`, then for every `i` the range of `τ` with the `i`-th entry deleted
is still not `S`: it is contained in `tupRng τ`, and a subset of `tupRng τ` cannot equal `S` because
`S` is neither strictly larger in cardinality nor equal to `tupRng τ`. -/
lemma tupRng_tupDel_ne_of_card_le {ι : Type a} [DecidableEq ι] {m j : ℕ} {S : Finset ι}
    {τ : Fin (m + 2) → ι} (hS : S.card = j) (hτ : (tupRng τ).card ≤ j) (hne : tupRng τ ≠ S)
    (i : Fin (m + 2)) : tupRng (tupDel i τ) ≠ S := by
  intro heq
  have hsub : S ⊆ tupRng τ := heq ▸ tupRng_del_subset i τ
  have hle : (tupRng τ).card ≤ S.card := le_trans hτ (le_of_eq hS.symm)
  exact hne (Finset.eq_of_subset_of_card_le hsub hle).symm

lemma HCd_block_vanishing {ι : Type a} [DecidableEq ι] {R : Type a} [CommRing R] (t : ι → R)
    {j m : ℕ} {y : HCX t m} {S : Finset ι} (hS : S.card = j)
    (hy : ∀ σ : Fin (m + 1) → ι, tupRng σ ≠ S → y σ = 0)
    {τ : Fin (m + 2) → ι} (hτ : (tupRng τ).card ≤ j) (hne : tupRng τ ≠ S) :
    HCd t m y τ = 0 := by
  rw [HCd_apply]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [hy (tupDel i τ) (tupRng_tupDel_ne_of_card_le hS hτ hne i), map_zero, smul_zero]

end Work.DSM5b
