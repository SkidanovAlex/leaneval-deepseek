import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

namespace Commons.Combinatorics.Finset

open _root_.Finset
open scoped BigOperators

/-- A double sum over the increasing pairs of `Fin a`, transported along an order embedding
`e : Fin a ↪o Fin m`, is dominated by the double sum over all increasing pairs of `Fin m`
(the transported pairs form a subset of the increasing pairs, and all terms are nonnegative). -/
theorem sum_pairs_le_of_orderEmb {a m : ℕ} (e : Fin a ↪o Fin m) (F : Fin m → Fin m → ℝ)
    (hF : ∀ i j, 0 ≤ F i j) :
    ∑ k : Fin a, ∑ k' ∈ Finset.univ.filter (fun k' => k < k'), F (e k) (e k')
      ≤ ∑ i : Fin m, ∑ j ∈ Finset.univ.filter (fun j => i < j), F i j := by
  set row : Fin m → ℝ := fun i => ∑ j ∈ Finset.univ.filter (fun j => i < j), F i j with hrow
  have hstep : ∀ k : Fin a,
      (∑ k' ∈ Finset.univ.filter (fun k' => k < k'), F (e k) (e k')) ≤ row (e k) := by
    intro k
    have hsub : (Finset.univ.filter (fun k' => k < k')).image e
        ⊆ Finset.univ.filter (fun j => e k < j) := by
      intro j hj
      rcases Finset.mem_image.mp hj with ⟨k', hk', rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk' ⊢
      exact (e.lt_iff_lt).mpr hk'
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg (f := fun j => F (e k) j) hsub
      (fun j _ _ => hF (e k) j)
    have h2 : (∑ j ∈ (Finset.univ.filter (fun k' => k < k')).image e, F (e k) j)
        = ∑ k' ∈ Finset.univ.filter (fun k' => k < k'), F (e k) (e k') :=
      Finset.sum_image (f := fun j => F (e k) j) (s := Finset.univ.filter (fun k' => k < k'))
        (g := e) (fun x _ y _ h => e.injective h)
    rw [hrow]; simp only
    rw [h2] at h1
    exact h1
  have hmap : (∑ i ∈ (Finset.univ : Finset (Fin a)).image e, row i) = ∑ k : Fin a, row (e k) :=
    Finset.sum_image (f := row) (s := Finset.univ) (g := e) (fun x _ y _ h => e.injective h)
  calc ∑ k : Fin a, ∑ k' ∈ Finset.univ.filter (fun k' => k < k'), F (e k) (e k')
      ≤ ∑ k : Fin a, row (e k) := Finset.sum_le_sum (fun k _ => hstep k)
    _ = ∑ i ∈ (Finset.univ : Finset (Fin a)).image e, row i := hmap.symm
    _ ≤ ∑ i : Fin m, row i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (f := row)
        · exact Finset.subset_univ _
        · intro i _ _
          rw [hrow]; simp only
          exact Finset.sum_nonneg (fun j _ => hF i j)

end Commons.Combinatorics.Finset