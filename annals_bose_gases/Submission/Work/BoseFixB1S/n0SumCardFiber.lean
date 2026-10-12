import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

/-- Regroup a sum over all finite subsets of `Fin N` by the cardinality of the subset:
`∑ S, |S| * φ S = ∑ k ≤ N, k * ∑_{|S| = k} φ S`. -/
theorem n0SumCardFiber {N : ℕ} (φ : Finset (Fin N) → ℝ) :
    (∑ S : Finset (Fin N), (S.card : ℝ) * φ S)
      = ∑ k ∈ Finset.range (N + 1),
          (k : ℝ) * (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) => S.card = k), φ S) := by
  have hcard : ∀ S ∈ (Finset.univ : Finset (Finset (Fin N))), S.card ∈ Finset.range (N + 1) := by
    intro S _
    rw [Finset.mem_range]
    have h1 : S.card ≤ (Finset.univ : Finset (Fin N)).card :=
      Finset.card_le_card (Finset.subset_univ S)
    rw [Finset.card_univ, Fintype.card_fin] at h1
    exact Nat.lt_succ_of_le h1
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.range (N + 1))
        (g := fun S : Finset (Fin N) => S.card) (f := fun S => (S.card : ℝ) * φ S) hcard]
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro S hS
  rw [Finset.mem_filter] at hS
  rw [hS.2]

end Work.BoseFixB1S
