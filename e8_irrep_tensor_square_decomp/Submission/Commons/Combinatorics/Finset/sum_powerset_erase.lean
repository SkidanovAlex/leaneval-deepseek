import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset

namespace Commons.Combinatorics.Finset

open scoped BigOperators

/-- Sum over `(a, t)` with `a ∈ s` and `t ⊆ s.erase a` equals the sum over `(T, a)` with
`T ⊆ s` and `a ∈ T`, via the bijection `(a,t) ↦ (insert a t, a)` (inverse `(T,a) ↦ (a, T.erase a)`). -/
theorem sum_powerset_erase {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    (s : Finset α) (f : α → Finset α → β) :
    (∑ a ∈ s, ∑ t ∈ (s.erase a).powerset, f a t)
      = ∑ T ∈ s.powerset, ∑ a ∈ T, f a (T.erase a) := by
  rw [Finset.sum_sigma' s (fun a => (s.erase a).powerset) f,
      Finset.sum_sigma' s.powerset (fun T => T) (fun T a => f a (T.erase a))]
  refine Finset.sum_nbij'
    (fun x => (⟨insert x.1 x.2, x.1⟩ : (T : Finset α) × α))
    (fun y => (⟨y.2, y.1.erase y.2⟩ : (a : α) × Finset α)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, t⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨ha, ht⟩ := hx
    rw [Finset.mem_powerset] at ht
    rw [Finset.mem_sigma, Finset.mem_powerset]
    refine ⟨fun x hx' => ?_, Finset.mem_insert_self a t⟩
    rcases Finset.mem_insert.mp hx' with rfl | hxt
    · exact ha
    · exact Finset.mem_of_mem_erase (ht hxt)
  · rintro ⟨T, a⟩ hy
    rw [Finset.mem_sigma] at hy
    obtain ⟨hT, haT⟩ := hy
    rw [Finset.mem_powerset] at hT
    rw [Finset.mem_sigma, Finset.mem_powerset]
    exact ⟨hT haT, Finset.erase_subset_erase a hT⟩
  · rintro ⟨a, t⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨ha, ht⟩ := hx
    rw [Finset.mem_powerset] at ht
    simp only
    rw [Finset.erase_insert (fun h => Finset.notMem_erase a s (ht h))]
  · rintro ⟨T, a⟩ hy
    rw [Finset.mem_sigma] at hy
    obtain ⟨hT, haT⟩ := hy
    simp only
    rw [Finset.insert_erase haT]
  · rintro ⟨a, t⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨ha, ht⟩ := hx
    rw [Finset.mem_powerset] at ht
    simp only
    rw [Finset.erase_insert (fun h => Finset.notMem_erase a s (ht h))]

end Commons.Combinatorics.Finset