import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Interval.Finset.Fin

namespace Commons.Data.Fin

open scoped BigOperators
set_option autoImplicit false

lemma pairFilter_snd {N : ℕ} {α : Type*} [AddCommMonoid α] (k : Fin N) (f : Fin N → Fin N → α) :
    (∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)).filter
      (fun p => p.2 = k), f p.1 p.2) = ∑ i ∈ Finset.Iio k, f i k := by
  refine Finset.sum_bij (s := (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)).filter
      (fun p => p.2 = k)) (t := Finset.Iio k)
    (f := fun p : Fin N × Fin N => f p.1 p.2) (g := fun i : Fin N => f i k)
    (fun p _ => p.1) ?_ ?_ ?_ ?_
  · intro p hp
    -- hp : p ∈ ((univ.filter fun p => p.1 < p.2).filter fun p => p.2 = k)
    have hP2 : p.2 = k := (Finset.mem_filter.mp hp).2
    have hP1 : p.1 < p.2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    rw [Finset.mem_Iio]
    rwa [hP2] at hP1
  · intro p hp q hq hpq
    apply Prod.ext
    · exact hpq
    · have hP2p : p.2 = k := (Finset.mem_filter.mp hp).2
      have hP2q : q.2 = k := (Finset.mem_filter.mp hq).2
      rw [hP2p, hP2q]
  · intro b hb
    refine ⟨(b, k), ?_, rfl⟩
    rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_univ (b, k)
      · exact Finset.mem_Iio.mp hb
    · rfl
  · intro p hp
    rw [(Finset.mem_filter.mp hp).2]

end Commons.Data.Fin