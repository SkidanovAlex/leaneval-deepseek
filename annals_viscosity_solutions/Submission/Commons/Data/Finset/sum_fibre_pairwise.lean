import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Fin

namespace Commons.Data.Finset

theorem sum_fibre_pairwise {K N : ℕ} {M : Type*} [AddCommMonoid M]
    (jj : Fin N → Fin K) (f : Fin N → Fin N → M) :
    (∑ j : Fin K, ∑ k ∈ Finset.univ.filter (fun k => jj k = j),
        ∑ i ∈ (Finset.univ.filter (fun i => jj i = j)).filter (fun i => i < k), f i k)
      = ∑ k : Fin N, ∑ i ∈ (Finset.Iio k).filter (fun i => jj i = jj k), f i k := by
  classical
  have key : ∀ (k : Fin N) (j : Fin K), jj k = j →
      (∑ i ∈ (Finset.univ.filter (fun i => jj i = j)).filter (fun i => i < k), f i k)
        = ∑ i ∈ (Finset.Iio k).filter (fun i => jj i = jj k), f i k := by
    intro k j hk
    have hset : (Finset.univ.filter (fun i => jj i = jj k)).filter (fun i => i < k)
        = (Finset.Iio k).filter (fun i => jj i = jj k) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
      exact and_comm ..
    rw [← hk]
    exact Finset.sum_congr hset (fun _ _ => rfl)
  calc
    (∑ j : Fin K, ∑ k ∈ Finset.univ.filter (fun k => jj k = j),
        ∑ i ∈ (Finset.univ.filter (fun i => jj i = j)).filter (fun i => i < k), f i k)
        = ∑ j : Fin K, ∑ k ∈ Finset.univ.filter (fun k => jj k = j),
            ∑ i ∈ (Finset.Iio k).filter (fun i => jj i = jj k), f i k := by
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k hk
          exact key k j (Finset.mem_filter.mp hk).2
      _ = ∑ k : Fin N, ∑ i ∈ (Finset.Iio k).filter (fun i => jj i = jj k), f i k := by
          rw [Finset.sum_fiberwise]

end Commons.Data.Finset