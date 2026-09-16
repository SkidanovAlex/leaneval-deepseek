import Mathlib.Algebra.BigOperators.Fin

namespace Commons.Data.Fin

theorem prod_split_head {M : Type*} [CommMonoid M] {r : ℕ} (hr : 0 < r)
    (g : Fin r → M) :
    (∏ i : Fin r, g i) = g ⟨0, hr⟩ * ∏ j : Fin (r - 1), g ⟨j.1 + 1, by omega⟩ := by
  have hsucc : (r - 1) + 1 = r := by omega
  calc
    (∏ i : Fin r, g i) = ∏ j : Fin ((r - 1) + 1), g (finCongr hsucc j) := by
      rw [← Equiv.prod_comp (finCongr hsucc) g]
    _ = g (finCongr hsucc (0 : Fin ((r - 1) + 1))) *
          ∏ j : Fin (r - 1), g (finCongr hsucc j.succ) := by
      rw [Fin.prod_univ_succ]
    _ = g ⟨0, hr⟩ * ∏ j : Fin (r - 1), g ⟨j.1 + 1, by omega⟩ := by
      congr 2

end Commons.Data.Fin