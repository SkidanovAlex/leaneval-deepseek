import Mathlib

namespace Work.Q44Geom

/-- Two submodules `L`, `M` of `ℤ^5` containing a common submodule `N` and generated
modulo `N` by `z` and `y` respectively are equal, provided `z ≡ y (mod N)`. -/
theorem eq_of_coset_eq {N L M : Submodule ℤ (Fin 5 → ℤ)} {z y : Fin 5 → ℤ}
    (hNL : N ≤ L) (hNM : N ≤ M)
    (hgenL : ∀ w ∈ L, ∃ k : ℤ, ∃ n ∈ N, w = k • z + n)
    (hgenM : ∀ w ∈ M, ∃ k : ℤ, ∃ n ∈ N, w = k • y + n)
    (hz : z ∈ L) (hy : y ∈ M) (hzy : z - y ∈ N) : L = M := by
  apply le_antisymm
  · -- `L ≤ M`: from `z = y + (z - y)` with `y ∈ M`, `z - y ∈ N ≤ M`.
    intro w hw
    obtain ⟨k, n, hn, rfl⟩ := hgenL w hw
    have hzM : z ∈ M := by
      have h1 : z = y + (z - y) := by abel
      rw [h1]
      exact M.add_mem hy (hNM hzy)
    exact M.add_mem (M.smul_mem k hzM) (hNM hn)
  · -- `M ≤ L`: from `y = z - (z - y)` with `z ∈ L`, `z - y ∈ N ≤ L`.
    intro w hw
    obtain ⟨k, n, hn, rfl⟩ := hgenM w hw
    have hyL : y ∈ L := by
      have h1 : y = z - (z - y) := by abel
      rw [h1]
      exact L.sub_mem hz (hNL hzy)
    exact L.add_mem (L.smul_mem k hyL) (hNL hn)

end Work.Q44Geom
