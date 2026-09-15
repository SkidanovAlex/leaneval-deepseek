import Mathlib.Data.Fintype.BigOperators

namespace Commons.Combinatorics.Finset

/-- The fiber over `i : Fin d` of the map "evaluate at `i`" is equivalent to the
functions on the complement of `i`. -/
private def fiberEquiv (d : ℕ) (i : Fin d) :
    {ω : Fin d → Bool // ω i = false} ≃ ({j : Fin d // j ≠ i} → Bool) where
  toFun ω := fun j => ω.1 j.1
  invFun g := ⟨fun j => if h : j = i then false else g ⟨j, h⟩, by simp⟩
  left_inv ω := by
    ext j
    by_cases h : j = i
    · subst h; simp [ω.2]
    · simp [h]
  right_inv g := by
    ext j
    simp [j.2]

/-- The complement of a point in `Fin d` has `d - 1` elements. -/
private theorem card_ne (d : ℕ) (i : Fin d) :
    Fintype.card {j : Fin d // j ≠ i} = d - 1 := by
  rw [Fintype.card_subtype]
  have hf : (Finset.univ.filter (fun j : Fin d => j ≠ i)) = Finset.univ.erase i := by
    ext j; simp [Finset.mem_filter, Finset.mem_erase]
  rw [hf, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]

/-- The number of Boolean functions on `Fin d` that vanish at a fixed point is `2 ^ (d - 1)`. -/
private theorem card_fiber (d : ℕ) (i : Fin d) :
    Fintype.card {ω : Fin d → Bool // ω i = false} = 2 ^ (d - 1) := by
  rw [Fintype.card_congr (fiberEquiv d i), Fintype.card_fun, card_ne d i, Fintype.card_bool]

/-- The number of pairs `(i, ω)` with `i : Fin d` and `ω : Fin d → Bool` a Boolean function
with `ω i = false` equals `d * 2 ^ (d - 1)`. -/
theorem card_sigma_bool_false {d : ℕ} :
    Fintype.card (Σ i : Fin d, {ω : Fin d → Bool // ω i = false}) = d * 2 ^ (d - 1) := by
  rw [Fintype.card_sigma]
  simp_rw [card_fiber]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

end Commons.Combinatorics.Finset