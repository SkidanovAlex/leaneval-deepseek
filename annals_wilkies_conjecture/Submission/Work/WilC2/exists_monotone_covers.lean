/-
  WilC2 : enumerating a finite set of reals by a monotone sequence of prescribed length.

  Every finite set `Z ⊆ ℝ` with `Z.card ≤ K` is contained in the range of a monotone map
  `Fin K → ℝ`: order `Z` increasingly via `Finset.orderEmbOfFin` and then pad the remaining
  values by repeating the maximum of `Z` (i.e. the last value of the enumeration).
-/
import Mathlib

namespace Work.WilC2

theorem exists_monotone_covers {K : ℕ} {Z : Finset ℝ} (h : Z.card ≤ K) :
    ∃ y : Fin K → ℝ, Monotone y ∧ ∀ x ∈ Z, ∃ i : Fin K, y i = x := by
  by_cases hZ : Z = ∅
  · -- `Z` is empty: any constant map works.
    refine ⟨fun _ => 0, fun _ _ _ => le_refl 0, ?_⟩
    intro x hx
    rw [hZ] at hx
    exact absurd hx (Finset.notMem_empty x)
  · have hzpos : 0 < Z.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hZ)
    -- `g i` is the index in the increasing enumeration of `Z` given to `i`, clamped to
    -- `Z.card - 1` so that the surplus indices repeat the maximum of `Z`.
    let g : Fin K → Fin Z.card := fun i =>
      ⟨min (i : ℕ) (Z.card - 1),
        lt_of_le_of_lt (min_le_right _ _) (by omega)⟩
    have hgval : ∀ i : Fin K, (g i : ℕ) = min (i : ℕ) (Z.card - 1) := fun i => rfl
    have hgmono : Monotone g := by
      intro i j hij
      refine Fin.le_def.mpr ?_
      rw [hgval i, hgval j]
      exact min_le_min (Fin.le_def.mp hij) le_rfl
    refine ⟨fun i => Z.orderEmbOfFin rfl (g i), ?_, ?_⟩
    · -- monotonicity: the increasing enumeration composed with the monotone `g`
      intro i j hij
      exact (Z.orderEmbOfFin rfl).monotone (hgmono hij)
    · -- covering: every `x ∈ Z` is the `j`-th element of the enumeration
      intro x hx
      have hxr : x ∈ Set.range (Z.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        exact hx
      obtain ⟨j, hj⟩ := hxr
      refine ⟨⟨(j : ℕ), lt_of_lt_of_le j.isLt h⟩, ?_⟩
      show Z.orderEmbOfFin rfl (g ⟨(j : ℕ), lt_of_lt_of_le j.isLt h⟩) = x
      have hgi : g ⟨(j : ℕ), lt_of_lt_of_le j.isLt h⟩ = j := by
        refine Fin.ext ?_
        show min (j : ℕ) (Z.card - 1) = (j : ℕ)
        exact min_eq_left (by have := j.isLt; omega)
      rw [hgi, hj]

end Work.WilC2
