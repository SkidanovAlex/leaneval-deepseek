import Mathlib

namespace Work.WilE9G.Assembly

/-- A set of Lebesgue measure zero in `ℝ^k` (`k ≥ 1`) is a proper subset of the whole space:
it cannot exhaust `Fin k → ℝ`, since the unit cube has volume `1 ≠ 0`.

The hypothesis `0 < k` is not needed for the argument (the unit cube has volume `1` for
every `k`), but is kept because the requested statement carries it. -/
theorem exists_notMem_of_volume_zero {k : ℕ} (hk : 0 < k) (N : Set (Fin k → ℝ))
    (hN : MeasureTheory.volume N = 0) : ∃ x, x ∉ N := by
  -- `hk` is not needed; mention it to keep the binder used.
  have _hk : 0 < k := hk
  by_contra h
  -- `h : ¬ ∃ x, x ∉ N`, so every point of `ℝ^k` lies in `N`, i.e. `N = univ`.
  have hmem : ∀ x, x ∈ N := by simpa using not_exists.mp h
  -- Hence the unit cube, being contained in `N`, must have measure zero ...
  have hsub : Set.Icc (0 : Fin k → ℝ) (1 : Fin k → ℝ) ⊆ N := fun x _ => hmem x
  have h0 : MeasureTheory.volume (Set.Icc (0 : Fin k → ℝ) (1 : Fin k → ℝ)) = 0 :=
    MeasureTheory.measure_mono_null hsub hN
  -- ... but its volume is `∏ i, ofReal (1 - 0) = 1`, a contradiction.
  rw [Real.volume_Icc_pi] at h0
  simp at h0

end Work.WilE9G.Assembly
