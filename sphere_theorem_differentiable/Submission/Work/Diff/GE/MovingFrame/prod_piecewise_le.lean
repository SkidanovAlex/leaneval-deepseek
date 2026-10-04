import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE.MovingFrame

open scoped BigOperators

/-- Product bound for a `Finset.piecewise` mixture.  In Mathlib `s.piecewise δ u` is `δ` **on** `s`
and `u` off `s` (`piecewise_eq_of_mem`).  If `s` is nonempty, `u` is bounded by `M` and `δ` by
`c ≤ M` (with `M ≥ 0`), then the product of the norms of the five entries is at most `M^4 * c`:
one entry is a `δ`-entry contributing `c`, the remaining four are at least... at most `M`.
Used to bound the higher-order terms in the expansion `f (δ + u) = ∑_{s} f (s.piecewise δ u)` of a
multilinear form when `δ → 0`. -/
theorem prod_piecewise_le
    {V : Type*} [NormedAddCommGroup V]
    (u δ : Fin 5 → V) (s : Finset (Fin 5)) (hs : s.Nonempty) {M c : ℝ}
    (hM0 : 0 ≤ M) (hcM : c ≤ M) (hM : ∀ i, ‖u i‖ ≤ M) (hc : ∀ i, ‖δ i‖ ≤ c) :
    ∏ i, ‖s.piecewise δ u i‖ ≤ M ^ 4 * c := by
  -- `M` is only used through `c ≤ M` and the nonnegativity of `c`; record it to keep the binder alive.
  have _hM0 : (0 : ℝ) ≤ M := hM0
  let f : Fin 5 → ℝ := fun i => ‖s.piecewise δ u i‖
  -- Pick a `δ`-entry: `s` is nonempty.
  obtain ⟨i0, hi0⟩ := hs
  -- Then `0 ≤ c`, since `‖δ i0‖ ≤ c`.
  have hc0 : 0 ≤ c := le_trans (norm_nonneg _) (hc i0)
  -- The distinguished factor is bounded by `c`.
  have hmem : f i0 ≤ c := by
    show ‖s.piecewise δ u i0‖ ≤ c
    rw [Finset.piecewise_eq_of_mem s δ u hi0]
    exact hc i0
  -- Every other factor is bounded by `M`: on `s` it is a `δ`-entry (`≤ c ≤ M`), off `s` a `u`-entry.
  have hrest : ∀ i, i ≠ i0 → f i ≤ M := by
    intro i hi
    show ‖s.piecewise δ u i‖ ≤ M
    by_cases h : i ∈ s
    · rw [Finset.piecewise_eq_of_mem s δ u h]
      exact le_trans (hc i) hcM
    · rw [Finset.piecewise_eq_of_notMem s δ u h]
      exact hM i
  -- The four remaining factors multiply to at most `M ^ 4`.
  have hcard : (Finset.univ.erase i0 : Finset (Fin 5)).card = 4 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i0), Finset.card_univ, Fintype.card_fin]
  have hprod : ∏ i ∈ Finset.univ.erase i0, f i ≤ M ^ 4 := by
    calc ∏ i ∈ Finset.univ.erase i0, f i
        ≤ ∏ i ∈ Finset.univ.erase i0, (M : ℝ) :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
            (fun i hi => hrest i (Finset.mem_erase.mp hi).1)
      _ = M ^ 4 := by rw [Finset.prod_const, hcard]
  have hnonneg : 0 ≤ ∏ i ∈ Finset.univ.erase i0, f i :=
    Finset.prod_nonneg (fun i _ => norm_nonneg _)
  -- Split off the distinguished factor and combine.
  calc ∏ i : Fin 5, f i
      = f i0 * ∏ i ∈ Finset.univ.erase i0, f i :=
        (Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i0)).symm
    _ ≤ c * M ^ 4 := mul_le_mul hmem hprod hnonneg hc0
    _ = M ^ 4 * c := by ring

end Work.Diff.GE.MovingFrame
