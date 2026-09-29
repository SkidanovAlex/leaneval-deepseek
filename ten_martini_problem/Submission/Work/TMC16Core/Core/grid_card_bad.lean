import Mathlib
import Submission.Work.TMC16Core.Basic.nnDist
import Submission.Work.TMC16Core.Core.grid_count

/-!
# The "bad grid" cardinality estimate (`grid_card_bad`)

For `q > 0`, `p : ℤ` coprime to `q`, real `x`, `0 ≤ γ ≤ 1/2` and `k₁ ∈ {1,…,q}`, the number of
`k ∈ {1,…,q} \ {k₁}` with `nn (2x + k·(p/q)) < γ` is at most `2 γ q + 2`.

The mathematics is entirely contained in
`Work.TMC16Core.Core.grid_count` (already proved in this workspace): the map `k ↦ k*p mod q`
identifies the `q` points `2x + k·(p/q)` with the `q` grid points `2x + j/q`, `j < q`, which
are `1/q`-separated, so at most `2γq + 2` of them can lie within distance `γ` of an integer.
Removing `k₁` can only decrease the count, which gives the stated bound; for `γ = 0` the
filtered set is empty since `nn ≥ 0`.
-/

namespace Work.TMC16Core.Core

theorem grid_card_bad {q : ℕ} (hq : 0 < q) {p : ℤ} (hcop : Nat.Coprime p.natAbs q)
    (x γ : ℝ) (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 2) {k₁ : ℕ} (hk₁ : k₁ ∈ Finset.Icc 1 q) :
    ((((Finset.Icc 1 q).erase k₁).filter
        (fun k : ℕ => Work.TMC16Core.Basic.nn (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) < γ)).card : ℝ)
      ≤ 2 * γ * (q : ℝ) + 2 := by
  classical
  rcases lt_or_eq_of_le hγ0 with hγpos | hγzero
  · -- `γ > 0`: erase only removes points, and `grid_count` bounds the full grid
    have hsub : ((Finset.Icc 1 q).erase k₁).filter
          (fun k : ℕ => Work.TMC16Core.Basic.nn (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) < γ)
        ⊆ (Finset.Icc 1 q).filter
          (fun k : ℕ => Work.TMC16Core.Basic.nn (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) < γ) :=
      Finset.filter_subset_filter _ (Finset.erase_subset k₁ _)
    calc ((((Finset.Icc 1 q).erase k₁).filter
          (fun k : ℕ => Work.TMC16Core.Basic.nn (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) < γ)).card : ℝ)
        ≤ (((Finset.Icc 1 q).filter
          (fun k : ℕ => Work.TMC16Core.Basic.nn (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) < γ)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ 2 * (q : ℝ) * γ + 2 := grid_count hq hcop x γ hγpos
      _ = 2 * γ * (q : ℝ) + 2 := by ring
  · -- `γ = 0`: the filter is empty because `nn ≥ 0`
    rw [← hγzero]
    have hempty : ((Finset.Icc 1 q).erase k₁).filter
        (fun k : ℕ => Work.TMC16Core.Basic.nn (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) < (0 : ℝ)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro k _
      exact not_lt.mpr (Work.TMC16Core.Basic.nn_nonneg _)
    rw [hempty]
    simp

end Work.TMC16Core.Core
