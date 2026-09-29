import Mathlib
import Submission.Work.Holonomy3.siegelDefs
import Submission.Work.Holonomy3.lowdiscCells
import Submission.Work.Holonomy3.cell_biUnion_measure

namespace Work.Holonomy3

open Submission.CDT.Discrepancy
open MeasureTheory

/-- **Counting bound from grid cells.**  Let `D > 0`, `ε > 0`, and let `S` be a finset of exponent
vectors `k : Fin d → ℕ` with all coordinates `≤ D - 1`, so that the cells
`cell d D k = ∏_j [k_j/D, (k_j+1)/D)` all lie in `[0,1)^d`.  If every cell attached to an element of
`S` is contained in the tail event `{u | ε ≤ disc u}`, then

`#S ≤ D^d · 100 exp (-d ε⁴/100)`.

Route: cells of distinct `k` are pairwise disjoint and each has `(muP d)`-measure `D^{-d}` (product
measure of half-open intervals of equal length `1/D`; see `Work.Holonomy3.cell_biUnion_measure`), so
`#S · D^{-d} = (muP d).real (⋃ k ∈ S, cell d D k) ≤ (muP d).real {u | ε ≤ disc u}`, which
`Submission.CDT.Discrepancy.disc_concentration_four` bounds by `100 exp (-d ε⁴/100)`.  Multiplying by
`D^d` gives the claim. -/
theorem card_le_of_cells {d : ℕ} (hd : 0 < d) {D : ℕ} (hD : 0 < D) {ε : ℝ} (hε : 0 < ε)
    (S : Finset (Fin d → ℕ)) (hS : ∀ k ∈ S, ∀ j, k j ≤ D - 1)
    (hsub : ∀ k ∈ S, Work.Holonomy3.cell d D k ⊆ {u : Fin d → ℝ | ε ≤ Submission.CDT.Discrepancy.disc u}) :
    (S.card : ℝ) ≤ (D : ℝ) ^ d * (100 * Real.exp (-(d : ℝ) * ε ^ 4 / 100)) := by
  classical
  -- every exponent vector of `S` has all coordinates `< D`
  have hlt : ∀ k ∈ S, ∀ j, k j < D := by
    intro k hk j
    have := hS k hk j
    omega
  -- the union of the cells lies in the tail event
  have hmono : (muP d).real (⋃ k ∈ S, Work.Holonomy3.cell d D k) ≤
      (muP d).real {u : Fin d → ℝ | ε ≤ Submission.CDT.Discrepancy.disc u} := by
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro u hu
    simp only [Set.mem_iUnion] at hu
    obtain ⟨k, hk, hku⟩ := hu
    exact hsub k hk hku
  -- its measure is `#S · D^{-d}`
  have hmeas : (muP d).real (⋃ k ∈ S, Work.Holonomy3.cell d D k) =
      (S.card : ℝ) * ((D : ℝ) ^ d)⁻¹ :=
    cell_biUnion_measure hd D hD S hlt
  -- the concentration bound on the tail event
  have hconc : (muP d).real {u : Fin d → ℝ | ε ≤ Submission.CDT.Discrepancy.disc u} ≤
      100 * Real.exp (-(d : ℝ) * ε ^ 4 / 100) :=
    disc_concentration_four (by omega) hε
  rw [hmeas] at hmono
  have hDpow : (0 : ℝ) < (D : ℝ) ^ d := pow_pos (by exact_mod_cast hD) d
  -- multiply through by `D^d`
  have hmul := mul_le_mul_of_nonneg_right (le_trans hmono hconc) (le_of_lt hDpow)
  rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hDpow), mul_one] at hmul
  calc (S.card : ℝ) ≤ (100 * Real.exp (-(d : ℝ) * ε ^ 4 / 100)) * (D : ℝ) ^ d := hmul
    _ = (D : ℝ) ^ d * (100 * Real.exp (-(d : ℝ) * ε ^ 4 / 100)) := by ring

end Work.Holonomy3
