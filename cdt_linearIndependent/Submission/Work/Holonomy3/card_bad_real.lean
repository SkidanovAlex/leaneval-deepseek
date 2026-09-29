import Mathlib
import Submission.Work.Holonomy3.siegelDefs
import Submission.Work.Holonomy3.lowdiscCells
import Submission.Work.Holonomy3.cell_subset_disc_half
import Submission.Work.Holonomy3.card_le_of_cells

namespace Work.Holonomy3

open Submission.CDT.Discrepancy
open MeasureTheory
open scoped BigOperators

/-- Arithmetic bookkeeping for the final case split: if `y` is bounded both by `(f+1)^d · c` and by
`(f+1)^d` (with `0 ≤ f`, `0 ≤ c`), then `y ≤ f^d · c + ((f+1)^d - f^d)`.

Indeed, if `c ≤ 1` then `(f+1)^d c = f^d c + ((f+1)^d - f^d) c ≤ f^d c + ((f+1)^d - f^d)`, while if
`c ≥ 1` then `y ≤ (f+1)^d = f^d + ((f+1)^d - f^d) ≤ f^d c + ((f+1)^d - f^d)`. -/
private lemma key_arith {d : ℕ} {f c y : ℝ} (hf : 0 ≤ f)
    (h1 : y ≤ (f + 1) ^ d * c) (h2 : y ≤ (f + 1) ^ d) :
    y ≤ f ^ d * c + ((f + 1) ^ d - f ^ d) := by
  by_cases hle : c ≤ 1
  · have hbd : 0 ≤ (f + 1) ^ d - f ^ d :=
      sub_nonneg.mpr (pow_le_pow_left₀ hf (by linarith) d)
    have hbc : ((f + 1) ^ d - f ^ d) * c ≤ ((f + 1) ^ d - f ^ d) :=
      mul_le_of_le_one_right hbd hle
    nlinarith [h1, hbc]
  · have hlt : 1 < c := not_le.mp hle
    have hfd : 0 ≤ f ^ d := pow_nonneg hf d
    have hfc : f ^ d ≤ f ^ d * c := le_mul_of_one_le_right hfd (le_of_lt hlt)
    nlinarith [h2, hfc]

/-- **The high-discrepancy lattice points are exponentially few** (real normalisation).
For `d ≥ 1`, `R ≥ 1`, `ε > 0` with `4 (1/R + 1/d) ≤ ε`, the number of `k : Fin d → ℕ` with all
`k j ≤ R` (real bound) and `ε ≤ disc (k/R)` is at most
`⌊R⌋^d · 100 exp (-d (ε/2)^4/100) + ((⌊R⌋+1)^d - ⌊R⌋^d)`.

Route: the boxes `∏_j [k_j/R, (k_j+1)/R)` for `k` with all `k_j ≤ ⌊R⌋ - 1` are disjoint with
`(muP d)`-measure `R^{-d}`; moving a coordinate by at most `1/R` changes `disc` by at most
`2/R + 1/d ≤ ε/2` (by `Work.Holonomy3.disc_shift_lipschitz` or a locally proved version), so
`disc (k/R) ≥ ε` forces each such box into `{disc ≥ ε/2}`; hence `#bad ≤ R^d · 100 exp (-d(ε/2)^4/100)`
plus the `(⌊R⌋+1)^d - ⌊R⌋^d` points with some coordinate equal to `⌊R⌋`, using
`Submission.CDT.Discrepancy.disc_concentration_four` for the measure. To replace the coefficient
`R^d` by `⌊R⌋^d` split on `100 exp (-d(ε/2)^4/100) ≤ 1`: either the boundary term
`(⌊R⌋+1)^d - ⌊R⌋^d` already absorbs the difference (since `R ≤ ⌊R⌋+1`), or the right hand side is
at least `(⌊R⌋+1)^d`, which dominates the total number of `k` with all `k_j ≤ R`.

Here the grid is taken with the *integer* denominator `g = ⌊R⌋ + 1 > R`: the cells
`cell d g k = ∏_j [k_j/g, (k_j+1)/g)` (for `k` with all `k_j ≤ ⌊R⌋`) tile `[0,1)^d`, each has
`(muP d)`-measure `g^{-d}`, and `Work.Holonomy3.cell_subset_disc_half` shows that the cell of a bad
`k` lies in `{disc ≥ ε/2}`.  Hence `#bad ≤ g^d · 100 exp (-d(ε/2)^4/100) = ⌊R⌋^d c + bd · c` with
`c = 100 exp (-d(ε/2)^4/100)` and `bd = (⌊R⌋+1)^d - ⌊R⌋^d`; combined with the trivial bound
`#bad ≤ (⌊R⌋+1)^d` this gives the claim (if `c ≤ 1` the second summand `bd · c ≤ bd` is absorbed by
the boundary term, if `c ≥ 1` the trivial bound `⌊R⌋^d ≤ ⌊R⌋^d c` is used). -/
theorem card_bad_real {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 1 ≤ R) {ε : ℝ} (hε : 0 < ε)
    (hbig : 4 * (R⁻¹ + (d : ℝ)⁻¹) ≤ ε) :
    ((Fintype.piFinset (fun _ : Fin d => Finset.range (Nat.ceil R + 1))).filter
        (fun k : Fin d → ℕ => (∀ j, (k j : ℝ) ≤ R) ∧
          ε ≤ Submission.CDT.Discrepancy.disc (fun j => (k j : ℝ) / R))).card ≤
      (Nat.floor R : ℝ) ^ d * (100 * Real.exp (-(d : ℝ) * (ε / 2) ^ 4 / 100)) +
        (((Nat.floor R : ℕ) + 1 : ℝ) ^ d - (Nat.floor R : ℝ) ^ d) := by
  classical
  set c : ℝ := 100 * Real.exp (-(d : ℝ) * (ε / 2) ^ 4 / 100) with hcdef
  set B : Finset (Fin d → ℕ) :=
    ((Fintype.piFinset (fun _ : Fin d => Finset.range (Nat.ceil R + 1))).filter
        (fun k : Fin d → ℕ => (∀ j, (k j : ℝ) ≤ R) ∧
          ε ≤ Submission.CDT.Discrepancy.disc (fun j => (k j : ℝ) / R))) with hBdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  -- every element of `B` has all coordinates `≤ ⌊R⌋`
  have hle_floor : ∀ k ∈ B, ∀ j, k j ≤ Nat.floor R := by
    intro k hk j
    exact Nat.le_floor ((Finset.mem_filter.mp hk).2.1 j)
  have hbad : ∀ k ∈ B, ε ≤ Submission.CDT.Discrepancy.disc (fun j => (k j : ℝ) / R) :=
    fun k hk => (Finset.mem_filter.mp hk).2.2
  have hDpos : 0 < Nat.floor R + 1 := by omega
  -- ## Step 2: the counting bound via the grid cells of denominator `g = ⌊R⌋ + 1`
  have hstep2 : (B.card : ℝ) ≤ ((Nat.floor R : ℝ) + 1) ^ d * c := by
    have hsub : ∀ k ∈ B, cell d (Nat.floor R + 1) k ⊆
        {u : Fin d → ℝ | ε / 2 ≤ Submission.CDT.Discrepancy.disc u} :=
      fun k hk => cell_subset_disc_half hd hR hbig (hle_floor k hk) (hbad k hk)
    have hcount := card_le_of_cells (ε := ε / 2) hd hDpos (by positivity) B hle_floor hsub
    simpa [hcdef, Nat.cast_add, Nat.cast_one] using hcount
  -- ## Step 1: the trivial counting bound
  have hstep1 : (B.card : ℝ) ≤ ((Nat.floor R : ℝ) + 1) ^ d := by
    have hBsub : B ⊆ Fintype.piFinset (fun _ : Fin d => Finset.range (Nat.floor R + 1)) := by
      intro k hk
      rw [Fintype.mem_piFinset]
      intro j
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (hle_floor k hk j)
    have hcard : B.card ≤ (Nat.floor R + 1) ^ d := by
      have h1 := Finset.card_le_card hBsub
      simpa [Fintype.card_piFinset, Finset.prod_const, Finset.card_range, Finset.card_univ,
        Fintype.card_fin] using h1
    calc (B.card : ℝ) ≤ (((Nat.floor R + 1) ^ d : ℕ) : ℝ) := by exact_mod_cast hcard
      _ = ((Nat.floor R : ℝ) + 1) ^ d := by push_cast; ring
  -- ## Assembly
  have hgoal : (B.card : ℝ) ≤ (Nat.floor R : ℝ) ^ d * c +
      (((Nat.floor R : ℝ) + 1) ^ d - (Nat.floor R : ℝ) ^ d) :=
    key_arith (Nat.cast_nonneg _) hstep2 hstep1
  rw [hBdef]
  simpa [hcdef] using hgoal

end Work.Holonomy3
