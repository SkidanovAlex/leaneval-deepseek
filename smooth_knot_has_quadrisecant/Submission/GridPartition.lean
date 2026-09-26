import Mathlib
import ChallengeDeps
import Submission.CoverRefine

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

/-!
# Layer A (xx) — grid partition of a compact interval

`CoverRefine.lean` (Layer A (xix)) produced the uniform refinement
`chart_refinement`: a `δ > 0` such that every subinterval of `[a,b]` of
length at most `δ` lies in a single chart region.  This module turns `δ`
into an explicit **grid**:

1. **`exists_grid_step`** — the Archimedean step: `∃ m > 0` with
   `(b − a) / m ≤ δ`;
2. **`gridPoint a b m i`** — the grid points `pᵢ = a + i·(b−a)/m`;
3. cell facts: every grid point with `i ≤ m` lies in `[a,b]`
   (`gridPoint_mem_Icc_left` / `_right`), consecutive grid points are
   ordered (`gridPoint_mono`), and the length of each cell is exactly
   `(b − a) / m` (`gridPoint_step`);
4. **`grid_partition`** — the assembled grid lemma: a positive `m` whose
   cells all lie inside `[a,b]` and have length at most `δ`.

The per-cell chart choice (by `classical` from `chart_refinement`) and the
adapted chain (via `chainFromList`) are built on this grid in the next
stages.  Everything here is elementary and verified (no axioms, no
`sorry`).
-/

namespace LeanEval.KnotTheory.Quadrisecant

/-- **The Archimedean step**: for a positive `δ` there is a positive number
of grid cells `m` such that the cell length `(b − a)/m` does not exceed
`δ`. -/
lemma exists_grid_step {a b δ : ℝ} (hδ : 0 < δ) (hab : a ≤ b) :
    ∃ m : ℕ, 0 < m ∧ (b - a) / (m : ℝ) ≤ δ := by
  rcases exists_nat_ge ((b - a) / δ) with ⟨n, hn⟩
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  have hD : 0 ≤ b - a := sub_nonneg.mpr hab
  have h1 : (b - a) ≤ (n : ℝ) * δ := by
    have hdiv : (b - a) / δ ≤ (n : ℝ) := hn
    exact (div_le_iff₀ hδ).mp hdiv
  have hpos : (0 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
  rw [div_le_iff₀ hpos]
  nlinarith [h1, hcast, hδ]

/-- The `i`-th **grid point**: `pᵢ = a + i·(b−a)/m`. -/
noncomputable def gridPoint (a b : ℝ) (m : ℕ) (i : ℕ) : ℝ :=
  a + (i : ℝ) * (b - a) / (m : ℝ)

/-- Consecutive grid points are ordered (for `a ≤ b`). -/
lemma gridPoint_mono {a b : ℝ} (hab : a ≤ b) {m : ℕ} {i j : ℕ} (hij : i ≤ j) :
    gridPoint a b m i ≤ gridPoint a b m j := by
  dsimp [gridPoint]
  have hD : 0 ≤ b - a := sub_nonneg.mpr hab
  have hle : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  have hnm : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have h1 : (i : ℝ) * (b - a) ≤ (j : ℝ) * (b - a) := by
    nlinarith [hD, hle]
  have h2 : (i : ℝ) * (b - a) / (m : ℝ) ≤ (j : ℝ) * (b - a) / (m : ℝ) := by
    exact div_le_div_of_nonneg_right h1 hnm
  nlinarith

/-- The grid point `pᵢ` lies in `[a,b]` whenever `i ≤ m`. -/
lemma gridPoint_mem_Icc_left {a b : ℝ} (hab : a ≤ b) {m : ℕ} (hm : 0 < m)
    {i : ℕ} (_hi : i ≤ m) : a ≤ gridPoint a b m i := by
  dsimp [gridPoint]
  have hD : 0 ≤ b - a := sub_nonneg.mpr hab
  have hnm : (0 : ℝ) ≤ (m : ℝ) := le_of_lt (by exact_mod_cast hm)
  have hnn : 0 ≤ (i : ℝ) * (b - a) / (m : ℝ) := by
    exact div_nonneg (mul_nonneg (by positivity) hD) hnm
  nlinarith

/-- The grid point `pᵢ` lies in `[a,b]` whenever `i ≤ m`. -/
lemma gridPoint_mem_Icc_right {a b : ℝ} (hab : a ≤ b) {m : ℕ} (hm : 0 < m)
    {i : ℕ} (hi : i ≤ m) : gridPoint a b m i ≤ b := by
  dsimp [gridPoint]
  have hD : 0 ≤ b - a := sub_nonneg.mpr hab
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hle : (i : ℝ) * (b - a) ≤ (m : ℝ) * (b - a) := by
    have hile : (i : ℝ) ≤ (m : ℝ) := by exact_mod_cast hi
    nlinarith [hD, hile]
  have h1 : (i : ℝ) * (b - a) / (m : ℝ) ≤ (m : ℝ) * (b - a) / (m : ℝ) := by
    exact div_le_div_of_nonneg_right hle (le_of_lt hmpos)
  have hcancel : (m : ℝ) * (b - a) / (m : ℝ) = b - a := by
    field_simp [ne_of_gt hmpos]
  nlinarith [h1, hcancel]

/-- The length of the cell `[pᵢ, pᵢ₊₁]` is exactly `(b−a)/m`. -/
lemma gridPoint_step {a b : ℝ} {m : ℕ} (hm : 0 < m) (i : ℕ) :
    gridPoint a b m (i + 1) - gridPoint a b m i = (b - a) / (m : ℝ) := by
  have hcast : (((i + 1 : ℕ) : ℝ) : ℝ) = (i : ℝ) + 1 := by norm_num
  have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  dsimp [gridPoint]
  rw [hcast]
  field_simp [hmne]
  ring

/-- **The grid lemma.**  For a positive `δ` and `a ≤ b` there is a positive
number of cells `m` such that every grid point `pᵢ` with `i ≤ m` lies in
`[a,b]` and every cell `[pᵢ, pᵢ₊₁]` (for `i < m`) has length at most
`δ`. -/
theorem grid_partition {a b δ : ℝ} (hδ : 0 < δ) (hab : a ≤ b) :
    ∃ m : ℕ, 0 < m ∧ (b - a) / (m : ℝ) ≤ δ ∧
      (∀ i : ℕ, i ≤ m → a ≤ gridPoint a b m i ∧ gridPoint a b m i ≤ b) ∧
      (∀ i : ℕ, i < m → gridPoint a b m (i + 1) - gridPoint a b m i ≤ δ) := by
  rcases exists_grid_step hδ hab with ⟨m, hm, hstep⟩
  refine ⟨m, hm, hstep, ?_, ?_⟩
  · intro i hi
    exact ⟨gridPoint_mem_Icc_left hab hm hi, gridPoint_mem_Icc_right hab hm hi⟩
  · intro i hi
    rw [gridPoint_step hm i]
    exact hstep

end LeanEval.KnotTheory.Quadrisecant

namespace LeanEval.KnotTheory.Quadrisecant

/-- **Per-cell chart choice.**  From the uniform refinement of the chart
cover one obtains a number of grid cells `m` such that every cell
`[pᵢ, pᵢ₊₁]` (a closed subinterval of `[a,b]` of length at most `δ`) lies
entirely in the region of one chart `g` of the cover — the raw material for
the adapted chain (each cell assigned its chart, junctions in the overlap of
consecutive regions). -/
theorem perCell_chart {r : ℝ → Space} {a b : ℝ} (hab : a ≤ b)
    (σ : CompactInterval a b → ZeroSetPoint r) (hσ : Continuous σ)
    (cs : List (Sigma (fun p : KnotParamTriple => ZeroSet1Chart r p)))
    (hcover : ∀ u : CompactInterval a b,
      ∃ g : Sigma (fun p : KnotParamTriple => ZeroSet1Chart r p), g ∈ cs ∧
        (σ u : KnotParamTriple) ∈ g.2.V) :
    ∃ m : ℕ, 0 < m ∧
      (∀ i : ℕ, i < m →
        ∃ g : Sigma (fun p : KnotParamTriple => ZeroSet1Chart r p), g ∈ cs ∧
          ∀ u : CompactInterval a b, (u : ℝ) ∈
              Set.Icc (gridPoint a b m i) (gridPoint a b m (i + 1)) →
            (σ u : KnotParamTriple) ∈ g.2.V) := by
  rcases chart_refinement hab σ hσ cs hcover with ⟨δ, hδpos, hδcell⟩
  rcases grid_partition hδpos hab with ⟨m, hm, _hstep, hbnds, hcells⟩
  refine ⟨m, hm, ?_⟩
  intro i hi
  have hile : i ≤ m := le_of_lt hi
  have hi1 : i + 1 ≤ m := (Nat.succ_le_iff).mpr hi
  have hp0 : gridPoint a b m i ∈ Set.Icc a b :=
    ⟨gridPoint_mem_Icc_left hab hm hile, gridPoint_mem_Icc_right hab hm hile⟩
  have hp1 : gridPoint a b m (i + 1) ∈ Set.Icc a b :=
    ⟨gridPoint_mem_Icc_left hab hm hi1, gridPoint_mem_Icc_right hab hm hi1⟩
  rcases hδcell (gridPoint a b m i) (gridPoint a b m (i + 1)) hp0 hp1
      (gridPoint_mono hab (Nat.le_succ i)) (hcells i hi) with ⟨g, hg, hcellg⟩
  exact ⟨g, hg, hcellg⟩

end LeanEval.KnotTheory.Quadrisecant
