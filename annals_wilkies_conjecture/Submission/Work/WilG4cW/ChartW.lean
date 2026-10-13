/-
  WilG4cW / `ChartW` — the elementary affine-chart lemmas of BNZ §5.4 under the *corrected*
  chart rule `Work.WilG4a.F1AffineW`.

  The frozen `CG.F1Affine` demands `0 < β l` for every chart of the output family.  The lead's
  audit (`sources/wilkiesG4/wilkies_g4_REVIEW.md`) shows that this is false at `p = 1`: the
  producer (`F1AffineW`, area G4a) can only supply charts with

  * `0 ≤ β l`, `0 ≤ α l`, `α l + β l ≤ 1` (a *degenerate* chart `β l = 0` is the constant chart
    `t ↦ α l`), and
  * the *image* clause `∀ t ∈ I, α l + β l * t ∈ I` (which for `β l = 0` says `α l ∈ I`),

  while the *cover* is still achieved by non-degenerate charts (`0 < β l`).

  Every downstream use of `0 < β l` that is not the pull-back of the finite bad set (that one
  is handled in `CurveDataPullCW`) only ever needs:
  * the chart to map the interval/cube into itself — that is the image clause, and
  * the chart to be distance-non-increasing — that follows from `0 ≤ β l` and `α l + β l ≤ 1`.

  This file records `Work.WilkG4c.ChartInW` (the corrected per-chart condition, verbatim the
  per-chart conjunct of `F1AffineW`) and the four elementary pullback lemmas under it:
  `chartPt_mem_openCubeW`, `pullX_YBoundW`, `pullX_lipW`, `valuesIn01_pullXW`.
-/
import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.Pullback

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- **The corrected per-chart condition** (`Work.WilG4a.F1AffineW`): the affine chart
`t ↦ α l + β l · t` of the distinguished coordinate is allowed to be degenerate (`β l = 0`),
but must have `β l ≥ 0`, `α l ≥ 0`, `α l + β l ≤ 1` and must map the interval `I = (0,1)`
(the range of the distinguished coordinate, on which BNZ's estimates live) into itself. -/
abbrev ChartInW {p : ℕ} (α β : (Fin p → ℝ) → ℝ) : Prop :=
  ∀ l : Fin p → ℝ, 0 ≤ β l ∧ 0 ≤ α l ∧ α l + β l ≤ 1 ∧ ∀ t ∈ I, α l + β l * t ∈ I

/-- The (single-parameter) form of `ChartInW`, as it arises from the conjunction returned by
`F1AffineW`. -/
theorem chartInW_iff {p : ℕ} (α β : (Fin p → ℝ) → ℝ) :
    ChartInW α β ↔
      ∀ l : Fin p → ℝ, 0 ≤ β l ∧ 0 ≤ α l ∧ α l + β l ≤ 1 ∧ ∀ t ∈ I, α l + β l * t ∈ I :=
  Iff.rfl

/-- **The affine chart maps the cube into the cube.**  Under `ChartInW` the `0`-coordinate of
`chartPt α β l t` is `α l + β l · t 0 ∈ I` by the image clause, and the remaining coordinates
are unchanged. -/
theorem chartPt_mem_openCubeW {p n : ℕ} {α β : (Fin p → ℝ) → ℝ} {l : Fin p → ℝ}
    (h : 0 ≤ β l ∧ 0 ≤ α l ∧ α l + β l ≤ 1 ∧ ∀ t ∈ I, α l + β l * t ∈ I)
    {t : Fin (n + 1) → ℝ} (ht : t ∈ openCube (n + 1)) :
    chartPt α β l t ∈ openCube (n + 1) := by
  intro j
  induction j using Fin.cases with
  | zero => rw [chartPt_zero]; exact h.2.2.2 (t 0) (ht 0)
  | succ j => rw [chartPt_succ]; exact ht j.succ

/-- `chartPt_mem_openCubeW`, in the `ChartInW` form. -/
theorem chartPt_mem_openCubeW' {p n : ℕ} {α β : (Fin p → ℝ) → ℝ} {l : Fin p → ℝ}
    (h : ChartInW α β) {t : Fin (n + 1) → ℝ} (ht : t ∈ openCube (n + 1)) :
    chartPt α β l t ∈ openCube (n + 1) :=
  chartPt_mem_openCubeW (h l) ht

/-- **`YBound` is preserved by the affine `x`-pullback under `ChartInW`.**  The image clause is
exactly what is needed: for `x ∈ I` the chart point has first coordinate `α l + β l · x ∈ I`,
and the slice of the pullback there is the slice of `F`. -/
theorem pullX_YBoundW {k p n : ℕ} {F : Family k p (n + 1)} {r : ℕ} {α β : (Fin p → ℝ) → ℝ}
    (hY : YBound F r) (h : ChartInW α β) : YBound (pullX F α β) r := by
  intro i l x hx m hm y hy
  rw [slice_pullX]
  exact hY i l (α l + β l * x) ((h l).2.2.2 x hx) m hm y hy

/-- **`LipOnCube 1` is preserved by the affine `x`-pullback under `ChartInW`.**  The chart
`t ↦ (α l + β l · t 0, tail t)` is distance-non-increasing because `0 ≤ β l ≤ 1`
(`β l ≤ 1` follows from `0 ≤ α l` and `α l + β l ≤ 1`), and it maps the cube into the cube by
`chartPt_mem_openCubeW`. -/
theorem pullX_lipW {k p n : ℕ} {F : Family k p (n + 1)} {α β : (Fin p → ℝ) → ℝ}
    (hL : LipOnCube F 1) (h : ChartInW α β) : LipOnCube (pullX F α β) 1 := by
  intro i l z z' hz hz'
  have hβ0 : 0 ≤ β l := (h l).1
  have hβ1 : β l ≤ 1 := by have hh := h l; linarith [hh.2.1, hh.2.2.1]
  have hmem : ∀ {t : Fin (n + 1) → ℝ}, t ∈ openCube (n + 1) →
      chartPt α β l t ∈ openCube (n + 1) := fun ht => chartPt_mem_openCubeW (h l) ht
  have hchart : dist (chartPt α β l z) (chartPt α β l z') ≤ dist z z' := by
    rw [dist_pi_le_iff dist_nonneg]
    intro j
    induction j using Fin.cases with
    | zero =>
        rw [chartPt_zero, chartPt_zero, Real.dist_eq]
        have h2 : |z 0 - z' 0| ≤ dist z z' := by
          simpa [Real.dist_eq] using dist_le_pi_dist z z' (0 : Fin (n + 1))
        calc |(α l + β l * z 0) - (α l + β l * z' 0)|
            = β l * |z 0 - z' 0| := by
              rw [show (α l + β l * z 0) - (α l + β l * z' 0) = β l * (z 0 - z' 0) by ring,
                abs_mul, abs_of_nonneg hβ0]
          _ ≤ 1 * |z 0 - z' 0| := mul_le_mul_of_nonneg_right hβ1 (abs_nonneg _)
          _ = |z 0 - z' 0| := one_mul _
          _ ≤ dist z z' := h2
    | succ j =>
        rw [chartPt_succ, chartPt_succ]
        exact dist_le_pi_dist z z' j.succ
  calc |pullX F α β i l z - pullX F α β i l z'|
      = |F i l (chartPt α β l z) - F i l (chartPt α β l z')| := rfl
    _ ≤ 1 * dist (chartPt α β l z) (chartPt α β l z') := hL i l _ _ (hmem hz) (hmem hz')
    _ ≤ 1 * dist z z' := mul_le_mul_of_nonneg_left hchart zero_le_one

/-- **`ValuesIn01` is preserved by the affine `x`-pullback under `ChartInW`.** -/
theorem valuesIn01_pullXW {k p n : ℕ} {Λ : Set (Fin p → ℝ)} {F : Family k p (n + 1)}
    {α β : (Fin p → ℝ) → ℝ} (h : ValuesIn01 Λ F) (hc : ChartInW α β) :
    ValuesIn01 Λ (pullX F α β) := by
  intro i l hl t ht
  rw [pullX_apply]
  exact h i l hl _ (chartPt_mem_openCubeW (hc l) ht)

end Work.WilkG4c
