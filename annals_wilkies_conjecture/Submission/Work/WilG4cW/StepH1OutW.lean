/-
  WilG4cW / `StepH1OutW` — the abbreviation of the `F1AffineW` output for one chart.

  `Work.WilkG4c.StepStage_of_axesW` applies `h1 p` (`Work.WilG4a.F1AffineW`) to the padded
  tuple `tupleFamBig F γs` of BNZ §5.4 with `Λ := Set.univ`, order `r+1` and parameter `ε/2`.
  Its conclusion, restricted to one chart `(α₀,β₀)`, is abbreviated here as `H1ChartW`: the
  corrected chart conditions (`ChartInW`, i.e. `β ≥ 0` allowed) and the `C^{r+1}`-bounds for
  every tuple member along the chart.

  This is `Work.WilkG4c.H1Chart` (`StepH1Out.lean`) with the chart condition `0 < β₀ l`
  relaxed to `ChartInW α₀ β₀` (which is exactly the per-chart conjunct of `F1AffineW`), and
  the passage from the `Fin (tupleSizeBig k n r)` enumeration to the index set
  `TupleIdx k n r` is `h1Chart_of_f1affine_bigW`.
-/
import Mathlib
import Submission.Work.WilG4c.StepTupleBig
import Submission.Work.WilG4cW.ChartW

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- **The output of `F1AffineW` for one affine chart.**  For the tuple `tupleFam F γs` of BNZ
§5.4 and the chart `t ↦ α₀ l + β₀ l · t 0`, it records the corrected chart conditions
(`ChartInW`: `β ≥ 0`, `α ≥ 0`, `α + β ≤ 1`, image in `I`) and the `C^{r+1}` bounds: every
tuple member is `C^{r+1}` along the chart on `openCube 1`, with all operator norms of orders
`≤ r+1` bounded by `1`. -/
abbrev H1ChartW {k p n r : ℕ} (F : Family k p (n + 1))
    (γs : (i : Fin k) → MIdx n r → (Fin p → ℝ) → ℝ → (Fin n → ℝ))
    (α₀ β₀ : (Fin p → ℝ) → ℝ) : Prop :=
  ChartInW α₀ β₀ ∧
  ∀ x : TupleIdx k n r, ∀ l : Fin p → ℝ,
    ContDiffOn ℝ (r + 1)
      (fun t : Fin 1 → ℝ => tupleFunc F γs x l (fun _ => α₀ l + β₀ l * t 0)) (openCube 1) ∧
    ∀ q ≤ r + 1, ∀ t ∈ openCube 1,
      ‖iteratedFDeriv ℝ q
        (fun t : Fin 1 → ℝ => tupleFunc F γs x l (fun _ => α₀ l + β₀ l * t 0)) t‖ ≤ 1

/-- The conclusion of `F1AffineW` for `tupleFamBig F γs` (with `Λ := Set.univ`), in the
per-chart/per-parameter form in which `F1AffineW` states it, yields `H1ChartW` for every chart
of the family, by moving from the `Fin (tupleSizeBig k n r)` enumeration to the index set
`TupleIdx k n r`. -/
theorem h1Chart_of_f1affine_bigW {k p n r : ℕ} {F : Family k p (n + 1)}
    {γs : (i : Fin k) → MIdx n r → (Fin p → ℝ) → ℝ → (Fin n → ℝ)}
    {Φ₀ : Finset (((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ))}
    (h : ∀ cb ∈ Φ₀, ∀ l : Fin p → ℝ,
      0 ≤ cb.2 l ∧ 0 ≤ cb.1 l ∧ cb.1 l + cb.2 l ≤ 1 ∧
        (∀ t ∈ I, cb.1 l + cb.2 l * t ∈ I) ∧
      (∀ j : Fin (tupleSizeBig k n r),
        ContDiffOn ℝ (r + 1)
          (fun t : Fin 1 → ℝ => tupleFamBig F γs j l (fun _ => cb.1 l + cb.2 l * t 0))
          (openCube 1) ∧
        ∀ q ≤ r + 1, ∀ t ∈ openCube 1,
          ‖iteratedFDeriv ℝ q
            (fun t : Fin 1 → ℝ => tupleFamBig F γs j l (fun _ => cb.1 l + cb.2 l * t 0)) t‖ ≤ 1)) :
    ∀ cb ∈ Φ₀, H1ChartW F γs cb.1 cb.2 := by
  intro cb hcb
  refine ⟨fun l => ⟨(h cb hcb l).1, (h cb hcb l).2.1, (h cb hcb l).2.2.1,
      (h cb hcb l).2.2.2.1⟩, ?_⟩
  intro x l
  have hx := (h cb hcb l).2.2.2.2 ⟨((Fintype.equivFin (TupleIdx k n r)) x : ℕ),
      lt_of_lt_of_le (Fintype.equivFin (TupleIdx k n r) x).isLt (tupleSize_le_big k n r)⟩
  rwa [tupleFamBig_eq F γs x] at hx

end Work.WilkG4c
