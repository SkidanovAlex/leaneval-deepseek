/-
  WilG4c / `StepH1Out` — the abbreviation of the `F1Affine` output for one chart, and the glue
  between the `Fin`-indexed tuple `tupleFam` and the index set `TupleIdx`.

  `Work.WilkG4c.StepStage_of_axes` applies `h1 p` (`F1Affine`) to the tuple `tupleFam F γs` of
  BNZ §5.4 with `Λ := Set.univ`, order `r+1` and parameter `ε/2`.  Its conclusion, restricted to
  one chart `(α₀,β₀)`, is abbreviated here as `H1Chart F γs α₀ β₀`: the chart conditions, the
  `C^{r+1}`-smoothness of every tuple member along the chart, and the unit jet bound of all
  orders `≤ r+1`.  `h1Chart_of_f1affine` moves the statement from the `Fin (tupleSize k n r)`
  enumeration to the index set `TupleIdx k n r`.
-/
import Mathlib
import Submission.Work.WilG4c.StepTupleDefs

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- **The output of `F1Affine` for one affine chart.**  For the tuple `tupleFam F γs` of BNZ
§5.4 and the chart `t ↦ α₀ l + β₀ l · t 0`, it records the chart conditions and the `C^{r+1}`
bounds: every tuple member is `C^{r+1}` along the chart on `openCube 1`, with all operator norms
of orders `≤ r+1` bounded by `1`. -/
abbrev H1Chart {k p n r : ℕ} (F : Family k p (n + 1))
    (γs : (i : Fin k) → MIdx n r → (Fin p → ℝ) → ℝ → (Fin n → ℝ))
    (α₀ β₀ : (Fin p → ℝ) → ℝ) : Prop :=
  (∀ l : Fin p → ℝ, 0 < β₀ l ∧ 0 ≤ α₀ l ∧ α₀ l + β₀ l ≤ 1) ∧
  ∀ x : TupleIdx k n r, ∀ l : Fin p → ℝ,
    ContDiffOn ℝ (r + 1)
      (fun t : Fin 1 → ℝ => tupleFunc F γs x l (fun _ => α₀ l + β₀ l * t 0)) (openCube 1) ∧
    ∀ q ≤ r + 1, ∀ t ∈ openCube 1,
      ‖iteratedFDeriv ℝ q
        (fun t : Fin 1 → ℝ => tupleFunc F γs x l (fun _ => α₀ l + β₀ l * t 0)) t‖ ≤ 1

/-- The conclusion of `F1Affine` for `tupleFam F γs` (with `Λ := Set.univ`) yields `H1Chart` for
every chart of the family, by moving from the `Fin (tupleSize k n r)` enumeration to the index
set `TupleIdx k n r`. -/
theorem h1Chart_of_f1affine {k p n r : ℕ} {F : Family k p (n + 1)}
    {γs : (i : Fin k) → MIdx n r → (Fin p → ℝ) → ℝ → (Fin n → ℝ)}
    {Φ₀ : Finset (((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ))}
    (h : ∀ cb ∈ Φ₀,
      (∀ l : Fin p → ℝ, 0 < cb.2 l ∧ 0 ≤ cb.1 l ∧ cb.1 l + cb.2 l ≤ 1) ∧
      ∀ j : Fin (tupleSize k n r), ∀ l : Fin p → ℝ,
        ContDiffOn ℝ (r + 1)
          (fun t : Fin 1 → ℝ => tupleFam F γs j l (fun _ => cb.1 l + cb.2 l * t 0))
          (openCube 1) ∧
        ∀ q ≤ r + 1, ∀ t ∈ openCube 1,
          ‖iteratedFDeriv ℝ q
            (fun t : Fin 1 → ℝ => tupleFam F γs j l (fun _ => cb.1 l + cb.2 l * t 0)) t‖ ≤ 1) :
    ∀ cb ∈ Φ₀, H1Chart F γs cb.1 cb.2 := by
  intro cb hcb
  obtain ⟨hcond, hmem⟩ := h cb hcb
  refine ⟨hcond, fun x l => ?_⟩
  have hx := hmem (Fintype.equivFin (TupleIdx k n r) x) l
  rwa [tupleFam_apply] at hx

end Work.WilkG4c
