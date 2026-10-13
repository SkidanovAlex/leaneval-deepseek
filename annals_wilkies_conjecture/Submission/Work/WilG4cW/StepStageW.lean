/-
  WilG4cW / `StepStageW` — the stage hypothesis of BNZ §5.4 under the corrected chart rule.

  This is `Work.WilkG4c.StepStage` (`StepHigherStageDefs.lean`) with the per-chart condition
  `0 < cb.2 l ∧ 0 ≤ cb.1 l ∧ cb.1 l + cb.2 l ≤ 1` replaced by the corrected condition
  `ChartInW cb.1 cb.2` (i.e. `β ≥ 0` is allowed — the degenerate chart `β l = 0` is the
  constant chart `t ↦ α l` — together with the image clause
  `∀ t ∈ I, cb.1 l + cb.2 l * t ∈ I`).

  Everything else (the `Ω`-bounds on the charts, the `ε/2`-cover and the multi-curve data
  `CurveData` for each pullback) is unchanged; the consumer
  `Work.WilkG4c.FLemP_of_stageW` uses the W-variants of the five chart lemmas
  (`ChartW.lean`, `SubdivChartW.lean`) so that no strictness `0 < β l` is needed there.
-/
import Mathlib
import Submission.Work.WilG4c.StepHigherStageDefs
import Submission.Work.WilG4cW.ChartW

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- **The stage hypothesis of BNZ §5.4, corrected.**  For every family satisfying `PYLip` with
`Ω`-bounded graphs and values in `(0,1)`, there is a finite family `Φ₁` of affine `x`-charts
`(α,β)` such that

* the coordinate graphs of `α,β` are `Ω`-bounded with format `a₁` and degree `eval ![D,r] b₁`;
* every chart satisfies `ChartInW` (`0 ≤ β l`, `0 ≤ α l`, `α l + β l ≤ 1`, and the chart maps
  `I` into `I` — so a degenerate chart `β l = 0` is allowed and then `α l ∈ I`);
* the charts cover the `x`-interval `I` up to `ε/2`;
* each pullback `pullX F α β` carries the multi-curve data `CurveData` of the estimate;
* the number of charts is bounded by a polynomial in `D,r,k,-log ε`. -/
def StepStageW (S : SOMin) (p n : ℕ) : Prop :=
  ∀ (F0 : ℕ), ∃ (a₁ : ℕ) (b₁ : MvPolynomial (Fin 2) ℕ) (c₁ : MvPolynomial (Fin 4) ℝ),
      ∀ (D r k : ℕ) (ε : ℝ), 1 ≤ r → 0 < ε → ε < 1 →
      ∀ (Λ : Set (Fin p → ℝ)) (F : Family k p (n + 1)),
        PYLip p n r k F → (∀ i, famGraph (F i) ∈ S.Ω F0 D (p + (n + 1) + 1)) →
        ValuesIn01 Λ F →
        ∃ Φ₁ : Finset (((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ)),
          (Φ₁.card : ℝ) ≤
            MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c₁ ∧
          (∀ cb ∈ Φ₁,
            graphOf cb.1 ∈ S.Ω a₁ (MvPolynomial.eval ![D, r] b₁) (p + 1) ∧
            graphOf cb.2 ∈ S.Ω a₁ (MvPolynomial.eval ![D, r] b₁) (p + 1) ∧
            ChartInW cb.1 cb.2) ∧
          (∀ l ∈ Λ, ∀ x ∈ I, ∃ cb ∈ Φ₁, ∃ t ∈ I,
            |cb.1 l + cb.2 l * t - x| < ε / 2) ∧
          (∀ cb ∈ Φ₁, CurveData k p n r (pullX F cb.1 cb.2))

end Work.WilkG4c
