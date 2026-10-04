import Mathlib
import Submission.Work.Diff.EXT.ConnCov.ChartTowerDefs
import Submission.Work.Diff.EXT.ConnCov.dAOfTowerBoundShiAux
import Submission.Work.Diff.EXT.ConnCov.covRicBoundShi
import Submission.Work.Diff.EXT.ConnCov.rmChartTower_eq_covKRmExt
import Submission.Work.Diff.EXT.ConnCov.reactJetsKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Jet bounds of the reaction array `∂_t aComp`

The statement `Work.Diff.EXT.ConnCov.reactArr_jets` — the chart jets of the reaction array
`Work.Diff.EXT.ConnCov.reactArr = ∂_t aComp` (the base array of the reaction tower, see
`Work.Diff.EXT.ConnCov.dAOfTower_chart_bound`) are bounded on `[T/2,T) × K'` by a constant, given the
chart jets of `rmChartExpr` and of `chartMat` up to order `K + 1`.

The content is assembled in `Submission/Work/Diff/EXT/ConnCov/reactJetsKit.lean`:

* `Work.Diff.EXT.ConnCov.reactArr_eq_reactExpr` — the pointwise identity `reactArr = reactExpr`,
  where `reactExpr` is the explicit chart expression
  `-(∂_i Ric_{jl} + ∂_j Ric_{il} - ∂_l Ric_{ij}) + 2 ∑_p Ric_{lp} Γ^p_{ij}(G 0)`
  (time derivative of the Koszul pairing by Clairaut, `∂_t g = -2 Ric`, and `Ric` as the
  inverse-Gram contraction of `rmChartExpr`);
* `Work.Diff.EXT.ConnCov.reactExpr_jets` — the jet bounds of `reactExpr`, an algebraic expression in
  the chart jets of `chartMat` (through `GramInv`) and of `rmChartExpr` together with the determinant
  lower bound for `GramM`.
-/

namespace Work.Diff.EXT.ConnCov

theorem reactArr_jets
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hbound : ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (hShi : Work.Diff.EXT.ShiBounds (I := I) (M := M))
    (K : ℕ) (x₀ : M) (K' : Set E) (hK'c : IsCompact K')
    (hK't : K' ⊆ (extChartAt I x₀).target)
    (hrm : ∃ Crm : ℝ, 0 ≤ Crm ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ J : ℕ, J ≤ K + 1 →
      ∀ (i j' k l : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ J (fun y' : E => Work.Diff.GE.rmChartExpr (I := I) G x₀ i j' k l t
            (Work.Diff.EXT.pt (I := I) x₀ y')) y‖ ≤ Crm)
    (hmat : ∃ Cmt : ℝ, 0 ≤ Cmt ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ J : ℕ, J ≤ K + 1 →
      ∀ (i j' : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ J
          (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j') y‖ ≤ Cmt)
    (hcomp : ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ J : ℕ, J ≤ K →
      ∀ (i j' l : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ J
          (fun y' : E => Work.Diff.EXT.aComp (I := I) (M := M) G x₀ t y' i j' l) y‖ ≤ Ca) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ J : ℕ, J ≤ K →
      ∀ (i j' l : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ J
          (fun y' : E => Work.Diff.EXT.ConnCov.reactArr (I := I) (M := M) G x₀ t y' i j' l) y‖
          ≤ Cd :=
  reactArr_jets' (I := I) (M := M) hLC G T C hT hC hflow hbound hmet hShi K x₀ K' hK'c hK't
    hrm hmat hcomp

end Work.Diff.EXT.ConnCov
