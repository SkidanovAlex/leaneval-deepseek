import Mathlib
import Submission.Work.Diff.STE.deTurck.ChartCompDefs
import Submission.Work.Diff.STE.DeTurckField
import Submission.Work.Diff.STE.deTurck.koszulPair_eq_jKz

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The chart expression of the DeTurck field is `coPhi`

This module identifies the manifold-level chart components of the DeTurck field,

`deTurckChartComp g gbar x₀ p c = ∑_{ab} GramInv^{ab}(p)(Γ^c_{ab}(p) - Γ̃^c_{ab}(p))`

(`Submission/Work/Diff/STE/DeTurckField.lean`), with the chart-coordinate expression `coPhi` of
`Submission/Work/Diff/STE/deTurck/ChartCompDefs.lean`:

`deTurckChartComp g gbar x₀ p c = coPhi (chartMatFun g x₀) (chartMatFun gbar x₀) c (extChartAt I x₀ p)`.

The dictionary is

* `GramInv (fun _ ↦ g) x₀ 0 p = (gmat g x₀ p)⁻¹` and `gmat g x₀ p = chartMatFun g x₀ (χ p)`
  (`gramInv_eq_jInv_chartMatFun`);
* `chrCoord (fun _ ↦ g) x₀ c a b 0 p = ∑_p' γ^{c p'} Γ_{abp'}` with `Γ_{abp'} = jKz (fderiv (chartMatFun g x₀) (χ p)) a b p'`
  (`Work.Diff.STE.deTurck.koszulPair_eq_jKz`).
-/

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set

namespace Work.Diff.STE.deTurck

open Work.Diff.EXT Work.Diff.STE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
variable [I.Boundaryless] [T2Space M]

noncomputable section

/-- The Gram matrix of the coordinate frame is the chart matrix of the metric at the chart
coordinate of the base point. -/
lemma chartCompB_gmat_eq_chartMatFun (g : Submission.Diff.SMet I M) (x₀ : M) {p : M}
    (hp : p ∈ (chartAt H x₀).source) :
    Work.Diff.EXT.gmat (I := I) g x₀ p = chartMatFun g x₀ ((extChartAt I x₀) p) := by
  funext i j
  have hps : p ∈ (extChartAt I x₀).source := by rwa [extChartAt_source]
  have hsymm : (extChartAt I x₀).symm ((extChartAt I x₀) p) = p := (extChartAt I x₀).left_inv hps
  rw [Work.Diff.EXT.gmat, chartMatFun, hsymm]
  rfl

/-- The inverse Gram matrix of the coordinate frame is `jInv` of the chart matrix. -/
lemma chartCompB_gramInv_eq_jInv_chartMatFun (g : Submission.Diff.SMet I M) (x₀ : M) {p : M}
    (hp : p ∈ (chartAt H x₀).source) (r s : Fin (Module.finrank ℝ E)) :
    Work.Diff.GE.GramInv (I := I) (fun _ : ℝ => g) x₀ 0 p r s
      = Work.Diff.EXT.jInv (chartMatFun g x₀ ((extChartAt I x₀) p)) r s := by
  have hG : Work.Diff.GE.GramM (I := I) (fun _ : ℝ => g) x₀ 0 p
      = Matrix.of (Work.Diff.EXT.gmat (I := I) g x₀ p) := by
    unfold Work.Diff.GE.GramM Work.Diff.GE.mComp Work.Diff.EXT.gmat Work.Diff.EXT.fvec
    simp only [Work.Diff.GE.cFrame_apply]
    rfl
  rw [Work.Diff.GE.GramInv, hG, ← chartCompB_gmat_eq_chartMatFun g x₀ hp]
  rfl

/-- **The chart components of the DeTurck field are the chart-coordinate expression `coPhi`.** -/
theorem chartCompB_deTurckChartComp_eq_coPhi (g gbar : Submission.Diff.SMet I M) (x₀ : M) {p : M}
    (hp : p ∈ (chartAt H x₀).source) (c : Fin (Module.finrank ℝ E)) :
    Work.Diff.STE.DeTurck.deTurckChartComp g gbar x₀ p c
      = coPhi (chartMatFun g x₀) (chartMatFun gbar x₀) c ((extChartAt I x₀) p) := by
  simp only [Work.Diff.STE.DeTurck.deTurckChartComp, Work.Diff.GE.chrCoord, coPhi, coGamU]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [chartCompB_gramInv_eq_jInv_chartMatFun g x₀ hp a b]
  congr 1
  rw [show (∑ p', Work.Diff.GE.GramInv (I := I) (fun _ : ℝ => g) x₀ 0 p c p'
        * Work.Diff.GE.koszulPair (fun _ : ℝ => g) (I := I) x₀ a b p' 0 p)
      = ∑ p', Work.Diff.EXT.jInv (chartMatFun g x₀ ((extChartAt I x₀) p)) c p'
        * Work.Diff.EXT.jKz (fderiv ℝ (chartMatFun g x₀) ((extChartAt I x₀) p)) a b p' from
      Finset.sum_congr rfl (fun p' _ => by
        rw [chartCompB_gramInv_eq_jInv_chartMatFun g x₀ hp c p', koszulPair_eq_jKz g x₀ hp a b p']),
    show (∑ p', Work.Diff.GE.GramInv (I := I) (fun _ : ℝ => gbar) x₀ 0 p c p'
        * Work.Diff.GE.koszulPair (fun _ : ℝ => gbar) (I := I) x₀ a b p' 0 p)
      = ∑ p', Work.Diff.EXT.jInv (chartMatFun gbar x₀ ((extChartAt I x₀) p)) c p'
        * Work.Diff.EXT.jKz (fderiv ℝ (chartMatFun gbar x₀) ((extChartAt I x₀) p)) a b p' from
      Finset.sum_congr rfl (fun p' _ => by
        rw [chartCompB_gramInv_eq_jInv_chartMatFun gbar x₀ hp c p', koszulPair_eq_jKz gbar x₀ hp a b p'])]

end

end Work.Diff.STE.deTurck
