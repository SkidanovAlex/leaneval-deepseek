import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_deriv_bdd
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_continuousOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open MeasureTheory Set

/-- **Interval integrability of the angular derivative of a trace-class slice.**

For a trace-class datum `G` and a fixed radius `w > 0`, the angular derivative
`s ↦ ∂_θG(w,s)` is interval integrable on `[0, π/2]`.  Indeed `slice_deriv_bdd` provides a
uniform bound `|∂_θG(w,s)| ≤ M` on the *open* interval `(0, π/2)`, the derivative of any
function `ℝ → ℝ` is measurable (`measurable_deriv`), and `(0, π/2)` differs from
`(0, π/2]` by the null set `{π/2}`.  (No continuity at the endpoints is needed.) -/
theorem intervalIntegrable_pth_slice (G : ℝ → ℝ → ℝ)
    (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G) {w : ℝ} (hw : 0 < w) :
    IntervalIntegrable (fun s : ℝ => Work.Spaces.pth G w s) MeasureTheory.volume 0 (Real.pi / 2) := by
  obtain ⟨M, -, hM⟩ := slice_deriv_bdd G hT hw
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hIoo : IntegrableOn (fun s : ℝ => deriv (fun θ' : ℝ => G w θ') s) (Set.Ioo 0 (Real.pi / 2))
      MeasureTheory.volume := by
    refine IntegrableOn.of_bound ?_ (measurable_deriv _).aestronglyMeasurable M ?_
    · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun s hs => by
        rw [Real.norm_eq_abs]; exact hM s hs)
  have hIoc : IntegrableOn (fun s : ℝ => deriv (fun θ' : ℝ => G w θ') s) (Set.Ioc 0 (Real.pi / 2))
      MeasureTheory.volume :=
    hIoo.congr_set_ae (MeasureTheory.Ioo_ae_eq_Ioc (μ := MeasureTheory.volume)).symm
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi).mpr hIoc

end Work.FTS.EllSol.EllPkgAux.MollDom
