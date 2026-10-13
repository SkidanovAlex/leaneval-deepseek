import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS_EllLimOK.RulingELF
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Basic
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Data
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Assembly
import Submission.Work.FTS_EllLimOK.ProducerH.H2.BoxDataOf
import Submission.Work.FTS_EllLimOK.ProducerH.H2.clause1
import Submission.Work.FTS_EllLimOK.ProducerH.H2.clause2
import Submission.Work.FTS_EllLimOK.ProducerH.H2.clause3

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

theorem pkgBoxH_of_ellClassOk2 :
    ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 < α → α ≤ α₁ → ∀ Ce : ℝ,
      ∀ E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn,
        (∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
          Work.FTS.EllExist.EllClassOk 8 α g (E g) ∧
            Work.FTS.VocabO.EllPkgGo α Ce g (E g) ∧
            Work.FTS.ClassC.EllPkgK α 6 Ce g (E g)) →
        Work.FTS_EllLimOK.RulingELF.PkgBoxH α E := by
  -- the source thresholds of the chapter are `0 < α`, `α ≤ 1/4`
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro α hα hα4 Ce E hE
  -- the assembly (box quantifiers, degenerate box) is `pkgBoxH_of_data`; the four analytic
  -- inputs and the three clauses are the H2 chapter
  exact pkgBoxH_of_data
    (fun a b ha hab => H2.boxData_of_parts hα hα4 hE ha hab)
    (fun a b ha hab hd => H2.clause1 hα hα4 hE ha hab hd)
    (fun a b ha hab hd hc1 => H2.clause2 hα hα4 hE ha hab hd hc1)
    (fun a b ha hab hd hc1 => H2.clause3 hα hα4 hE ha hab hd hc1)

end Work.FTS_EllLimOK.ProducerH
