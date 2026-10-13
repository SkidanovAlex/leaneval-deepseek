import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSXrhs
import Submission.Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS
import Submission.Work.FTS.StrongEps.SupPort.classC_mixed_sup_le
import Submission.Work.FTS_RegExport.RXT.Slots.v2_hkMem_pointwise_min
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.Components2
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.GamTraces
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.BdryTracesMixedTendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

theorem ProfRHSTraces {α Ce Cs : ℝ} (hα : α ∈ Set.Ioc 0 1) {Φs W : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hW : Work.FTS.ClassC.ClassC α W) (hell : Work.FTS.VocabO.EllPkgGo α Ce W (E W))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    (∀ z : ℝ, 0 < z → Filter.Tendsto
        (fun θ => Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W z θ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
    (∀ z : ℝ, 0 < z → Filter.Tendsto
        (fun θ => Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) := by
  constructor
  · intro z hz
    exact ProfRHSAux.tendsto_profRHS hα hW hell hstar
      { hz := hz
        hquad := ProfRHSAux.eventually_mem_Ioo_left
        gam := (ProfRHSAux.GamTraces hα.1).1
        dth_gam := (ProfRHSAux.GamTraces hα.1).2.2.1
        slot := fun a b hab => (ProfRHSAux.BdryTracesMixedTendsto hα.1 hW.bdry hab hz).1 }
  · intro z hz
    exact ProfRHSAux.tendsto_profRHS hα hW hell hstar
      { hz := hz
        hquad := ProfRHSAux.eventually_mem_Ioo_right
        gam := (ProfRHSAux.GamTraces hα.1).2.1
        dth_gam := (ProfRHSAux.GamTraces hα.1).2.2.2
        slot := fun a b hab => (ProfRHSAux.BdryTracesMixedTendsto hα.1 hW.bdry hab hz).2 }

end Work.FTS.StrongEps.EpsRLX
