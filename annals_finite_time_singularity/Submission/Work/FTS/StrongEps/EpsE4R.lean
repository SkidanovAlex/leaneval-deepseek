import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E4R3.Fourth5
import Submission.Work.FTS.StrongEps.E4R3.Sixth5
import Submission.Work.FTS.StrongEps.EpsODEDefs
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Clause1Aux
import Submission.Work.FTS_EllLimOK.ProducerH.H2.bounds_rates
import Submission.Work.FTS_EllLimOK.ProducerH.H2.clause1
import Submission.Work.FTS_StreamBdry.Inputs.residual_slot_jetsB
import Submission.Work.FTS_StreamBdry.Inputs.slice_assy

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **E4 (room ruling, restated 2026-10-12 with kernel symmetry + `StarPkg6`)**.  Proved from the
corrected chapters (`StrongEps/E4R3/`, a-priori chapter v4). -/
theorem EpsE4R : ∀ {Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ}, IsSmoothKernel ρ → (∀ p : ℝ × ℝ, ρ (-p) = ρ p) →
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C₀ : ℝ, Cstar ≤ C₀ → ∃ α₄ : ℝ, 0 < α₄ ∧
    ∀ α ∈ Set.Ioc 0 α₄, ∀ {K : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}, 0 ≤ K →
    (∀ z, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0) →
    (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
    Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    MuLamOK α C₀ Φs E →
    (∀ ε : ℝ, 0 < ε → EpsDatum α ρ ε g₀) →
    Work.FTS.Nonlin.Xn α g₀ ≤ α ^ 2 →
    Work.FTS.StrongGlobal.Xn6 α g₀ ≤ K * α ^ 2 →
    EpsUniformMem α ρ Φs E g₀ C₀ K := fun hρ hρs =>
  EpsE4Thr.E4R5.EpsE4R5_of_chapters hρ
    (EpsE4Thr.E4R5.localStepChapter5_of_XStepInvariant hρ (fun C₀ hC₀ =>
      ⟨1, one_pos, le_rfl, fun _ _ =>
        EpsE4Thr.XStepWired.XStepInvariant_of_regDW (C₀ := C₀) (by linarith) hρ⟩))
    (EpsE4Thr.E4R5.aprioriChapter5_of_halves (EpsE4Thr.E4R5.fourthChapterBF_leaf hρ)
      (EpsE4Thr.E4R5.sixthChapterBF_leaf hρ hρs))
    (EpsE4Thr.E4R3.decayChapter3_leaf hρ)

end Work.FTS.StrongEps
