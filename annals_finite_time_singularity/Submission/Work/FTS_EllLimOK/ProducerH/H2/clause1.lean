import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.RulingELF
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Basic
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Data
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Clause1Aux
import Submission.Work.FTS_EllLimOK.ProducerH.H2.PsiBlock
import Submission.Work.FTS_EllLimOK.ProducerH.H2.ABlock
import Submission.Work.FTS_EllLimOK.ProducerH.H2.BBlockAlt
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.BoxC2
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.contDiffOn_two_of_sliceData
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.hasDerivWithinAt_of_tendsto_deriv
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2EgRate
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.Trace
import Submission.Work.FTS_EllLimOK.ProducerH.MixedJets.mixed_jets_le_Xn6
import Submission.Work.FTS_EllLimOK.BoxDataH.contDiffOn_two_of_fderivWithin_data
import Submission.Work.FTS_EllLimOK.BoxDataH.wJet_slice

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.H2

theorem clause1 {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : Work.FTS_EllLimOK.ProducerH.H2.Ctx α Ce E) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hdata : Work.FTS_EllLimOK.ProducerH.H2.BoxData α Ce E a b) :
    ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      ContDiffOn ℝ 2 (Function.uncurry (E g)) (Work.FTS_EllLimOK.cbox a b) := by
  intro g hg
  -- the box data, unpacked once: the angular rate bound, the pointwise/rate bounds of the
  -- radial derivatives, the angular limits and the two-point Hölder modulus
  have hdata' : BoxData α Ce E a b := hdata
  obtain ⟨K, hK, β, hβ, hmodw, hrates, hlimw, hhol⟩ := hdata'
  obtain ⟨CL, hCL, hlimb⟩ := hlimw
  obtain ⟨L0, N0, L1, N1, hLim⟩ := hlimb g hg
  have hLimAt : LimitsAt (E g) (Work.FTS.StrongGlobal.Xn6 α g) CL a b L0 N0 L1 N1 := hLim
  -- the three blocks of slice data
  have hP := PsiBlock hα hα4 hE ha hab hdata g hg hLimAt
  have hQ := ABlock hα hα4 hE ha hab hdata g hg hLimAt
  have hR := BBlockAlt hα hα4 hE ha hab hdata g hg hLimAt
  -- the assembly: the seven functions `Ψ, A, B, A₁, A₂, B₁, B₂` with their within-slice
  -- derivatives, whence the closed-box `C²`-regularity
  exact Work.FTS_EllLimOK.ProducerH.BoxAux.contDiffOn_two_of_sliceData (le_of_lt hab)
    hP.1 hQ.1 hR.1 hQ.2.1 hR.2.1 hR.2.1 hR.2.2.1
    hP.2.1 hP.2.2 hQ.2.2.1 hQ.2.2.2 hR.2.2.2.1 hR.2.2.2.2

end Work.FTS_EllLimOK.ProducerH.H2
