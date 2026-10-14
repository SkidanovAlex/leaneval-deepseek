import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.HkMem_mono
import Submission.Work.Coercivity.L2CoercivityTransport
import Submission.Work.Coercivity.L2CoercivityTransportEta
import Submission.Work.Coercivity.slice_ibp_eta
import Submission.Work.FTS.CoercivityStep.Step.Coercive
import Submission.Work.FTS.CoercivityStep.Step.HkIPStep_core
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.StrongPersist.L3Aux.acoef_gamCoef_slots_le
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.Coercivity.firstTransportCoercivity =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false



end Work.Coercivity
end
end
-- ===== merged: Submission.Work.FTS.CoercivityStep.Step =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityStep

set_option autoImplicit false

open Work.FTS.CoercivityStep.Norm (HkAdm_mono HkSq_Dth_le HkSq_Dz_le HkSq_mono_le)

/-! ## Descending the regularity class -/

theorem HkReg.mono {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ} (h : HkReg α (k + 1) f) :
    HkReg α k f :=
  ⟨h.1, Work.Coercivity.HkMem_mono α k h.1 h.2⟩

theorem HkReg.dth {α : ℝ} (hα : 0 < α) {k : ℕ} {f : ℝ → ℝ → ℝ}
    (h : HkReg α (k + 1) f) : HkReg α k (Work.Spaces.Dth f) :=
  ⟨h.1.Dth, (Work.Coercivity.HkMem_dth α hα k h.1 h.2).1⟩

theorem HkReg.dz {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ} (h : HkReg α (k + 1) f) :
    HkReg α k (Work.Spaces.Dz f) :=
  ⟨h.1.Dz, Work.Coercivity.HkMem_dz_free α k h.1 h.2⟩

/-! ## The Cauchy–Schwarz bound of the new pairing, with its explicit constant -/



/-! ## The induction step -/


end Work.FTS.CoercivityStep
end
end
