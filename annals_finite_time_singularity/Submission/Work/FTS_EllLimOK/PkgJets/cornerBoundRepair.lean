import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_const_mul
import Submission.Work.FTS.StrongPersist.H6Aux.RStep
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBound
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.PkgRepair
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.bt_integral_weight_id
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.ClassCDiffData =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **`ℋ⁵`-honesty of a profile of the linear class `ClassC α`**, by the monotonicity of the
`ℋ`-integrand in the order (`ClassC` carries `HkMem α 7`, and `7 ≥ 5`). -/
private theorem cdd_hkMem_five_of_classC {α : ℝ} {g : Fn}
    (h : Work.FTS.ClassC.ClassC α g) : Work.Spaces.HkMem α 5 g :=
  Work.FTS.OpenPkg.HkMem_mono_open (k := 7) h.reg 5 (by norm_num) h.mem

/-- **`|f|_{ℋ⁴} ≤ |f|_{ℋ⁵}`** for an honest `ℋ⁵`-function: the two sides are the square roots of
`HkSq α 4 f` and `HkSq α 5 f`, and the squared integrand is monotone in the order. -/
private theorem cdd_Xn_le_Xn5 {α : ℝ} {f : Fn} (h5 : Work.Spaces.HkMem α 5 f) :
    Work.FTS.Nonlin.Xn α f ≤ Work.FTS.GalFields.Xn5 α f :=
  Real.sqrt_le_sqrt (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) h5)

/-- **The open-quadrant data of the difference of two `ClassC` profiles.**

Every field of the bundle `ClassCDiffFacts α W₁ W₂` (about `h = W₁ - W₂`, about the radial
function `L₁₂(h)`, and about the `D_θ`/`D_z`-fields of `W₂`) follows from `ClassC α W₁`,
`ClassC α W₂` and the analytic tools of the open-quadrant calculus. -/
theorem ClassCDiffData {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {W₁ W₂ : Work.FTS.Galerkin.Fn}
    (hW₁ : Work.FTS.ClassC.ClassC α W₁) (hW₂ : Work.FTS.ClassC.ClassC α W₂) :
    Work.FTS.StrongEps.EpsRLX.ClassCDiffFacts α W₁ W₂ := by
  -- `ClassC` is a linear class, so the difference is again in it: this supplies, in one stroke,
  -- the open-quadrant smoothness, the `ℋ⁷`-honesty and the `L₁₂`-data of `h = W₁ - W₂`.
  have hsub : Work.FTS.ClassC.ClassC α (fun z θ => W₁ z θ - W₂ z θ) :=
    Work.FTS.StrongEps.EComparison.classC_sub hW₁ hW₂
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => W₁ z θ - W₂ z θ) := hsub.reg
  have hmem5 : Work.Spaces.HkMem α 5 (fun z θ => W₁ z θ - W₂ z θ) :=
    cdd_hkMem_five_of_classC hsub
  have hmem5₁ : Work.Spaces.HkMem α 5 W₁ := cdd_hkMem_five_of_classC hW₁
  have hmem5₂ : Work.Spaces.HkMem α 5 W₂ := cdd_hkMem_five_of_classC hW₂
  exact
    ⟨hsm,
     hmem5,
     cdd_Xn_le_Xn5 hmem5,
     -- `D_θh`
     hsm.Dth,
     Work.FTS.StrongEps.ClassCRHS.hkMem_Dth_of_smoothOpen hα 4 hsm hmem5,
     Work.FTS.GalFields.Xn_Dth_le_Xn5 hα hmem5,
     -- `D_zh`
     hsm.Dz,
     Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 4 hsm hmem5,
     Work.FTS.GalFields.Xn_Dz_le_Xn5 hα hsm hmem5,
     -- the radial function `L₁₂(h)`
     Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα hsub,
     hsub.l12,
     Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα hW₁,
     -- the two profiles
     cdd_Xn_le_Xn5 hmem5₁,
     cdd_Xn_le_Xn5 hmem5₂,
     -- `D_θW₂`
     hW₂.reg.Dth,
     Work.FTS.StrongEps.ClassCRHS.hkMem_Dth_of_smoothOpen hα 4 hW₂.reg hmem5₂,
     Work.FTS.GalFields.Xn_Dth_le_Xn5 hα hmem5₂,
     -- `D_zW₂`
     hW₂.reg.Dz,
     Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 4 hW₂.reg hmem5₂,
     Work.FTS.GalFields.Xn_Dz_le_Xn5 hα hW₂.reg hmem5₂⟩

end Work.FTS.StrongEps.EpsRLX
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.boxConvOnCbox =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS_EllLimOK.PkgJets


end Work.FTS_EllLimOK.PkgJets
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.cornerBoundRepair =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.PkgJets

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## §1  The repaired corner field -/


/-! ## §2  The crux: a uniform box bound along a `LimSeq4` -/


/-! ## §3  The consumption: closed-box `C²`-regularity of a cluster limit -/


/-! ## §4  Why the other fields of `HasPkgE` see nothing at the angular endpoints -/







end Work.FTS_EllLimOK.PkgJets
end
end
