import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS_EllLimOK.tower_jet_identities
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_RegExport.RXT.Sys.CoeffCont
import Submission.Work.FTS_RegExport.RXT.SysAux.bR_decomp
import Submission.Work.FTS_RegExport.RXT.coeff_C2
import Submission.Work.FTS_RegExport.RXT.st1_of_weighted
import Submission.Work.FTS_RegExport.RXT.velVanish2Aux
import Submission.Work.FTS_RegExport.RXT0.DtauAux
import Submission.Work.FTS_RegExport.RXT0.L12FKJetsJointCont
import Submission.Work.FTS_RegExport.RXT0.RXJets.L12FKJetsJointCont
import Submission.Work.FTS_RegExport.RXT0.RXJets.coeffJetsJointCont
import Submission.Work.FTS_RegExport.RXT0.RXJets.coeffcR
import Submission.Work.FTS_RegExport.RXT0.RXJets.jetBasic
import Submission.Work.FTS_RegExport.RXT0.slotJetsJointCont
import Submission.Work.FTS_RegExport.RXVPMain
import Submission.Work.H2W.weakSliceZContinuousAe
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
-- ===== merged: Submission.Work.FTS_RegExport.RXT0.DtauProto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT0.DtauProto` — the assembly of RX-T0

The pieces, with the RX-T0 hypotheses in force:

* `dtau_jet_eq`: on the open quadrant, the mixed jets of `gdot g σ` and of the transport
  expression `RHS α Φs E g σ` agree for `σ ∈ (0,S]` (both are the `(E)`-form of the equation).
* `dtau_hId`: the integral identity
  `D^β g(τ) = D^β g(0) + ∫_0^τ D^β(RHS)(σ) dσ` for every `β = (b,a)`, `a + b ≤ 2`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT0

open Work.FTS.Galerkin (Fn Fam slice gdot)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp)
open Work.FTS.RegPkgGal (extG St1Class)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)
open Work.FTS.RegExportIface

set_option autoImplicit false

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}



end Work.FTS_RegExport.RXT0
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT0.RHSJetsJointCont =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT0.RHSJetsJointCont` — joint continuity of the `RHS` jets (RX-T0)

The target: for a family `g` satisfying the RX-T0 hypotheses, the mixed jets
`D_z^b D_θ^a (RHS α Φs E g σ)`, `a + b ≤ 2`, are jointly continuous on the slab
`z > 0`, `θ ∈ (0,π/2)`, `σ ∈ [0,S]`, for every `S > 0`.

The route is the Leibniz expansion of the three summands of
`RHS σ = -(VR σ · D_zF(σ) + bR σ · D_θF(σ) + cR σ · F(σ))`:

* the *profile* jets `mixed k l (FtauS α g σ)` (`k + l ≤ 3`) are jointly continuous by
  `jc3` (joint continuity of the order-`≤ 3` slice jets) plus the explicit smooth term `F_*`
  (`profileJetsJointCont` below);
* `productJetsCont` turns the profile jets and the (jointly continuous) coefficient jets into
  the continuity of the Leibniz sum;
* the coefficient jets come from the leaves `RXJets.L12FKJetsJointCont` and
  `RXJets.coeffJetsJointCont` (whose input is the proved `RXT0.slotJetsJointCont`);
* `mixed_RHS_eq_Icc` (the `σ ∈ [0,S]` version of `Sys.mixed_RHS_eq`) splits `RHS` into its
  three summands `Afun`, `Bfun`, `Cfun` on the slab, so the result follows from the continuity
  of the three Leibniz products.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT0

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Regularity (pExp)
open Work.FTS.FinalV2 (Sol DynOK' EllLimOK3)
open Work.FTS.RegExportIface.RXT (GR ΦR μR VR bR cR)

set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}

/-- The RX-T0 slab `(0,∞) × (0,π/2) × [0,S]`. -/
abbrev Slab (S : ℝ) : Set (ℝ × ℝ × ℝ) :=
  Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)

/-! ## §1 The profile jets `mixed k l (F(σ))` are jointly continuous (`k + l ≤ 3`) -/



/-! ## §2 The generic Leibniz product -/


/-! ## §3 The `σ ∈ [0,S]` split of `RHS` into its three summands -/



/-! ## §4 The assembly -/



end Work.FTS_RegExport.RXT0
end
end
