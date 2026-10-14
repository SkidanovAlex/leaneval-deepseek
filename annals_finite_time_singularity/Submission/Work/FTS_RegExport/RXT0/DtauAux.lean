import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.Sys.gdot_regular
import Submission.Work.FTS_RegExport.RXT.Sys.mixed_integral_identity
import Submission.Work.FTS_RegExport.RXT.coeff_C2
import Submission.Work.FTS_RegExport.RXT0.RXJets.coeffJetsJointCont
import Submission.Work.FTS_RegExport.RXVPMain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT0.DtauAux` — the auxiliary facts behind RX-T0

Two things:

* `DtauAux.gdotLoc_of_hyp`: the regularity package `GdotLoc S g` of `∂_τ g` (spatial `C²` at each
  fake time, with locally uniform jet bounds) for a family `g` satisfying the RX-T0 hypotheses.
  Assembled from the already-proved St1-chain leaves `Sys.coeff_jets` (`CoeffJets`),
  `RXT.coeff_C2` (`C²` of the coefficient slices), `Sys.gdot_eq_profile` (the `(E)`-form of the
  equation for the raw `g`) and `Sys.gdot_regular` (the producer of `GdotLoc`).
* `DtauAux.dtau_mii`: the integrated identity
  `D^β g(τ₂) − D^β g(τ₁) = ∫_{τ₁}^{τ₂} D^β(∂_τ g)(σ) dσ` for *every* `β = (b,a)` with
  `a + b ≤ 2`, packaged out of the six-component statement `Sys.mixed_integral_identity`.
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
