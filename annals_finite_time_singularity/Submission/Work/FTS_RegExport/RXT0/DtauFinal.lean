import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS_RegExport.RXT0.DtauGeo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT0.DtauFinal` — the assembly of RX-T0 from its two black boxes

The two inputs (both delegated, both stated for the RX-T0 hypothesis bundle):

* `hRHS` — joint continuity on the slab of the `≤ 2` mixed jets of the transport expression
  `RHS α Φs E g σ` (the `HkIntegrand`-free version of "`gdot`'s jets are continuous");
* `hSlab` — the abstract slab `C¹`-lemma (`RXT0.slabC1`).

The assembly below produces exactly the RX-T0 conclusion, with the integral identity
`dtau_hId` and the Fréchet data `dtau_hasFDerivAt`/`dtau_Lcont`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT0

open Work.FTS.Galerkin (Fn Fam slice gdot)
open Work.FTS.Regularity (pExp)
open Work.FTS.FinalV2 (DynOK' EllLimOK3 Sol)
open Work.FTS.RegExportIface

set_option autoImplicit false

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}


end Work.FTS_RegExport.RXT0
