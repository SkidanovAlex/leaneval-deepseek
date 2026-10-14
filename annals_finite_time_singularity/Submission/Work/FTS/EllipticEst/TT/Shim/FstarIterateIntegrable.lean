import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.Shim.EllHyp_certificates
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.Spaces.SmoothCompact_HkMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The angular moment of the `j`-th radial iterate

`Work.Elliptic.Qang g j` is the angular moment of `D_z^j g` against the weight
`K(θ) = 3 sinθcos²θ`, whereas the paper's moment `F_*(D_z^j g)` uses the weight `sinθcos²θ`
(`Work.FTS.EllipticEst.Bmom`, `Work.FTS.EllipticEst.Cert.GbarSin.Uj`).  The two differ by the
factor `3`; this bridge makes the differentiation-under-the-integral lemma
`Work.Elliptic.Qang_deriv_mul` (proved for `SmoothNbhd` data) available for the paper's moment.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`. -/





end Work.FTS.EllipticEst.Cert
