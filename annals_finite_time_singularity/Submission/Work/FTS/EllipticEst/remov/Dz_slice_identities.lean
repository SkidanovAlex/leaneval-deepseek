import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.TruncIdentAe
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.BslZsq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.uncurry_partial_c1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-! ## The two slice identities

The first identity is the `m = 1`, `i = 0` instance of
`Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_mixed_open` (i.e. `z²∂_z²` commutes with
`D_z = z∂_z`).  The second is the commutation of `∂_z` with the iterated `∂_θ`, which is
Clairaut's theorem iterated, together with the trivial commutation of `∂_θ` with the
`z`-multiplication. -/

end Work.FTS.EllipticEst.remov
