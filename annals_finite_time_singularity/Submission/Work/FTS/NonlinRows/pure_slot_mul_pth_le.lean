import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.FinalClock.PhysClock
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.FinalClock.MuBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology Interval

namespace Work.FTS.FinalClock

open Work.Construction (L12 N0 N Ftau mufunS)
open Work.Spaces (HkNorm Dth)
open Work.FTS.Galerkin (Fam slice muDyn)

/-! ## The bridge from `L₁₂`-estimates to the `ℋ⁴` norm -/



/-! ## The arithmetic of `muDyn_small` -/





/-! ## `muDyn_small` -/





/-! ## The usable consequence: `|muDyn| ≤ 1/2` -/


end Work.FTS.FinalClock
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow10aux.starProdPt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows.NRow10aux

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.Spaces

/-!
## The pointwise product bound `HkIntegrand α 4 (R·g) ≤ C K² HkIntegrand α 4 g`

`R` is a coefficient whose `D_z`-iterates are bounded by `K` and whose mixed derivatives of
angular order `≥ 1` are bounded by `K · sin 2θ`; `g` is an arbitrary function.  The claim is
the pointwise domination of the `H⁴`-integrand of the product `R·g` by `K²` times that of `g`.

The proof is the binomial expansion of `D_z^i (R·g)` resp. `D_z^j D_θ^i (R·g)`
(`leibniz_open_Dz`, `leibniz_open_mixed`), Cauchy–Schwarz on the resulting finite sums
(`sq_sum_le_card_mul_sum_sq`), and the two facts that each Leibniz summand is (i) bounded by
`K` or `K sin 2θ` in its `R`-factor and (ii) a genuine summand of `HkIntegrand α 4 g`.
The single analytic input is
`(sin 2θ · Wt α z θ)² ≤ (w z / sin(2θ)^{η/2})²`, which makes up the deficit of one power of
`sin 2θ` left over by the `R`-factor in the case where every angular derivative falls on `R`.
-/






end Work.FTS.NonlinRows.NRow10aux
end
-- ===== merged: Submission.Work.FTS.NonlinRows.pure_slot_mul_pth_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

set_option maxHeartbeats 1000000

/-! ## The weight comparison -/


/-! ## The pointwise estimate -/



end Work.FTS.NonlinRows
end
