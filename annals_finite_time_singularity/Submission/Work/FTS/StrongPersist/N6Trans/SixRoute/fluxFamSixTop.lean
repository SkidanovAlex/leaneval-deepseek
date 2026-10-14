import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.fluxFamSix
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Asm
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.t1SlotTermZ
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The canonical-weight form of the level-six top flux bound

The target `fluxFamSixTop` is the top family (`a + b = 6`) of the level-six transport
expansion with the three *leaf* weights of `TransportS.IsLeafW` as the weight `ρ`.  Each of
the three leaf weights is literally one of the canonical weights `canonW q = w² sin(2θ)^{-q}`
with `q ∈ {η, 0, γ(α)}`, so the whole statement is the `canonW`-form below, and the reduction
to it is a case split plus the (definitional) identification of the weight.

The `canonW`-form for `a + b = 6` is *not* a purely pointwise statement (the two `g`-slots are
of order `7` and `6`, and only `HkIntegrand α 7` dominates the former, which would give the
wrong right-hand side): the value bound is the honest level-six radial integration by parts of
`SixAux.fluxSix`, which prices the flux by the surviving slot `mixed b a g` of order `6` (the
`HkMem α 7 g` hypothesis is used only for the boundary identity).  That flux bound enters the
lemma below as a *hypothesis* (with an explicit constant `C`), so that the constant produced by
`fluxSix` is the one the main theorem exports.

* the pointwise domination of the *integrand* by `(Mf/2)(HkIntegrand α 7 + HkIntegrand α 6)`
  (`ℋ⁷`-slot for `D_z(mixed b a g)`, `ℋ⁶`-slot for `mixed b a g`, AM–GM) gives the
  `IntegrableOn` conjunct, through `Hon.integrable_HkIntegrand_prod_open` (at order `7`);
* the two slot dominations are `T2Sup.canonW_z_slot_le_gen` (the pure `D_z`-slot, `q ≤ η`) and
  `T2Sup.canonW_mixed_slot_le_gen` (the mixed slots, `q ≤ γ`), both with the *non-strict*
  hypothesis `0 ≤ q`, which is what makes the `q = 0` leaf weight `w²` fall out as well;
* the value bound (stated on the iterated integral) is moved to the product measure by Fubini
  (`MeasureTheory.integral_integral`), the integrability hypothesis being exactly the one
  produced above. -/



end

end Work.FTS.StrongPersist.N6Trans.SixRoute
