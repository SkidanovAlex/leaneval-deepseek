/-
Copyright: work module for the Elgindi finite-time singularity project.

# `N6Trans/Hon/TraceDefs`: the honest boundary-trace predicate

The frozen level-4 transport clauses (`VocabO.T2Clause`/`T3Clause` and their per-slot
engines) are stated on `T2SG`/`T3SG`, whose `RegQ`-component carries `BdryTraces α 4 g`:
the *pointwise* vanishing, for every interior angle `θ`, of

`z · (D_z^bD_θ^a g z θ · w z)^2` as `z → 0⁺` and as `z → +∞`.

The honest level-six chapter (`StrongPersist.T2Clause6` and the three nodes
`N6Trans.IP4T*Honest`) replaces the `RegQ`-bundle by

`SmoothOpen g ∧ HkMem α 4 g ∧ HkMem α 5 g ∧ DecayAll 4 g`,

in which `BdryTraces` is *not* available as a hypothesis.  What *is* available is the pair of
weighted `L²`-integrability conditions at orders `4` and `5`, and the classical
`H¹`-argument (see `Hon/TraceBase.lean`) shows that those force the *same* traces — but only
for a.e. angle `θ`.  Since every consumer of the traces is an integral over `θ`, the a.e.
statement is exactly what is needed.

This file fixes that predicate (`TraceAe`).  It is the honest replacement for the
`BdryTraces`-component of `RegQ` in the transport clause.
-/
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.T2Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.Hon

set_option autoImplicit false

/-- **The honest boundary-trace predicate.**  For almost every angle `θ ∈ Iθ`, each of the
five order-`4` hard slots `Thard g k` (`k : Fin 5`) satisfies the two *radial* boundary
conditions of the frozen `BdryTraces α 4 g`: `z · (Thard g k z θ · w z)² → 0` both as
`z → 0⁺` and as `z → +∞`.

This is what replaces the `BdryTraces`-component of `RegQ α 4 g` in the honest transport
clauses; it is *derived* from `SmoothOpen g` together with `HkMem α 4 g` and `HkMem α 5 g`
in `Hon/TraceAe.lean`. -/
def TraceAe (g : ℝ → ℝ → ℝ) : Prop :=
  ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
    ∀ k : Fin 5,
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
        Filter.atTop (nhds 0)

end Work.FTS.StrongPersist.N6Trans.Hon
