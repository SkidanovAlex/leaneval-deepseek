import Mathlib
import Submission.Work.RPB1a.Defs

/-!
# `Work.RPB.B1a.RiemannMapNodeSmooth`: node N6 in the form the analytic route can discharge

The route's node N6 (`Work.RPB1a.RiemannMapNode`) asks, for an arbitrary Jordan domain `D`
(`hJ : Work.RPB1a.IsJordanCurveSet (frontier D)`), for a conformal map of the disc onto `D` extending
continuously and injectively to the closed disc.  Its *general* form is Carathéodory's boundary
correspondence for topological Jordan domains, which is a substantial development in its own right.

In the route, however, `D` is always produced by node N4 from a **smooth** loop `v` with
`frontier D = Set.range v`, and the in-house development `Submission/Work/RPB/B1a/` proves the
boundary correspondence *in that smooth case* (`Work.RPB.B1a.caratheodory_boundary_of_smooth`, plus
the Riemann map itself, `Work.RPB.B1a.riemannMap_exists`).  This file states the node in exactly that
form: the extra hypotheses `Work.RPB1a.IsSmoothLoop v` and `frontier D = Set.range v` are what the
smooth proof needs, and the chain that consumes the node has them at the point of use.

This is the vocabulary of the chain `Submission/Work/RPB/B1a/loopFamily_chain.lean`, which is a
smooth-boundary variant of `Work.RPB1a.loopFamily_chain_of_nodes`.  Note the loop predicates are the
route's own (`Work.RPB1a.IsSmoothLoop`), so that this file is importable from that chain without
shadowing any route vocabulary.
-/

open Complex Set Metric
open scoped ContDiff Real

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B1a

/-- **N6, smooth-boundary form**: for a smooth loop `v` bounding a Jordan domain `D`
(`frontier D = Set.range v`) whose complement is connected, there is a biholomorphism
`Φ` of the unit disc onto `D` extending continuously and injectively to the closed disc, carrying
the circle into the curve, with `deriv Φ 0` a positive real. -/
def RiemannMapNodeSmooth : Prop :=
  ∀ (v : ℝ → ℂ), Work.RPB1a.IsSmoothLoop v → ∀ (D : Set ℂ), IsOpen D → IsConnected D →
    Bornology.IsBounded D → IsConnected Dᶜ → frontier D = Set.range v →
    ∃ Φ : ℂ → ℂ, ContinuousOn Φ (Metric.closedBall 0 1) ∧
      DifferentiableOn ℂ Φ (Metric.ball 0 1) ∧ Set.InjOn Φ (Metric.closedBall 0 1) ∧
      Φ '' Metric.ball 0 1 = D ∧ Set.MapsTo Φ (Metric.sphere 0 1) (Set.range v) ∧
      ∃ a : ℝ, 0 < a ∧ deriv Φ 0 = a

end Work.RPB.B1a
