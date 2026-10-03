/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Node N6's input at the `∗`-regular closure, and `DivLoc` from it

This file records, for an arbitrary coefficient field `K`, the statement

`Work.ORDivLoc.HstepOn K G φK` — the JZLA20 engine's induction environment
`Work.ORHughesFree.Thm61Step K ↥H V_H (starClosureCod E φK H) H₀` exists for every locally
indicable `H ≤ G` and every finitely generated non-trivial `H₀ ≤ ↥H`, where `V_H` is the
`∗`-regular closure of the image of `K[H]` in `U(G) = countableEnvelope G` — and the two theorems
`Work.ORDivLoc.clDivLoc_of_hstep`, `Work.ORDivLoc.divLoc_of_hstep` that turn it into `DivLoc`.

## Use `HstepOnComplex`, not `HstepOn`

`HstepOn K G φK` is the conclusion of
`Work.ORHughesFree.Section6.thm61Step_nonempty (hpos) (φ) (rkU) (hfaith) (hφ) (hstar) (hHF)`
at `(V_H, starClosureCod E φK H)`.  Its construction needs `IsEpic (starClosureCod E φK H)`, which
is **false** for a general coefficient field `K` (the stars of the scalars need not be ring
expressions in the image — see the counterexample in
`Submission/Work/ORDivLoc/Closure/isEpic_starClosureCod.lean`), and **true** for `K = ℂ`
(`Work.ORDivLoc.Closure.isEpic_starClosureCod_complex`).  The primary interface is therefore the
`ℂ`-version

`Work.ORDivLoc.HstepOnComplex G` — the same statement with `K = ℂ`, `φK = id`, for the canonical
envelope — used by `Work.ORDivLoc.Final`:

* `Work.ORDivLoc.divLoc_of_thm61StepComplex' : Prop311OnComplexClosure G → N6EngineInput →
  DivLoc K G φK` (all side conditions discharged),
* `Work.ORDivLoc.finalInputUnit_hdiv` — the `hdiv` field of `Work.ORFinal.FinalInput Unit`,

and the reduction from an arbitrary `φK : K →+* ℂ` to `ℂ` is `Work.ORDivLoc.Complex`
(`divOn_of_complexClosureDivOn`, via `V_K ⊆ V_ℂ` and division closedness).

The definitions `HstepOn`, `ClDivLoc`, `DivLoc`, `DivOn` below are (definitionally) the ones used
by the rest of the directory; `HstepOn` is kept because it is the `K`-vocabulary form of the same
statement, and specialising it at `ℂ` — up to the (propositionally equal, not definitionally equal)
choice of `ℂ`-algebra structure on `U(G)`: the envelope's own, used here, versus
`Work.ORBridgeLinnell.kAlgebra E (RingHom.id ℂ)` — recovers `HstepOnComplex`.
-/
import Submission.Work.ORDivLoc.N6

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORDivLoc

/-- **Node N6's raw input at the `∗`-regular closure, for every locally indicable `H ≤ G`.**

The engine's induction environment `Work.ORHughesFree.Thm61Step` for the pair
`(↥H, ∗-regular closure V_H of the image of K[H] in U(G))` and the structure map
`K[H] →+* V_H`, for every finitely generated non-trivial `H₀ ≤ ↥H`.  This is the conclusion of
`Work.ORHughesFree.Section6.thm61Step_nonempty`; see the module docstring for the list of its
inputs and where each is proved or converted. -/
def HstepOn (K : Type) [Field K] (G : Type) [Group G] [Countable G] (φK : K →+* ℂ) : Prop :=
  letI := Work.ORBridgeLinnell.kAlgebra (Work.ORBridgeLinnell.countableEnvelope G) φK
  ∀ H : Subgroup G, Work.ORLocInd.Group.LocallyIndicable H →
    ∀ H₀ : Subgroup ↥H, H₀.FG → H₀ ≠ ⊥ →
      Nonempty (Work.ORHughesFree.Thm61Step K ↥H
        (↥(starClosureOfSubgroup (Work.ORBridgeLinnell.countableEnvelope G) φK H))
        (starClosureCod (Work.ORBridgeLinnell.countableEnvelope G) φK H) H₀)

/-- **Node N6's output `ClDivLoc`, from the raw input `HstepOn`.** -/
theorem clDivLoc_of_hstep {K : Type} [Field K] {G : Type} [Group G] [Countable G]
    (φK : K →+* ℂ) (h : HstepOn K G φK) : ClDivLoc K G φK := by
  letI := Work.ORBridgeLinnell.kAlgebra (Work.ORBridgeLinnell.countableEnvelope G) φK
  intro H hLI
  exact clDivOn_of_hstep φK (h H hLI)

/-- **The deliverable: `DivLoc` from node N6's raw input.**  This is the theorem that discharges
`Work.ORFinal.FinalInput.hdiv` (at `Type`) once
`Work.ORHughesFree.Section6.thm61Step_nonempty` is available. -/
theorem divLoc_of_hstep {K : Type} [Field K] {G : Type} [Group G] [Countable G]
    (φK : K →+* ℂ) (h : HstepOn K G φK) : DivLoc K G φK :=
  divLoc_of_clDivLoc K G φK (clDivLoc_of_hstep φK h)

end Work.ORDivLoc
