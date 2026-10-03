/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The `ORDivLoc` results in the vocabulary of `Work.ORFinal`

The bridge of this directory was developed against a *copy* (`Work.ORDivLoc.DivLoc`,
`Work.ORDivLoc.DivOn`) of the two definitions of `Work.ORFinal.AnalyticInput`, so that the
subproject does not have to be rebuilt every time the (separately maintained) `ORFinal` area
changes.  The two copies are definitionally identical; this file records that, and restates the
deliverable in the vocabulary of `Work.ORFinal`.
-/
import Submission.Work.ORDivLoc.Final
import Submission.Work.ORDivLoc.ToORFinalAux

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v

namespace Work.ORDivLoc

/-- `Work.ORDivLoc.DivOn` is `Work.ORFinal.DivOn` (same `letI`, same body). -/
theorem divOn_iff_orFinalDivOn {G : Type v} [Group G] {K : Type u} [Field K]
    (E : Work.ORVonNeumann.StarRegularEnvelope G) (φK : K →+* ℂ) (H : Subgroup G) :
    letI := Work.ORBridgeLinnell.kAlgebra E φK
    (DivOn E φK H ↔ Work.ORFinal.DivOn K E φK H) :=
  Iff.rfl

/-- `Work.ORDivLoc.DivLoc` is `Work.ORFinal.DivLoc` (same `letI`, same body): the copy in this
directory is definitionally the definition used by `Work.ORFinal`. -/
theorem divLoc_iff_orFinalDivLoc (K : Type u) [Field K] (G : Type v) [Group G] [Countable G]
    (φK : K →+* ℂ) : DivLoc K G φK ↔ Work.ORFinal.DivLoc K G φK :=
  Iff.rfl

/-- **The discharge of `Work.ORFinal.DivLoc` at `Type`** from the engine's construction
`thm61Step_nonempty` and [JZLA20, Proposition 3.11]. -/
theorem orFinalDivLoc_of_thm61StepComplex {G : Type} [Group G] [Countable G]
    (hHF : Prop311OnComplexClosure G) (hN6 : N6EngineInput)
    {K : Type} [Field K] (φK : K →+* ℂ) : Work.ORFinal.DivLoc K G φK :=
  (divLoc_iff_orFinalDivLoc K G φK).mp (divLoc_of_thm61StepComplex' hHF hN6 φK)

/-- **The `hdiv` field of `Work.ORFinal.FinalInput Unit`** (i.e. at universe `0`), discharged from

* the engine's construction `Work.ORHughesFree.Section6.thm61Step_nonempty` (as `hN6`, see
  `Work.ORDivLoc.N6EngineInput`), and
* [JZLA20, Proposition 3.11] over `ℂ` (as `h311`).

The copy of `FinalInput` at the universe `v` of the coefficient field is obtained from this one by
the reduction of P2: `Ring.Coherent.of_subfield` reduces the coefficient field `K : Type v` to its
finitely generated subfields, each of which is isomorphic to a (small) subfield of `ℂ`
(`Work.ORDivLoc.P2.ringCoherent_mapRingEquiv`), and the group `ULift.{v} X` is replaced by
`X : Type 0` (`Work.ORDivLoc.P2.ringCoherent_ulift_of_typeZero`). -/
theorem finalInputUnit_hdiv
    (h311 : ∀ (G : Type) [Group G] [Countable G], Prop311OnComplexClosure G)
    (hN6 : N6EngineInput) :
    ∀ (K : Type) [Field K] (G : Type) [Group G] [Countable G] (φK : K →+* ℂ),
      Work.ORFinal.DivLoc K G φK :=
  fun K _ G _ _ φK => orFinalDivLoc_of_thm61StepComplex (h311 G) hN6 φK

end Work.ORDivLoc
