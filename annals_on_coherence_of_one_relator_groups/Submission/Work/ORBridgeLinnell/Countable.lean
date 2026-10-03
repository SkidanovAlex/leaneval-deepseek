/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The M1 bridge for countable groups and for the one-relator presentations

Node N5's envelope is available for every *countable* group
(`Work.ORVonNeumann.countableStarRegularEnvelopeOfCountable`).  This file fixes the canonical
choice `Work.ORBridgeLinnell.countableEnvelope G` and applies the bridge `linBridgeDataOf` to it,
producing the `U`/`datum` fields of `Work.ORAssembly.RingInputs`:

* `Work.ORBridgeLinnell.linBridgeDataOfCountable` — for `G` countable, any `φK : K →+* ℂ` and any
  Hughes-free / Ore input in the sense of `Work.ORBridgeLinnell.HughesFreeInput`;
* `Work.ORBridgeLinnell.linBridgeDataOfPresentedGroup` — for the finitely generated one-relator
  presentations `⟨Fin n | r⟩` used by the assembly's `hRingQ`;
* `Work.ORBridgeLinnell.linBridgeDataOfULiftPresentedGroup` — the same for
  `ULift (⟨Fin n | r⟩)`, the groups used by the assembly's `hRingK`;
* `Work.ORBridgeLinnell.linBridgeDataRat` — the case `K = ℚ`, with the canonical embedding
  `ℚ →+* ℂ`.
-/
import Mathlib
import Submission.Work.ORBridgeLinnell.Bridge

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORBridgeLinnell

open Work.ORVonNeumann

variable {G : Type*} [Group G] {K : Type*} [Field K]

/-- The free group on a countable generating type is countable (Mathlib has no instance for
this; `FreeGroup.mk : List (α × Bool) → FreeGroup α` is surjective). -/
instance instCountableFreeGroup (α : Type*) [Countable α] [DecidableEq α] :
    Countable (FreeGroup α) :=
  Function.Surjective.countable (f := FreeGroup.mk) fun x => ⟨x.toWord, FreeGroup.mk_toWord⟩

/-- The presented group `⟨α | r⟩` on a countable generating type is countable (Mathlib has no
instance for this; it is a quotient of `FreeGroup α`). -/
instance instCountablePresentedGroup (α : Type*) [Countable α] [DecidableEq α]
    (r : Set (FreeGroup α)) : Countable (PresentedGroup r) :=
  inferInstanceAs (Countable (Quotient (QuotientGroup.leftRel (Subgroup.normalClosure r))))

/-- **The canonical N5 envelope for a countable group**: the *concrete* envelope
`Work.ORVonNeumann.countableStarRegularEnvelope`, whose `U` is the ring of affiliated operators
`U(G)`, `ι` the inclusion `ℂ[G] ↪ U(G)` and `sub` the inclusion `U(H) ↪ U(G)` with Linnell
independence.

Until 2026-10-02 this was `Classical.choice (countableStarRegularEnvelopeOfCountable)`, i.e. an
*arbitrary* `StarRegularEnvelope`; since the interface `StarRegularEnvelope` does not force
`D_{K[H]}` to be a division ring, the statements about it (`Work.ORFinal.DivLoc` in particular)
were statements about an unknown model and were not provable.  The concrete model is obtained by
pinning the measurable structure of `G` to the discrete one, exactly as in
`Work.ORVonNeumann.countableStarRegularEnvelopeOfCountable`. -/
noncomputable def countableEnvelope (G : Type*) [Group G] [Countable G] : StarRegularEnvelope G := by
  letI : MeasurableSpace G := ⊤
  haveI : MeasurableSingletonClass G := ⟨fun _ => trivial⟩
  haveI : MeasurableMul G := ⟨fun _ => fun s _ => trivial, fun _ => fun s _ => trivial⟩
  exact countableStarRegularEnvelope

/-- **The M1 bridge for a countable group.**  Node N5's envelope for `G`, the field embedding
`φK : K →+* ℂ` and the two analytic inputs of node N6 (`HughesFreeInput`) produce the `U`/`datum`
fields of `Work.ORAssembly.RingInputs`. -/
noncomputable def linBridgeDataOfCountable (K : Type*) [Field K] (G : Type*) [Group G]
    [Countable G] (φK : K →+* ℂ) (hin : HughesFreeInput K G (countableEnvelope G) φK) :
    LinBridgeData K G :=
  linBridgeDataOf (countableEnvelope G) φK hin

/-- **The M1 bridge for the one-relator presentations `⟨Fin n | r⟩`** of the assembly's `hRingQ`. -/
noncomputable def linBridgeDataOfPresentedGroup (K : Type*) [Field K] (n : ℕ)
    (r : FreeGroup (Fin n)) (φK : K →+* ℂ)
    (hin : HughesFreeInput K (PresentedGroup ({r} : Set (FreeGroup (Fin n))))
      (countableEnvelope (PresentedGroup ({r} : Set (FreeGroup (Fin n))))) φK) :
    LinBridgeData K (PresentedGroup ({r} : Set (FreeGroup (Fin n)))) :=
  linBridgeDataOfCountable K _ φK hin

/-- **The M1 bridge for `ULift (⟨Fin n | r⟩)`**, the groups of the assembly's `hRingK`. -/
noncomputable def linBridgeDataOfULiftPresentedGroup (K : Type*) [Field K] (n : ℕ)
    (r : FreeGroup (Fin n)) (φK : K →+* ℂ)
    (hin : HughesFreeInput K (ULift (PresentedGroup ({r} : Set (FreeGroup (Fin n)))))
      (countableEnvelope (ULift (PresentedGroup ({r} : Set (FreeGroup (Fin n)))))) φK) :
    LinBridgeData K (ULift (PresentedGroup ({r} : Set (FreeGroup (Fin n))))) :=
  linBridgeDataOfCountable K _ φK hin

/-- **The M1 bridge at `K = ℚ`**, with the canonical embedding `algebraMap ℚ ℂ`. -/
noncomputable def linBridgeDataOfCountableRat (G : Type*) [Group G] [Countable G]
    (hin : HughesFreeInput ℚ G (countableEnvelope G) (algebraMap ℚ ℂ)) : LinBridgeData ℚ G :=
  linBridgeDataOfCountable ℚ G (algebraMap ℚ ℂ) hin

/-- **The M1 bridge at `K = ℚ` for the one-relator presentations** — the input of the assembly's
`hRingQ`. -/
noncomputable def linBridgeDataOfPresentedGroupRat (n : ℕ) (r : FreeGroup (Fin n))
    (hin : HughesFreeInput ℚ (PresentedGroup ({r} : Set (FreeGroup (Fin n))))
      (countableEnvelope (PresentedGroup ({r} : Set (FreeGroup (Fin n))))) (algebraMap ℚ ℂ)) :
    LinBridgeData ℚ (PresentedGroup ({r} : Set (FreeGroup (Fin n)))) :=
  linBridgeDataOfCountable ℚ _ (algebraMap ℚ ℂ) hin

end Work.ORBridgeLinnell
