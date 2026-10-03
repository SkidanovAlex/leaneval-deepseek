/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Work.ORFinal.RingData`: the ring half with the `hinj` field discharged

`Work.ORAssembly.RingInputs K G` is the lead's interface for the L² (ring) half of Theorem 1.1: the
ambient ring `U = U(G)`, the Linnell datum `D_{K[G]}(U(G))`, a normal torsion-free finite-index
subgroup `G' ≤ G`, injectivity of `K[G] → D(G)`, `gl.dim K[G] ≤ 2` and
`Tor₂^{K[G]}(D(G), -) = 0`.

This file removes from that interface the field which is *not* an input at all:

* `hinj` — injectivity of `K[G] → D(G)` is Linnell independence at the trivial subgroup
  (`Work.ORAssembly.Ring.toS_injective`), a theorem about the datum, not a hypothesis.

The result is `Work.ORFinal.RingData K G`, whose fields are exactly the remaining inputs.
`Work.ORFinal.RingData.toRingInputs` fills `hinj` in, so every theorem of the assembly applies to a
`RingData`.

* `Work.ORFinal.RingData.ofEnvelope` — how to build a `RingData` from the M1 bridge
  (`Work.ORBridgeLinnell.linBridgeDataOf`, i.e. node N5's envelope + node N6's Hughes-free input +
  node N7's semisimplicity) plus nodes N4, N3 and N9.
* `Work.ORFinal.ringCoherent_of_ringData` — the ring half of Theorem 1.1 for a `RingData`.

The file also records the piece of node N3 that is *proved* here for every nontrivial relator
(`globalDim_le_two_of_ne_one`, from `Work.ORLyndon.globalDim_le_two_of_pow` and
`Work.OROneRel.exists_root`), together with its `ULift` transport, and the transport of the node N4
datum along `ULift`.
-/
import Submission.Work.ORAssembly.Main
import Submission.Work.ORReductions.API
import Submission.Work.ORLyndon.All
import Submission.Work.ORBridgeLinnell.Countable

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v w

namespace Work.ORFinal

open Work.ORAssembly

/-! ## The flatness conclusion of JL §5 at the M1 datum -/

/-- **The flatness conclusion of JL §5 at the datum built from an envelope and node N6's input.**

For a countable group `G`, a field `K` with an embedding into `ℂ` and the Hughes-free input `hin`
on the canonical envelope `E`, `FlatConclAt E φK hin` is `Tor₂^{K[G]}(D(G), -) = 0` for the Linnell
datum `D(G) ⊆ U(G)` of the M1 bridge.

It is phrased as a *definition* rather than a `letI`-expression in a hypothesis so that the
coefficient field and the group may be required to share a universe: `FlatConclAt` is available
only with `K : Type u` and `G : Type u`, which is exactly the constraint imposed by
`Work.ORAssembly.LinData.toS` and by `Work.ORFinal.RingData`. -/
def FlatConclAt (K : Type u) [Field K] {G : Type u} [Group G]
    (E : Work.ORVonNeumann.StarRegularEnvelope G) (φK : K →+* ℂ)
    (hin : Work.ORBridgeLinnell.HughesFreeInput K G E φK) : Prop :=
  letI := Work.ORBridgeLinnell.kAlgebra E φK
  Work.ORCoherence.TorTwoVanishes
    (Work.ORAssembly.LinData.toS (Work.ORBridgeLinnell.linnellDatumOfEnvelope E φK hin)).toRingHom

/-- `FlatConclAt` at the canonical envelope of a countable group. -/
def FlatConcl (K : Type u) [Field K] {G : Type u} [Group G] [Countable G] (φK : K →+* ℂ)
    (hin : Work.ORBridgeLinnell.HughesFreeInput K G
      (Work.ORBridgeLinnell.countableEnvelope G) φK) : Prop :=
  FlatConclAt K (Work.ORBridgeLinnell.countableEnvelope G) φK hin

/-! ## The interface -/

/-- **The ring half's per-presentation input, with `hinj` removed.**

`RingData K G` is `Work.ORAssembly.RingInputs K G` without the field `hinj`, which is proved from
the datum (`Work.ORAssembly.Ring.toS_injective`).  Every remaining field is a genuine input:

* `U`, `datum` — nodes N5 (envelope), N6 (Hughes-free division rings), N7 (semisimplicity);
* `G'`, `normal_G'`, `finiteIndex_G'`, `torsionFree_G'` — node N4;
* `hgl` — node N3 (Lyndon's identity theorem);
* `hTor` — node N9 (the flatness theorem of JL §5, from N3 + N8 + N1). -/
structure RingData (K : Type u) [Field K] [CharZero K] (G : Type u) [Group G] where
  /-- the ambient ring `U(G)` -/
  U : Type u
  [ringU : Ring U]
  [nontrivialU : Nontrivial U]
  [algebraU : Algebra K U]
  /-- the Linnell datum: the division closures `D H` of `K[H]` in `U(G)` -/
  datum : Work.ORLinnell.LinnellDatum K G U
  /-- node N4: a normal, finite-index, torsion-free subgroup -/
  G' : Subgroup G
  normal_G' : G'.Normal
  finiteIndex_G' : G'.FiniteIndex
  torsionFree_G' : IsMulTorsionFree G'
  /-- node N3: `gl.dim K[G] ≤ 2` -/
  hgl : Work.ORCoherence.globalDim (MonoidAlgebra K G) ≤ (2 : WithBot ℕ∞)
  /-- node N9: `Tor₂^{K[G]}(D(G), -) = 0` -/
  hTor : Work.ORCoherence.TorTwoVanishes (LinData.toS datum).toRingHom

attribute [instance] RingData.ringU RingData.nontrivialU RingData.algebraU

variable {K : Type u} [Field K] [CharZero K] {G : Type u} [Group G]

namespace RingData

/-- A `RingData` is a `RingInputs`: the only missing field, injectivity of `K[G] → D(G)`, is
Linnell independence at the trivial subgroup, i.e. `Work.ORAssembly.Ring.toS_injective`. -/
noncomputable def toRingInputs (D : RingData K G) : RingInputs K G where
  U := D.U
  ringU := D.ringU
  nontrivialU := D.nontrivialU
  algebraU := D.algebraU
  datum := D.datum
  G' := D.G'
  normal_G' := D.normal_G'
  finiteIndex_G' := D.finiteIndex_G'
  torsionFree_G' := D.torsionFree_G'
  hinj := Work.ORAssembly.Ring.toS_injective D.datum
  hgl := D.hgl
  hTor := D.hTor

/-- **Building a `RingData` from the M1 bridge.**  The `U`/`datum` fields are taken from
`Work.ORBridgeLinnell.LinBridgeData K G` (node N5's envelope, node N6's Hughes-free input, node
N7's semisimplicity); the remaining fields are nodes N4, N3 and N9. -/
noncomputable def ofLinBridge (D : Work.ORBridgeLinnell.LinBridgeData K G)
    (G' : Subgroup G) (hN : G'.Normal) (hfin : G'.FiniteIndex) (htf : IsMulTorsionFree G')
    (hgl : Work.ORCoherence.globalDim (MonoidAlgebra K G) ≤ (2 : WithBot ℕ∞))
    (hTor : Work.ORCoherence.TorTwoVanishes (LinData.toS D.datum).toRingHom) :
    RingData K G where
  U := D.U
  ringU := D.ringU
  nontrivialU := D.nontrivialU
  algebraU := D.algebraU
  datum := D.datum
  G' := G'
  normal_G' := hN
  finiteIndex_G' := hfin
  torsionFree_G' := htf
  hgl := hgl
  hTor := hTor

/-- **Building a `RingData` from node N5's envelope and node N6's input.**  The `U`/`datum` fields
are those of the M1 bridge `Work.ORBridgeLinnell.linBridgeDataOf E φK hin`; the remaining fields
are nodes N4, N3 and N9. -/
noncomputable def ofEnvelope (E : Work.ORVonNeumann.StarRegularEnvelope G) (φK : K →+* ℂ)
    (hin : Work.ORBridgeLinnell.HughesFreeInput K G E φK)
    (G' : Subgroup G) (hN : G'.Normal) (hfin : G'.FiniteIndex) (htf : IsMulTorsionFree G')
    (hgl : Work.ORCoherence.globalDim (MonoidAlgebra K G) ≤ (2 : WithBot ℕ∞))
    (hTor : FlatConclAt K E φK hin) :
    RingData K G :=
  ofLinBridge (Work.ORBridgeLinnell.linBridgeDataOf E φK hin) G' hN hfin htf hgl hTor

end RingData

/-- **The ring half of Theorem 1.1 for a `RingData`**: `K[G]` is coherent.

Node N7 (via `Work.ORLinnell.isSemisimpleRing_S`) makes `S = D(G)` semisimple; N3 and N9 supply
`gl.dim K[G] ≤ 2` and `Tor₂^{K[G]}(S, -) = 0`; JL Corollary 3.3 in the form of node N10
(`Work.ORCoherence.coherent_of_embeds_semisimple`) concludes. -/
theorem ringCoherent_of_ringData (D : RingData K G) : Ring.Coherent (MonoidAlgebra K G) :=
  Work.ORAssembly.ringCoherent_of_ringInputs D.toRingInputs

/-! ## The part of node N3 that is proved here -/

/-- **Node N3's `gl.dim K[G] ≤ 2` for every *nontrivial* relator**, unconditionally: Lyndon's
identity theorem in the form `Work.ORLyndon.globalDim_le_two_of_pow`, applied to the root of the
relator supplied by `Work.OROneRel.exists_root`.  (`PresentedGroup {r}` and
`Work.ORLyndon.OneRelatorGroup r` are the same type by definition.) -/
theorem globalDim_le_two_of_ne_one (n : ℕ) (r : FreeGroup (Fin n)) (hr : r ≠ 1) :
    Work.ORCoherence.globalDim
      (MonoidAlgebra K (PresentedGroup ({r} : Set (FreeGroup (Fin n))))) ≤ (2 : WithBot ℕ∞) := by
  obtain ⟨u, l, hl, hru, hu⟩ := Work.OROneRel.exists_root r hr
  exact Work.ORLyndon.globalDim_le_two_of_pow r u l hl hru hu hr

/-- `ULift` does not change the global dimension of the group algebra (the group may live in a
different universe from the coefficient field; the lift is taken into the field's universe). -/
theorem globalDim_le_two_ulift (K : Type v) [Field K] {H : Type u} [Group H]
    (h : Work.ORCoherence.globalDim (MonoidAlgebra K H) ≤ (2 : WithBot ℕ∞)) :
    Work.ORCoherence.globalDim (MonoidAlgebra K (ULift.{v} H)) ≤ (2 : WithBot ℕ∞) :=
  Work.ORLyndon.globalDim_le_of_ringEquiv
    (MonoidAlgebra.mapDomainRingEquiv K (MulEquiv.ulift (α := H)).symm) h

/-- `Ring.Coherent` of a group algebra is invariant under `ULift` of the group (the group may live
in a different universe from the coefficient field; the lift is taken into the field's universe). -/
theorem ringCoherent_ulift_group (K : Type v) [Semiring K] {H : Type u} [Group H] :
    Ring.Coherent (MonoidAlgebra K H) ↔
      Ring.Coherent (MonoidAlgebra K (ULift.{v} H)) :=
  ⟨fun h => Ring.Coherent.of_ringEquiv
      (MonoidAlgebra.mapDomainRingEquiv K (MulEquiv.ulift (α := H)).symm) h,
    fun h => Ring.Coherent.of_ringEquiv
      (MonoidAlgebra.mapDomainRingEquiv K (MulEquiv.ulift (α := H))) h⟩

/-! ## Transporting the node N4 datum along `ULift` -/

/-- **Node N4's datum is stable under `ULift` of the group**: a normal, finite-index,
`IsMulTorsionFree` subgroup of `H` pulls back to one of `ULift H`.  The anchor `X` pins the
universe of the lift (it plays no mathematical role). -/
theorem exists_subgroup_ulift (X : Type w) {H : Type u} [Group H]
    (h : ∃ G' : Subgroup H, G'.Normal ∧ G'.FiniteIndex ∧ IsMulTorsionFree G') :
    ∃ G'' : Subgroup (ULift.{w} H), G''.Normal ∧ G''.FiniteIndex ∧ IsMulTorsionFree G'' := by
  obtain ⟨G', hN, hfin, htf⟩ := h
  haveI : IsMulTorsionFree (↥G') := htf
  let K : FiniteIndexNormalSubgroup H :=
    { toSubgroup := G', isNormal' := hN, isFiniteIndex' := hfin }
  let K' : FiniteIndexNormalSubgroup (ULift.{w} H) :=
    FiniteIndexNormalSubgroup.comap (MulEquiv.ulift (α := H)).toMonoidHom K
  have hmt : IsMulTorsionFree (↥(K' : Subgroup (ULift.{w} H))) :=
    Function.Injective.isMulTorsionFree
      ({ toFun := fun x => (⟨(MulEquiv.ulift (α := H)) x.1, x.2⟩ : ↥G')
         map_one' := by ext; simp
         map_mul' := by intro a b; ext; simp } :
          ↥(K' : Subgroup (ULift.{w} H)) →* ↥G')
      (fun a b hab => by
        have h : (MulEquiv.ulift (α := H)) a.1 = (MulEquiv.ulift (α := H)) b.1 :=
          congrArg (fun z : ↥G' => (z : H)) hab
        exact Subtype.ext (MulEquiv.injective (MulEquiv.ulift (α := H)) h))
  exact ⟨(K' : Subgroup (ULift.{w} H)), K'.isNormal', K'.isFiniteIndex', hmt⟩

end Work.ORFinal
