/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Node N14: the final assembly of Theorem 1.1

`Work.ORAssembly.theorem_1_1_of_nodes` is the complete assembly of

> **Theorem 1.1** (Jaikin-Zapirain--Linton, *Annals* 201, 2025).  Every one-relator group `G` is
> coherent, and `K[G]` is coherent for every field `K` of characteristic zero.

from the node-level inputs of the route design.  The *delivered* nodes are used verbatim (nodes N0,
N1, N5, N7, N8, N9, N10, N11 appear as proofs, not as hypotheses); the *open* nodes appear as the
explicit hypotheses

* `HN : NodeInputs` — N2 (`combinatorics`), N12 (`hnnTree`, `coprodTree`, `quotientTree`,
  `freeOnTree`, `bassSerre`) and N13 (`dunwoody`), see `Submission/Work/ORAssembly/Defs.lean`;
* `hRingQ`, `hRingK : ∀ G, OneRelator G → RingInputs _ G` — the ring half's inputs at `ULift ℚ`
  (for the group half) and at the field `K`, see `Submission/Work/ORAssembly/RingHalf.lean`;
  their fields are N5, N6 (via the Linnell datum), N4 (via `G'`), N3 (`hgl`) and N9 (`hTor`).

`README.md` records, for every hypothesis, which open node owes it and which interface mismatch
prevents the corresponding delivered theorem from being applied directly.
-/

import ChallengeDeps
import Submission.Work.ORAssembly.Defs
import Submission.Work.ORAssembly.GroupHalf
import Submission.Work.ORAssembly.RingHalf
import Submission.Work.ORAssembly.Coherent.freeGroup_coherent
import Submission.Work.ORAssembly.Ulift.ringCoherent_ulift
import Submission.Work.ORAssembly.Ring.toS_injective
import Submission.Work.ORAssembly.FP2.homologicallyCoherent_of_mulEquiv
import Submission.Work.ORAssembly.FP2.homologicallyCoherent_of_fg
import Submission.Work.ORAssembly.OneRelator.oneRelator_ulift
import Submission.Work.ORFP2.BieriStrebelBridge
import Submission.Work.ORDunwoody.Bridge

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped TensorProduct

open CategoryTheory Limits

universe u v w

namespace Work.ORAssembly

open Work.ORDunwoody

/-! ## Small bridges -/

/-- `ULift` of a ring of characteristic zero has characteristic zero (Mathlib has the `ULift`
instances for `AddMonoidWithOne` and `NatCast`, but not this one). -/
instance instCharZeroULift (K : Type u) [AddMonoidWithOne K] [CharZero K] :
    CharZero (ULift.{w} K) :=
  ⟨fun n m h => Nat.cast_injective (R := K) (ULift.up.inj (by
    rw [← show (n : ULift.{w} K) = ULift.up (n : K) from rfl, h]
    rfl))⟩

/-- **Node N11, in the vocabulary of node N13**: if `k[G]` is coherent then every finitely
generated subgroup of `G` is of type `FP₂(k)` (JL's remark after Theorem 4.7).  This is the
transfer that lets the ring half feed the group half. -/
theorem homologicallyCoherent_of_coherent {k : Type v} [CommRing k] {G : Type u} [Group G]
    (h : Ring.Coherent (MonoidAlgebra k G)) : Work.ORDunwoody.HomologicallyCoherent k G :=
  fun H hH => (Work.ORDunwoody.isFP2_iff_ORFP2 k ↥H).mpr
    (Work.ORFP2.IsFP2_of_coherent_monoidAlgebra k G H hH h)

/-- Coherence of `K[G]` is invariant under replacing the *coefficient field* by `ULift K`. -/
theorem ringCoherent_ulift_coeff (K : Type w) (G : Type w) [Semiring K] [Monoid G] :
    Ring.Coherent (MonoidAlgebra K G) ↔ Ring.Coherent (MonoidAlgebra (ULift.{w} K) G) :=
  ⟨fun h => Ring.Coherent.of_ringEquiv
      (MonoidAlgebra.mapRingEquiv G
        (ULift.ringEquiv (R := K) : ULift.{w} K ≃+* K)).symm h,
    fun h => Ring.Coherent.of_ringEquiv
      (MonoidAlgebra.mapRingEquiv G
        (ULift.ringEquiv (R := K) : ULift.{w} K ≃+* K)) h⟩

/-- **Constructing the ring inputs from their mathematical content.**  Every field of
`RingInputs` except `hinj` is an input; `hinj` is a *consequence* of the Linnell datum (Linnell
independence at the trivial subgroup), proved in `Submission/Work/ORAssembly/Ring/toS_injective.lean`. -/
def RingInputs.ofDatum {K : Type u} [Field K] [CharZero K] {G : Type u} [Group G]
    {U : Type u} [Ring U] [Nontrivial U] [Algebra K U]
    (L : Work.ORLinnell.LinnellDatum K G U) (G' : Subgroup G) (hN : G'.Normal)
    (hfin : G'.FiniteIndex) (htf : IsMulTorsionFree G')
    (hgl : Work.ORCoherence.globalDim (MonoidAlgebra K G) ≤ (2 : WithBot ℕ∞))
    (hTor : Work.ORCoherence.TorTwoVanishes (LinData.toS L).toRingHom) :
    RingInputs K G where
  U := U
  datum := L
  G' := G'
  normal_G' := hN
  finiteIndex_G' := hfin
  torsionFree_G' := htf
  hinj := Work.ORAssembly.Ring.toS_injective L
  hgl := hgl
  hTor := hTor

/-- **Constructing the ring inputs from the Linnell datum together with the flatness data of
node N9.**  This is the constructor a caller uses once nodes N3 (Lyndon sequence, Claim 5.8,
duality chain), N8 (Lemma 5.1′, right-module form) and N1 (Lemma 5.2(2)) have supplied the
hypotheses of `Work.ORAssembly.torTwoVanishes_of_flatHyp`; it combines `RingInputs.ofDatum` with
that bridge. -/
def RingInputs.ofDatumFlat {K : Type u} [Field K] [CharZero K] {G : Type u} [Group G]
    {U : Type u} [Ring U] [Nontrivial U] [Algebra K U]
    (L : Work.ORLinnell.LinnellDatum K G U) (G' : Subgroup G) (hN : G'.Normal)
    (hfin : G'.FiniteIndex) (htf : IsMulTorsionFree G')
    (hgl : Work.ORCoherence.globalDim (MonoidAlgebra K G) ≤ (2 : WithBot ℕ∞))
    {A : Type u} [AddCommGroup A] [Module (MonoidAlgebra K G) A]
    {B : Type u} [AddCommGroup B] [Module (MonoidAlgebra K G) B]
    {C : Type u} [AddCommGroup C] [Module K C] [Module (MonoidAlgebra K G) C]
    [IsScalarTower K (MonoidAlgebra K G) C] [SMulCommClass K (MonoidAlgebra K G) C]
    [Module ((MonoidAlgebra K G)ᵐᵒᵖ) (↥(LinData.SAlg L) ⊗[K] C)]
    (f : A →ₗ[MonoidAlgebra K G] B) (g : B →ₗ[MonoidAlgebra K G] C)
    (hg : Function.Surjective g) (hfg : f.range = g.ker)
    (hB : ∀ (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
      [IsScalarTower K (MonoidAlgebra K G) M] [SMulCommClass K (MonoidAlgebra K G) M],
      letI := Work.ORFlatness.diagRightModule K G ↥(LinData.SAlg L) (LinData.toS L) M
      Work.ORFlatness.Tor1Vanishes (MonoidAlgebra K G)
        (↥(LinData.SAlg L) ⊗[K] M) B)
    (hA : ∀ (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
      [IsScalarTower K (MonoidAlgebra K G) M] [SMulCommClass K (MonoidAlgebra K G) M],
      letI := Work.ORFlatness.diagRightModule K G ↥(LinData.SAlg L) (LinData.toS L) M
      Function.Injective (Work.ORFlatness.BalTensor.map (MonoidAlgebra K G)
        (LinearMap.id : (↥(LinData.SAlg L) ⊗[K] M) →ₗ[(MonoidAlgebra K G)ᵐᵒᵖ]
          (↥(LinData.SAlg L) ⊗[K] M)) f))
    (hswap : ∀ (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
      [IsScalarTower K (MonoidAlgebra K G) M] [SMulCommClass K (MonoidAlgebra K G) M],
      letI := Work.ORFlatness.diagRightModule K G ↥(LinData.SAlg L) (LinData.toS L) M
      (Work.ORFlatness.Tor1Vanishes (MonoidAlgebra K G) (↥(LinData.SAlg L) ⊗[K] M) C ↔
        Work.ORFlatness.Tor1Vanishes (MonoidAlgebra K G) (↥(LinData.SAlg L) ⊗[K] C) M))
    (hchain : ∀ (M : ModuleCat.{u} (MonoidAlgebra K G)),
      IsZero (Work.ORCoherence.Tor (LinData.toS L).toRingHom 2 M) ↔
        Work.ORFlatness.Tor1Vanishes (MonoidAlgebra K G) (↥(LinData.SAlg L) ⊗[K] C) (↥M)) :
    RingInputs K G :=
  RingInputs.ofDatum L G' hN hfin htf hgl
    (torTwoVanishes_of_flatHyp (LinData.toS L) f g hg hfg hB hA hswap hchain)

/-- **The group half of Theorem 1.1**, with the `FP₂` input asked only of the *finitely generated*
one-relator presentations `⟨Fin n | r⟩`.

This is the usable form of the group half: the input is supplied by the ring half at `ℚ`
(`ringCoherent_of_ringInputs` applied to `RingInputs ℚ ⟨Fin n | r⟩`, pushed through
`ringCoherent_ulift_coeff` and node N11) and promoted to all one-relator groups by
`Work.ORAssembly.FP2.homologicallyCoherent_of_fg`, which uses node N0's free-factor reduction
(so the uncountable generating types of node N2's hierarchy recursor are harmless). -/
theorem groupCoherent_of_fgInputs
    (HN : NodeInputs.{0} Unit)
    (hfp : ∀ (n : ℕ) (r : FreeGroup (Fin n)),
      HomologicallyCoherent (ULift.{0} ℚ) (PresentedGroup ({r} : Set (FreeGroup (Fin n))))) :
    ∀ (G : Type 0) [Group G], Group.OneRelator G → Group.Coherent G :=
  groupCoherent_of_oneRelatorNodes HN.combinatorics HN.hnnTree HN.coprodTree HN.quotientTree
    HN.freeOnTree HN.bassSerre HN.dunwoody (Work.ORAssembly.Coherent.freeGroup_coherent)
    (Work.ORAssembly.FP2.homologicallyCoherent_of_fg
      (fun e => Work.ORAssembly.FP2.homologicallyCoherent_of_mulEquiv e) hfp)

/-! ## The final assembly -/

/-- **Theorem 1.1 of Jaikin-Zapirain--Linton**, assembled from the node-level inputs, in the
generality of the challenge statement (`G` and `K` in arbitrary universes).

The proof:

* the ring half `ringCoherent_of_all hRingQ` at `ℚ` gives `ℚ[H]` coherent for every *finitely
  generated* one-relator group `H`, hence `FP₂(ℚ)` for its finitely generated subgroups (node N11,
  `homologicallyCoherent_of_coherent`); the f.g. case is promoted to all one-relator groups by
  `Work.ORAssembly.FP2.homologicallyCoherent_of_fg`, which uses node N0's free-factor reduction
  (`oneRelator_freeFactor`) and the isomorphism invariance of `FP₂`;
* the group half (node N2's `HasHierarchy` supplies the Magnus--Moldavanskii hierarchy; the
  induction is `fg_coherent_of_hierarchy`, using the Bass--Serre trees, node N13's JL Theorem 4.5
  with its Bieri--Strebel input discharged by node N11, and the free-group base case) gives
  `Group.Coherent H` for every one-relator group `H` in `Type 0`; node N0
  (`Group.Coherent.of_oneRelator_of_fg`) promotes this to `Group.Coherent G`;
* the ring half `ringCoherent_of_ringInputs hRingK` at the field `K`, applied to the lift of each
  finitely generated one-relator presentation, gives `Ring.Coherent K[G]` through node N0's
  reduction `Ring.Coherent.of_oneRelator_of_fg`. -/
theorem theorem_1_1_of_nodes {G : Type u} {K : Type v} [Group G] [Field K] [CharZero K]
    (hG : Group.OneRelator G)
    (HN : NodeInputs.{0} Unit)
    (hRingQ : ∀ (n : ℕ) (r : FreeGroup (Fin n)),
      RingInputs ℚ (PresentedGroup ({r} : Set (FreeGroup (Fin n)))))
    (hRingK : ∀ (n : ℕ) (r : FreeGroup (Fin n)),
      RingInputs K (ULift.{v} (PresentedGroup ({r} : Set (FreeGroup (Fin n)))))) :
    Group.Coherent G ∧ Ring.Coherent (MonoidAlgebra K G) := by
  have hfp_fg : ∀ (n : ℕ) (r : FreeGroup (Fin n)),
      HomologicallyCoherent (ULift.{0} ℚ) (PresentedGroup ({r} : Set (FreeGroup (Fin n)))) :=
    fun n r => homologicallyCoherent_of_coherent
      ((ringCoherent_ulift_coeff ℚ _).mp (ringCoherent_of_ringInputs (hRingQ n r)))
  have hcoh0 : ∀ (G : Type 0) [Group G], Group.OneRelator G → Group.Coherent G :=
    groupCoherent_of_fgInputs HN hfp_fg
  refine ⟨Group.Coherent.of_oneRelator_of_fg G hG ?_, ?_⟩
  · intro n r
    exact hcoh0 (PresentedGroup ({r} : Set (FreeGroup (Fin n))))
      ⟨Fin n, r, ⟨MulEquiv.refl _⟩⟩
  · refine Ring.Coherent.of_oneRelator_of_fg G K hG ?_
    intro n r
    exact Ring.Coherent.of_ringEquiv
      (MonoidAlgebra.mapDomainRingEquiv K
        (MulEquiv.ulift (α := PresentedGroup ({r} : Set (FreeGroup (Fin n))))))
      (ringCoherent_of_ringInputs (hRingK n r))

end Work.ORAssembly
