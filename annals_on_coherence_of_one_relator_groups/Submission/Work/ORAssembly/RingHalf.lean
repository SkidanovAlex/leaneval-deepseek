/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Node N14, part (2): coherence of `K[G]` for one-relator `G`

This file assembles the **ring half** of Theorem 1.1 from the *delivered* nodes of the L² strand
and the inputs still owed by the open ones.

Delivered and used here, verbatim:

* **N10** (`Work.ORCoherence.coherent_of_embeds_semisimple`, `Submission/Work/ORCoherence/Main.lean`):
  JL Corollary 3.3 — a ring that embeds injectively in an Artinian ring, has global dimension
  `≤ 2`, and has weak dimension `≤ 1` as a right module over itself, is coherent.  This is the
  final step of the ring half.
* **N7** (`Work.ORLinnell.isSemisimpleRing_S`, `Submission/Work/ORLinnell/Main.lean`):
  `S = D(G)` is a semisimple ring for a normal torsion-free finite-index `G' ⊴ G` and `K` of
  characteristic zero (Maschke for a finite crossed product).  Together with the Mathlib instance
  `IsSemisimpleRing → IsArtinianRing` this supplies N10's Artinianity hypothesis.
* **N9** (`Work.ORFlatness.torTwoVanishes_diagonal_jl_right`,
  `Submission/Work/ORFlatness/Tor2ORCoherence.lean`): the flatness hypotheses of JL §5 give
  `Tor₂^{K[G]}(S, -) = 0`.  `torTwoVanishes_of_flatHyp` below is the (thin) bridge from the
  hypotheses as stated in `Work.ORFlatness` to the hypothesis as stated in this file; it exists
  so that a caller can see exactly which inputs N9 still needs (a Lyndon exact sequence, JL Claim
  5.8, JL Lemma 5.1, JL Lemma 5.2 and its dimension-shifting chain).

Still open, and taken as the fields of `RingInputs`:

* **N6** (`Work.ORHughesFree.hughesFree_exists`): the division closure of `K[G]` in `U(G)` is a
  Hughes-free division ring — the `division_of_torsionFree`, `ore_field_unit`, `ore_field_frac`
  fields of `Work.ORLinnell.LinnellDatum`;
* **N5** (delivered, `Work.ORVonNeumann.CountableEnvelope`) supplies the Linnell independence
  fields of the datum, but the *construction* of the datum from the envelope (over `ℂ`, for
  countable `G`) is not formalised — mismatch (M1) of `README.md`;
* **N8** supplies the injectivity of `K[G] → S` (Linnell independence at the trivial subgroup)
  through the mirror of Lemma 5.1′ — mismatch (M2) of `README.md`;
* **N3** (`Work.ORLyndon`) supplies `gl.dim K[G] ≤ 2` and the Lyndon exact sequence together with
  JL Claim 5.8 and the duality chain — mismatch (M3);
* **N4** (`Work.ORLocInd`) supplies the normal torsion-free finite-index subgroup `G'`.
-/

import ChallengeDeps
import Submission.Work.ORAssembly.Defs
import Submission.Work.ORAssembly.RingHalfDefs
import Submission.Work.ORLinnell.Main
import Submission.Work.ORFlatness.All
import Submission.Work.ORCoherence.Main

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped TensorProduct

open CategoryTheory Limits

universe u

namespace Work.ORAssembly

/-! ## Node N9 in the vocabulary of the assembly -/

/-- **Node N9** (JL Theorem 5.6 + Lemma 5.2): the flatness hypotheses of JL §5 for a coefficient
ring `S` with `φ : K[G] → S` imply `Tor₂^{K[G]}(S, -) = 0`, in the form consumed by node N10.

The hypotheses, in the notation of `Work.ORFlatness`:

* `f : A → B`, `g : B → C` with `g` surjective and `f.range = g.ker` — the Lyndon exact sequence
  of the one-relator presentation (node N3);
* `hB` — JL Claim 5.8;
* `hA` — JL Lemma 5.1 (the torsion crux, node N8) in the right-module form;
* `hswap` — JL Lemma 5.2(2), delivered by node N1 (`Work.ORHomAlg.JL52.jl_5_2_2`);
* `hchain` — the dimension-shifting chain of JL Lemma 5.2. -/
theorem torTwoVanishes_of_flatHyp {K : Type u} [Field K] {G : Type u} [Group G] {S : Type u}
    [Ring S] [Algebra K S] (φ : MonoidAlgebra K G →ₐ[K] S)
    {A : Type u} [AddCommGroup A] [Module (MonoidAlgebra K G) A]
    {B : Type u} [AddCommGroup B] [Module (MonoidAlgebra K G) B]
    {C : Type u} [AddCommGroup C] [Module K C] [Module (MonoidAlgebra K G) C]
    [IsScalarTower K (MonoidAlgebra K G) C] [SMulCommClass K (MonoidAlgebra K G) C]
    [Module ((MonoidAlgebra K G)ᵐᵒᵖ) (S ⊗[K] C)]
    (f : A →ₗ[MonoidAlgebra K G] B) (g : B →ₗ[MonoidAlgebra K G] C)
    (hg : Function.Surjective g) (hfg : f.range = g.ker)
    (hB : ∀ (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
      [IsScalarTower K (MonoidAlgebra K G) M] [SMulCommClass K (MonoidAlgebra K G) M],
      letI := Work.ORFlatness.diagRightModule K G S φ M
      Work.ORFlatness.Tor1Vanishes (MonoidAlgebra K G) (S ⊗[K] M) B)
    (hA : ∀ (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
      [IsScalarTower K (MonoidAlgebra K G) M] [SMulCommClass K (MonoidAlgebra K G) M],
      letI := Work.ORFlatness.diagRightModule K G S φ M
      Function.Injective (Work.ORFlatness.BalTensor.map (MonoidAlgebra K G)
        (LinearMap.id : (S ⊗[K] M) →ₗ[(MonoidAlgebra K G)ᵐᵒᵖ] (S ⊗[K] M)) f))
    (hswap : ∀ (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
      [IsScalarTower K (MonoidAlgebra K G) M] [SMulCommClass K (MonoidAlgebra K G) M],
      letI := Work.ORFlatness.diagRightModule K G S φ M
      (Work.ORFlatness.Tor1Vanishes (MonoidAlgebra K G) (S ⊗[K] M) C ↔
        Work.ORFlatness.Tor1Vanishes (MonoidAlgebra K G) (S ⊗[K] C) M))
    (hchain : ∀ (M : ModuleCat.{u} (MonoidAlgebra K G)),
      IsZero (Work.ORCoherence.Tor φ.toRingHom 2 M) ↔
        Work.ORFlatness.Tor1Vanishes (MonoidAlgebra K G) (S ⊗[K] C) (↥M)) :
    Work.ORCoherence.TorTwoVanishes φ.toRingHom :=
  Work.ORFlatness.torTwoVanishes_diagonal_jl_right K G S φ f g hg hfg hB hA hswap hchain

/-! ## The L² input of the ring half -/

/-- **The L² input of the ring half, per one-relator group.**

For every one-relator group `G` in the universe and every Linnell datum `L` for `K[G]` in a ring
`U` (nodes N5 + N6 + N7), there is

* a normal torsion-free finite-index subgroup `G' ⊴ G` (node N4);
* `gl.dim K[G] ≤ 2` (node N3, from Lyndon's identity theorem);
* injectivity of the structure map `K[G] → S = D(G)` (Linnell independence, node N5);
* vanishing of `Tor₂^{K[G]}(S, -)` (node N9, from the flatness hypotheses of §5 — see
  `torTwoVanishes_of_flatHyp` for the precise list still owed by N3/N8/N1).

This is a *data* structure (not a `Prop`): the Linnell datum `U`, `D` of nodes N5/N6/N7 is an
object, not a proposition.  Its fields:

* `U`, `datum` — the ring of affiliated operators and the Linnell datum (nodes N5, N6, N7);
* `G'` — a normal torsion-free finite-index subgroup (node N4);
* `hinj` — injectivity of `K[G] → S` (Linnell independence, node N5); proved from the datum by
  `Work.ORAssembly.Ring.toS_injective`;
* `hgl` — `gl.dim K[G] ≤ 2` (node N3, from Lyndon's identity theorem);
* `hTor` — `Tor₂^{K[G]}(S, -) = 0` (node N9, from the flatness hypotheses of JL §5: see
  `torTwoVanishes_of_flatHyp`).

No field mentions `Ring.Coherent`. -/
structure RingInputs (K : Type u) [Field K] [CharZero K] (G : Type u) [Group G] where
  U : Type u
  [ringU : Ring U]
  [nontrivialU : Nontrivial U]
  [algebraU : Algebra K U]
  datum : Work.ORLinnell.LinnellDatum K G U
  G' : Subgroup G
  normal_G' : G'.Normal
  finiteIndex_G' : G'.FiniteIndex
  torsionFree_G' : IsMulTorsionFree G'
  hinj : Function.Injective (LinData.toS datum)
  hgl : Work.ORCoherence.globalDim (MonoidAlgebra K G) ≤ (2 : WithBot ℕ∞)
  hTor : Work.ORCoherence.TorTwoVanishes (LinData.toS datum).toRingHom

/-! ## The ring half of Theorem 1.1 -/

/-- **The ring half of Theorem 1.1 for a one-relator group**, from the node inputs.

Node N7 (via `Work.ORLinnell.isSemisimpleRing_S`) makes `S = D(G)` semisimple, hence Artinian;
the inputs supply `gl.dim K[G] ≤ 2` and `Tor₂^{K[G]}(S, -) = 0`; JL Corollary 3.3 in the form
delivered by node N10 (`Work.ORCoherence.coherent_of_embeds_semisimple`) then gives
`Ring.Coherent K[G]`. -/
theorem ringCoherent_of_ringInputs {K : Type u} [Field K] [CharZero K] {G : Type u} [Group G]
    (R : RingInputs K G) : Ring.Coherent (MonoidAlgebra K G) := by
  obtain ⟨U, L, G', hN, hfin, htf, hinj, hgl, hTor⟩ := R
  haveI hss : IsSemisimpleRing ↥(L.S) :=
    Work.ORLinnell.isSemisimpleRing_S L G' hN htf hfin
  haveI hArt : IsArtinianRing ↥(LinData.SAlg L) :=
    inferInstanceAs (IsArtinianRing ↥(L.S))
  exact Work.ORCoherence.coherent_of_embeds_semisimple (LinData.toS L).toRingHom hinj hgl hTor

/-- The ring half of Theorem 1.1, for all one-relator groups at once. -/
theorem ringCoherent_of_all {K : Type u} [Field K] [CharZero K]
    (h : ∀ (G : Type u) [Group G], Group.OneRelator G → RingInputs K G) :
    ∀ (G : Type u) [Group G], Group.OneRelator G → Ring.Coherent (MonoidAlgebra K G) :=
  fun G _ hG => ringCoherent_of_ringInputs (h G hG)

end Work.ORAssembly
