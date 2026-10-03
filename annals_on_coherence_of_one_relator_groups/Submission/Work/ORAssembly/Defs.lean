/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Node N14 (final assembly): the node-level hypotheses

`Submission/Work/ORAssembly/` is the *final assembly* of Theorem 1.1 of
Jaikin-Zapirain--Linton, *On the coherence of one-relator groups and their group algebras*
(Annals of Math 201, 2025): every one-relator group `G` is coherent and `K[G]` is coherent for
every field `K` of characteristic zero.

The assembly is written so that **every** deep input is an explicitly named `Prop`, never an
axiom.  Inputs that are *delivered* by a sibling subproject are imported and used; inputs that
are still open are recorded here as `Prop`-valued definitions whose statements mirror the
deliverable stated in the owner's own interface file.

## The open nodes, and where their deliverable is stated

| node | area | deliverable | mirrored here as |
|---|---|---|---|
| N2 | `Work.OROneRel` | `OneRelatorCombinatorics` (`Interface.lean`) | `NodeInputs.combinatorics` |
| N12 | `Work.ORBassSerre` | the three `Prop`s of `Work.ORDunwoody.Hypotheses` | `NodeInputs.quotientTree`, … |
| N12 (gap) | `Work.ORBassSerre` | Bass--Serre tree of `HNNExtension` / `Monoid.Coprod` | `HNNTreeInput`, `ZModCoprodTreeInput` |
| N13 | `Work.ORDunwoody` | `DunwoodyResolutionAll` (`Hypotheses.lean`) | `NodeInputs.dunwoody` |

The *delivered* nodes (N0 `ORReductions`, N1 `ORHomAlg`, N5 `ORVonNeumann`, N7 `ORLinnell`,
N8 `ORTorsion`, N9 `ORFlatness`, N10 `ORCoherence`, N11 `ORFP2`) are used directly; the places
where their conclusions do not literally match the next node's input are documented in
`README.md` (`## Interface mismatches`) and, where possible, bridged by a lemma in this area.
-/

import ChallengeDeps
import Submission.Work.ORDunwoody.Basic
import Submission.Work.ORDunwoody.Hypotheses
import Submission.Work.ORDunwoody.Corollaries
import Submission.Work.OROneRel.Interface
import Submission.Work.ORReductions.API

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORAssembly

open Work.ORDunwoody

/-! ## Node N12: Bass--Serre trees (the two not-yet-formalised pieces) -/

/-- **Bass--Serre tree of an HNN extension** (node N12, `Work.ORBassSerre`).

For an HNN extension `E = HNN(G, A, B, φ)` there is an `E`-tree whose vertex stabilizers are
the conjugates of the image of `G` in `E` (the vertex set is `E/G`, the edge set `E/A`).

`Submission/Work/ORBassSerre/README.md` lists this construction under "Not yet formalised";
it is the missing geometric ingredient of the HNN step of the Magnus--Moldavanskii induction
(`Work.ORAssembly.GroupHalf.hnn_step_coherent`). -/
def HNNTreeInput : Prop :=
  ∀ (G : Type u) [Group G] (A B : Subgroup G) (φ : A ≃* B),
    ∃ (V : Type u) (_ : MulAction (HNNExtension G A B φ) V)
      (T : GTree (HNNExtension G A B φ) V),
      ∀ v : V, ∃ g : HNNExtension G A B φ,
        T.vertexStab v =
          ((HNNExtension.of (A := A) (B := B) (φ := φ)).range).map
            (MulEquiv.toMonoidHom (MulAut.conj g))

/-- **Bass--Serre tree of the free product `ℤ/n ∗ F(γ)`** (node N12, `Work.ORBassSerre`).

For a free product `G ∗ H` there is a `G ∗ H`-tree whose vertex stabilizers are the conjugates
of the images of `G` and of `H`.  This is the "base case" tree of the Magnus--Moldavanskii
induction: it exhibits `F(γ) ∗ ℤ/n` as a group acting on a tree with free and finite vertex
groups.  It is a piece of the (not yet formalised) Bass--Serre structure theory for
`Monoid.Coprod` recorded in `Submission/Work/ORBassSerre/README.md`.

The first factor is written at universe `0` (`Multiplicative (ZMod n)`) because that is
literally the factor produced by `Work.OROneRel.presentedGroup_of_zpow_iso_coprod_zmod`. -/
def ZModCoprodTreeInput : Prop :=
  ∀ (γ : Type u) (n : ℕ),
    ∃ (V : Type u)
      (_ : MulAction (Monoid.Coprod (Multiplicative (ZMod n)) (FreeGroup γ)) V)
      (T : GTree (Monoid.Coprod (Multiplicative (ZMod n)) (FreeGroup γ)) V),
      ∀ v : V,
        (∃ g : Monoid.Coprod (Multiplicative (ZMod n)) (FreeGroup γ),
          T.vertexStab v =
            ((Monoid.Coprod.inl : Multiplicative (ZMod n) →*
              Monoid.Coprod (Multiplicative (ZMod n)) (FreeGroup γ)).range).map
              (MulEquiv.toMonoidHom (MulAut.conj g)))
        ∨ (∃ g : Monoid.Coprod (Multiplicative (ZMod n)) (FreeGroup γ),
          T.vertexStab v =
            ((Monoid.Coprod.inr : FreeGroup γ →*
              Monoid.Coprod (Multiplicative (ZMod n)) (FreeGroup γ)).range).map
              (MulEquiv.toMonoidHom (MulAut.conj g)))

/-! ## The bundle of inputs owned by the group-theoretic nodes -/

/-- The inputs of the group-theoretic half of Theorem 1.1, at the universe of the anchor `X`.

* `combinatorics` — node N2 (`Work.OROneRel`): the Freiheitssatz (proved there), the
  Magnus--Moldavanskii hierarchy, Weinbaum's theorem and the Karrass--Magnus--Solitar torsion
  theorem.
* `hnnTree`, `coprodTree` — the two Bass--Serre trees of node N12 listed above.
* `quotientTree`, `freeOnTree`, `bassSerre` — the three named inputs of `Work.ORDunwoody`,
  all owned by node N12.
* `dunwoody` — node N13 (`Work.ORDunwoody`): the Dunwoody resolution theorem.

The anchor `X` plays no mathematical role: it pins the universe level (the same device as in
`Work.ORDunwoody.Hypotheses.DunwoodyResolutionAll`). -/
structure NodeInputs (X : Type u) : Prop where
  /-- Node N2: one-relator combinatorics. -/
  combinatorics : Work.OROneRel.OneRelatorCombinatorics.{u}
  /-- Node N12: the Bass--Serre tree of an HNN extension. -/
  hnnTree : HNNTreeInput.{u}
  /-- Node N12: the Bass--Serre tree of the free product `ℤ/n ∗ F(γ)`. -/
  coprodTree : ZModCoprodTreeInput.{u}
  /-- Node N12: Serre, *Trees*, §5 / JL Lemma 4.1. -/
  quotientTree : Work.ORDunwoody.QuotientTreeByNormalClosureOfElliptic X
  /-- Node N12: a group acting freely on a tree is free. -/
  freeOnTree : Work.ORDunwoody.FreeOnTreeIsFree X
  /-- Node N12: the structure theorem for groups acting on trees. -/
  bassSerre : Work.ORDunwoody.BassSerreFinitelyPresentedAll X
  /-- Node N13: the Dunwoody resolution theorem (GL17 Prop. 2.17, constant case). -/
  dunwoody : Work.ORDunwoody.DunwoodyResolutionAll X

end Work.ORAssembly
