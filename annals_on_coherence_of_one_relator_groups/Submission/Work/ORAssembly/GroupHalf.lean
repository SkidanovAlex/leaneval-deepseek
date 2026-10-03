/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Node N14, part (1): coherence of one-relator groups

This file assembles the **group half** of Theorem 1.1 (Jaikin-Zapirain--Linton, *Annals* 2025)
from the node-level inputs declared in `Submission/Work/ORAssembly/Defs.lean`:

* the Magnus--Moldavanskii hierarchy of node N2 (`Work.OROneRel`), used as an induction principle;
* the Bass--Serre trees of node N12 (`ZModCoprodTreeInput` for the base case, `HNNTreeInput` for
  the step) together with the three named `Prop`s of `Work.ORDunwoody`;
* the Dunwoody resolution theorem `DunwoodyResolutionAll` of node N13;
* the Bieri--Strebel theorem of node N11 (`Work.ORFP2.BieriStrebel`, *proved* there) discharging
  the corresponding input of `Work.ORDunwoody`;
* the homological input `HomologicallyCoherent (ULift ℚ) G` — "every finitely generated subgroup
  of `G` is of type `FP₂(ℚ)`" — which the **ring half** of the theorem supplies: `Ring.Coherent
  ℚ[G]` (node N10 at `K = ℚ`) implies it through JL's remark after Theorem 4.7, formalised as
  `Work.ORFP2.IsFP2_of_coherent_monoidAlgebra`.

The conclusion is fed through JL Theorem 4.5 in the form proved by node N13,
`Work.ORDunwoody.groupCoherent_of_tree`: a group acting on a tree with coherent vertex stabilizers,
all of whose finitely generated subgroups are `FP₂(ℚ)`, is coherent.
-/

import ChallengeDeps
import Submission.Work.ORAssembly.Defs
import Submission.Work.ORDunwoody.Corollaries
import Submission.Work.ORFP2.BieriStrebelBridge
import Submission.Work.OROneRel.Derived
import Submission.Work.OROneRel.FreiheitssatzUnconditional
import Submission.Work.OROneRel.presentedGroup_of_zpow_iso_coprod_zmod
import Submission.Work.OROneRel.presentedGroup_one_iso_freeGroup

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v

namespace Work.ORAssembly

open Work.ORDunwoody
open scoped Classical

variable {X : Type u}

/-! ## Elementary transfers of `Group.Coherent` and the coherence of the base groups -/

/-- Coherence descends to the image of a subgroup under an injective homomorphism. -/
theorem coherent_map_of_injective {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (K : Subgroup G) (h : Group.Coherent K) :
    Group.Coherent (K.map f) :=
  Group.Coherent.of_mulEquiv (Subgroup.equivMapOfInjective K f hf) h

/-- Coherence of the range of an injective homomorphism. -/
theorem coherent_range_of_injective {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (h : Group.Coherent G) : Group.Coherent f.range :=
  Group.Coherent.of_mulEquiv (MonoidHom.ofInjective hf) h

/-- Coherence is invariant under conjugation of subgroups. -/
theorem coherent_map_conj {G : Type u} [Group G] (K : Subgroup G) (g : G)
    (h : Group.Coherent K) :
    Group.Coherent (K.map (MulEquiv.toMonoidHom (MulAut.conj g))) :=
  coherent_map_of_injective _ (MulAut.conj g).injective K h

/-- Every finite group is coherent. -/
theorem finite_coherent (G : Type u) [Group G] [Finite G] : Group.Coherent G := by
  intro H _
  haveI : Finite H := Finite.of_injective H.subtype Subtype.coe_injective
  exact inferInstance

/-! ## The base case of the Magnus--Moldavanskii induction -/

/-- **Base case of the induction**: `⟨α | r⟩` for a terminal relator `r` is `F(α ∖ {x}) ∗ ℤ/l`
(or a free group), which acts on its Bass--Serre tree with free and finite vertex stabilizers;
those are coherent, and `FP₂(ℚ)` for its finitely generated subgroups comes from the ring half.
Hence `⟨α | r⟩` is coherent by JL Theorem 4.5 (`Work.ORDunwoody.groupCoherent_of_tree`). -/
theorem terminal_coherent
    (hcop : ZModCoprodTreeInput.{u})
    (hq : QuotientTreeByNormalClosureOfElliptic X) (hfree : FreeOnTreeIsFree X)
    (hss : BassSerreFinitelyPresentedAll X) (hdr : DunwoodyResolutionAll X)
    (hfreeCoh : ∀ (γ : Type u), Group.Coherent (FreeGroup γ))
    (hfp : ∀ (G : Type u) [Group G], Group.OneRelator G → HomologicallyCoherent (ULift.{u} ℚ) G)
    {α : Type u} {r : FreeGroup α} (hr : Work.OROneRel.IsTerminalRelator r) :
    Group.Coherent (PresentedGroup ({r} : Set (FreeGroup α))) := by
  rcases hr with hr | ⟨x, m, hm, rfl⟩
  · subst hr
    obtain ⟨e⟩ := Work.OROneRel.presentedGroup_one_iso_freeGroup (α := α)
    exact Group.Coherent.of_mulEquiv e.symm (hfreeCoh α)
  · obtain ⟨e⟩ := Work.OROneRel.presentedGroup_of_zpow_iso_coprod_zmod x m hm
    obtain ⟨V, instV, T, hT⟩ := hcop {a : α // a ≠ x} m.natAbs
    haveI : NeZero m.natAbs := ⟨Int.natAbs_ne_zero.mpr hm⟩
    haveI : Finite (Multiplicative (ZMod m.natAbs)) := Finite.of_fintype _
    letI : MulAction (Monoid.Coprod (Multiplicative (ZMod m.natAbs))
        (FreeGroup {a : α // a ≠ x})) V := instV
    have hleft : Group.Coherent
        ((Monoid.Coprod.inl : Multiplicative (ZMod m.natAbs) →*
          Monoid.Coprod (Multiplicative (ZMod m.natAbs))
            (FreeGroup {a : α // a ≠ x})).range) :=
      coherent_range_of_injective _ Monoid.Coprod.inl_injective (finite_coherent _)
    have hright : Group.Coherent
        ((Monoid.Coprod.inr : FreeGroup {a : α // a ≠ x} →*
          Monoid.Coprod (Multiplicative (ZMod m.natAbs))
            (FreeGroup {a : α // a ≠ x})).range) :=
      coherent_range_of_injective _ Monoid.Coprod.inr_injective (hfreeCoh _)
    have hcop_coh : Group.Coherent (Monoid.Coprod (Multiplicative (ZMod m.natAbs))
        (FreeGroup {a : α // a ≠ x})) :=
      groupCoherent_of_tree (k := ULift.{u} ℚ) T (fun v => by
          rcases hT v with ⟨g, hg⟩ | ⟨g, hg⟩
          · rw [hg]; exact coherent_map_conj _ g hleft
          · rw [hg]; exact coherent_map_conj _ g hright)
        (Work.ORFP2.BieriStrebel (ULift.{u} ℚ)) hdr hq hfree hss
        (hfp _ ⟨α, FreeGroup.of x ^ m, ⟨e⟩⟩)
    exact Group.Coherent.of_mulEquiv e.symm hcop_coh

/-! ## The HNN step of the Magnus--Moldavanskii induction -/

/-- **The HNN step.**  If `⟨β | r'⟩` is coherent and `⟨α | r⟩` is an HNN extension of `⟨β | r'⟩`
over subgroups `A`, `B ≅ A`, then `⟨α | r⟩` is coherent: by the Bass--Serre tree of the HNN
extension, the HNN extension acts on a tree whose vertex stabilizers are conjugates of `⟨β | r'⟩`,
hence coherent, and JL Theorem 4.5 applies.  (The associated subgroups `A`, `B` are Magnus
subgroups and hence free by the Freiheitssatz, but their coherence is not needed here: only the
vertex stabilizers of the Bass--Serre tree enter Theorem 4.5.) -/
theorem hnn_step_coherent
    (hnn : HNNTreeInput.{u})
    (hq : QuotientTreeByNormalClosureOfElliptic X) (hfree : FreeOnTreeIsFree X)
    (hss : BassSerreFinitelyPresentedAll X) (hdr : DunwoodyResolutionAll X)
    (hfp : ∀ (G : Type u) [Group G], Group.OneRelator G → HomologicallyCoherent (ULift.{u} ℚ) G)
    {α β : Type u} {r : FreeGroup α} {r' : FreeGroup β}
    (ih : Group.Coherent (PresentedGroup ({r'} : Set (FreeGroup β))))
    (A B : Subgroup (PresentedGroup ({r'} : Set (FreeGroup β)))) (φ : A ≃* B)
    (e : PresentedGroup ({r} : Set (FreeGroup α)) ≃*
      HNNExtension (PresentedGroup ({r'} : Set (FreeGroup β))) A B φ) :
    Group.Coherent (PresentedGroup ({r} : Set (FreeGroup α))) := by
  obtain ⟨V, instV, T, hT⟩ := hnn (PresentedGroup ({r'} : Set (FreeGroup β))) A B φ
  letI : MulAction (HNNExtension (PresentedGroup ({r'} : Set (FreeGroup β))) A B φ) V := instV
  have hbase : Group.Coherent
      ((HNNExtension.of (A := A) (B := B) (φ := φ)).range) :=
    coherent_range_of_injective _ (HNNExtension.of_injective φ) ih
  refine Group.Coherent.of_mulEquiv e.symm
    (groupCoherent_of_tree (k := ULift.{u} ℚ) T (fun v => ?_)
      (Work.ORFP2.BieriStrebel (ULift.{u} ℚ)) hdr hq hfree hss
      (hfp _ ⟨α, r, ⟨e⟩⟩))
  obtain ⟨g, hg⟩ := hT v
  rw [hg]
  exact coherent_map_conj _ _ hbase

/-! ## The induction over the Magnus--Moldavanskii hierarchy, and Theorem 1.1's group half -/

/-- Coherence of `⟨α | r⟩` for every relator carrying a Magnus--Moldavanskii hierarchy, by
induction on the hierarchy (node N2's `HasMMHierarchy`). -/
theorem fg_coherent_of_hierarchy
    (hnn : HNNTreeInput.{u}) (hcop : ZModCoprodTreeInput.{u})
    (hq : QuotientTreeByNormalClosureOfElliptic X) (hfree : FreeOnTreeIsFree X)
    (hss : BassSerreFinitelyPresentedAll X) (hdr : DunwoodyResolutionAll X)
    (hfreeCoh : ∀ (γ : Type u), Group.Coherent (FreeGroup γ))
    (hfp : ∀ (G : Type u) [Group G], Group.OneRelator G → HomologicallyCoherent (ULift.{u} ℚ) G)
    {α : Type u} {r : FreeGroup α} (h : Work.OROneRel.HasMMHierarchy α r) :
    Group.Coherent (PresentedGroup ({r} : Set (FreeGroup α))) := by
  refine Work.OROneRel.HasMMHierarchy.rec
    (motive := fun α r _ => Group.Coherent (PresentedGroup ({r} : Set (FreeGroup α)))) ?_ ?_ ?_ h
  · intro α r hr
    exact terminal_coherent hcop hq hfree hss hdr hfreeCoh hfp hr
  · intro α r β r' hlt h A B hA hB φ e ih
    exact hnn_step_coherent hnn hq hfree hss hdr hfp ih A B φ e
  · intro α r β s hrec ι hι ih
    exact Group.Coherent.of_mulEquiv (MonoidHom.ofInjective hι).symm
      (Work.ORReductions.Coherent.groupCoherent_subgroup ι.range ih)

/-- **The group half of Theorem 1.1, from the node-level inputs.**  Every one-relator group is
coherent.  The inputs are exactly the open nodes (N2's `OneRelatorCombinatorics`, the N12 trees
and named `Prop`s, the N13 Dunwoody resolution) together with the `FP₂(ℚ)` input supplied by the
ring half; the Bieri--Strebel input of `Work.ORDunwoody` is *discharged* by node N11. -/
theorem groupCoherent_of_oneRelatorNodes
    (hC : Work.OROneRel.OneRelatorCombinatorics.{u})
    (hnn : HNNTreeInput.{u}) (hcop : ZModCoprodTreeInput.{u})
    (hq : QuotientTreeByNormalClosureOfElliptic X) (hfree : FreeOnTreeIsFree X)
    (hss : BassSerreFinitelyPresentedAll X) (hdr : DunwoodyResolutionAll X)
    (hfreeCoh : ∀ (γ : Type u), Group.Coherent (FreeGroup γ))
    (hfp : ∀ (G : Type u) [Group G], Group.OneRelator G → HomologicallyCoherent (ULift.{u} ℚ) G) :
    ∀ (G : Type u) [Group G], Group.OneRelator G → Group.Coherent G := by
  intro G _ hG
  obtain ⟨α, r, h, ⟨e⟩⟩ := Work.OROneRel.hasHierarchy_of_oneRelator hC hG
  exact Group.Coherent.of_mulEquiv e
    (fg_coherent_of_hierarchy hnn hcop hq hfree hss hdr hfreeCoh hfp h)

end Work.ORAssembly
