import Mathlib

/-!
# CWIND/GClass — gluing over a finite clopen partition, and the clopen decomposition

This file contains the light-condensed-set input for the `sigma` field of the CW induction: if a
topological space `Zt` is presented as a disjoint union of clopen pieces `Z j` (along open
embeddings `ι j`), then the light condensed set `Zt_cond` is the coproduct of the `(Z j)_cond`.

The proof has two steps:

* sections of a light condensed set over a light profinite set `S` glue uniquely along a finite
  family of pairwise disjoint clopen subsets covering `S` (`restrict_bijective_of_clopen_partition`);
* hence a section `S ⟶ Zt` may be decomposed into the clopen pieces `f ⁻¹' (range (ι j))`, of which
  only finitely many are nonempty, and a compatible family of sections over the pieces may be
  glued; the universal property of the coproduct follows.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits LightProfinite LightCondensed
open Opposite

namespace Work.CWIND.GClass

/-! ## Clopen subsets as light profinite sets -/

/-- A clopen subset of a light profinite set, viewed as a light profinite set. -/
def clopenLP (S : LightProfinite.{0}) (A : Set (↥S)) (hA : IsClopen A) : LightProfinite.{0} :=
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA.1.isCompact
  ↧A

/-- The inclusion of a clopen subset, as a morphism of light profinite sets. -/
def clopenIncl (S : LightProfinite.{0}) (A : Set (↥S)) (hA : IsClopen A) :
    clopenLP S A hA ⟶ S := by
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA.1.isCompact
  exact CompHausLike.ofHom _ ⟨Subtype.val, continuous_subtype_val⟩

@[simp]
lemma clopenIncl_apply (S : LightProfinite.{0}) (A : Set (↥S)) (hA : IsClopen A)
    (a : clopenLP S A hA) : (clopenIncl S A hA a : S) = Subtype.val (α := S) a := rfl

/-- The family of pieces of a finite clopen partition, as light profinite sets. -/
def partFam {S : LightProfinite.{0}} {I : Type} (A : I → Set (↥S)) (hA : ∀ i, IsClopen (A i)) :
    I → LightProfinite.{0} := fun i => clopenLP S (A i) (hA i)

/-- The inclusions of the pieces of a finite clopen partition. -/
def partMap {S : LightProfinite.{0}} {I : Type} (A : I → Set (↥S)) (hA : ∀ i, IsClopen (A i)) :
    ∀ i, partFam A hA i ⟶ S := fun i => clopenIncl S (A i) (hA i)

/-! ## A sheaf takes the empty light profinite set to a point -/

/-- The empty family of light profinite sets. -/
def emptyFam : Empty → LightProfinite.{0} := Empty.elim

/-- The empty family of morphisms into a light profinite set. -/
def emptyMap (T : LightProfinite.{0}) : (a : Empty) → emptyFam a ⟶ T :=
  fun a => Empty.instIsEmpty.elim a

theorem subsingleton_of_isEmpty (Z : LightCondSet.{0}) {T : LightProfinite.{0}}
    (hT : IsEmpty ↥T) : Subsingleton (Z.obj.obj (op T)) := by
  have hSF := Presheaf.IsSheaf.isSheafFor Z.property (Sieve.ofArrows emptyFam (emptyMap T))
    (by
      apply coherentTopology.mem_sieves_of_hasEffectiveEpiFamily
      refine ⟨Empty, inferInstance, emptyFam, emptyMap T, ?_, fun a => a.elim⟩
      rw [← effectiveEpi_desc_iff_effectiveEpiFamily, LightProfinite.effectiveEpi_iff_surjective]
      intro s
      exact (hT.false s).elim)
  have hSF' : Presieve.IsSheafFor Z.obj
      (Presieve.ofArrows Empty.elim (fun a => Empty.instIsEmpty.elim a) : Presieve T) :=
    (Presieve.isSheafFor_iff_generate _).2 hSF
  have hterm : IsTerminal (Z.obj.obj (op T)) :=
    Presieve.isTerminal_of_isSheafFor_empty_presieve T Z.obj hSF'
  have hU : Unique (Z.obj.obj (op T)) := Types.isTerminalEquivUnique _ hterm
  exact Subsingleton.intro fun a b => (hU.uniq a).trans (hU.uniq b).symm

/-! ## Gluing along a finite clopen partition -/

/-- **Gluing over a finite clopen partition.**  Let `A : I → Set S` be a finite family of
pairwise disjoint clopen subsets of a light profinite set `S` whose union is `S`.  Then a section of
a light condensed set `W` over `S` is the same thing as a family of sections over the pieces: the
restriction map `W(S) ⟶ ∏ i, W(A i)` is bijective. -/
theorem restrict_bijective_of_clopen_partition {S : LightProfinite.{0}} {I : Type} [Fintype I]
    (A : I → Set (↥S)) (hA : ∀ i, IsClopen (A i))
    (hdisj : Pairwise fun i k => Disjoint (A i) (A k))
    (hcov : (⋃ i, A i) = Set.univ) (W : LightCondSet.{0}) :
    Function.Bijective (fun z : W.obj.obj (op S) => fun i => W.obj.map (partMap A hA i).op z) := by
  classical
  have hmono : ∀ i, Mono (partMap A hA i) := by
    intro i
    rw [CompHausLike.mono_iff_injective]
    exact Subtype.val_injective
  have hsurj : Function.Surjective ⇑(Sigma.desc (partMap A hA)) := by
    intro s
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (by rw [hcov]; exact Set.mem_univ s)
    exact ⟨Sigma.ι (partFam A hA) i (show ↥(partFam A hA i) from ⟨s, hi⟩), by
      rw [Sigma.ι_comp_desc_apply]
      rfl⟩
  have hEff : EffectiveEpiFamily (partFam A hA) (partMap A hA) :=
    (effectiveEpi_desc_iff_effectiveEpiFamily _ _).mp
      ((LightProfinite.effectiveEpi_iff_surjective _).mpr hsurj)
  have hmem : Sieve.ofArrows (partFam A hA) (partMap A hA) ∈ coherentTopology LightProfinite S := by
    apply coherentTopology.mem_sieves_of_hasEffectiveEpiFamily
    exact ⟨I, inferInstance, partFam A hA, partMap A hA, hEff,
      fun i => Sieve.le_generate (Presieve.ofArrows (partFam A hA) (partMap A hA))
        (partFam A hA i) (partMap A hA i) (Presieve.ofArrows.mk i)⟩
  have hSF : Presieve.IsSheafFor W.obj (Presieve.ofArrows (partFam A hA) (partMap A hA)) :=
    (Presieve.isSheafFor_iff_generate _).2 (Presheaf.IsSheaf.isSheafFor W.property _ hmem)
  have key := (Presieve.isSheafFor_arrows_iff W.obj (partMap A hA)).1 hSF
  have hcompat : ∀ x, Presieve.Arrows.Compatible W.obj (partMap A hA) x := by
    intro x i k T gi gk hik
    by_cases h : i = k
    · subst h
      rw [(cancel_mono (partMap A hA i)).mp hik]
    · haveI hTe : IsEmpty ↥T := ⟨fun t => by
        have ht : (partMap A hA i) (gi t) = (partMap A hA k) (gk t) := by
          have h' := congrArg (fun f : T ⟶ S => ⇑(ConcreteCategory.hom f)) hik
          exact congrFun h' t
        have h1 : (partMap A hA i) (gi t) ∈ A i := (gi t).2
        have h2 : (partMap A hA k) (gk t) ∈ A k := (gk t).2
        exact Set.disjoint_left.mp (hdisj h) h1 (ht.symm ▸ h2)⟩
      haveI : Subsingleton (W.obj.obj (op T)) := subsingleton_of_isEmpty W hTe
      exact Subsingleton.elim _ _
  constructor
  · intro z z' h
    obtain ⟨u, -, huniq⟩ := key (fun i => W.obj.map (partMap A hA i).op z) (hcompat _)
    exact (huniq z fun i => rfl).trans ((huniq z' fun i => (congrFun h i).symm).symm)
  · intro x
    obtain ⟨z, hz, -⟩ := key x (hcompat x)
    exact ⟨z, funext hz⟩

end Work.CWIND.GClass
