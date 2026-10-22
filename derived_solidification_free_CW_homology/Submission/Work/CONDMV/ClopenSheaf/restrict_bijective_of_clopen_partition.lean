import Mathlib
import Submission.Work.CONDMV.Basic

set_option linter.style.haveILetI false

/-!
# Gluing along a clopen partition of a light profinite set

Let `S` be a light profinite set, `A`, `B` clopen subsets with `A ∪ B = S` and `A ∩ B = ∅`, and
let `Z` be a light condensed set.  Then a section of `Z` over `S` is the same thing as a pair of
sections over `A` and over `B`, i.e. the restriction map

`Z(S) ⟶ Z(A) × Z(B)`,  `z ↦ (z|A, z|B)`

is a bijection.

This is the sheaf (gluing) property of light condensed sets with respect to the covering family
given by the two clopen inclusions `A ↪ S`, `B ↪ S`, together with the description of the product
of a two-element family.  The only non-formal input is that a sheaf takes an *empty* light
profinite set to a point, which we prove from the fact that the empty family is a covering family
of the initial object for the coherent topology.
-/

namespace Work.CONDMV.ClopenSheaf

open CategoryTheory CategoryTheory.Limits Opposite LightProfinite

/-! ## The two pieces of a clopen partition, as a covering family -/

/-- The two pieces of a clopen partition, as a family of light profinite sets indexed by `Bool`:
the `false` piece is `A`, the `true` piece is `B`. -/
def partFam (S : LightProfinite.{0}) (A B : Set S) (hA : IsClopen A) (hB : IsClopen B) :
    Bool → LightProfinite.{0}
  | false => Work.CONDMV.clopenLP S A hA
  | true => Work.CONDMV.clopenLP S B hB

/-- The two inclusions of the pieces of a clopen partition into `S`, indexed by `Bool`. -/
def partMap (S : LightProfinite.{0}) (A B : Set S) (hA : IsClopen A) (hB : IsClopen B) :
    (i : Bool) → partFam S A B hA hB i ⟶ S
  | false => Work.CONDMV.clopenIncl S A hA
  | true => Work.CONDMV.clopenIncl S B hB

@[simp]
lemma partFam_false (S : LightProfinite.{0}) (A B : Set S) (hA : IsClopen A) (hB : IsClopen B) :
    partFam S A B hA hB false = Work.CONDMV.clopenLP S A hA := rfl

@[simp]
lemma partFam_true (S : LightProfinite.{0}) (A B : Set S) (hA : IsClopen A) (hB : IsClopen B) :
    partFam S A B hA hB true = Work.CONDMV.clopenLP S B hB := rfl

@[simp]
lemma partMap_false (S : LightProfinite.{0}) (A B : Set S) (hA : IsClopen A) (hB : IsClopen B) :
    partMap S A B hA hB false = Work.CONDMV.clopenIncl S A hA := rfl

@[simp]
lemma partMap_true (S : LightProfinite.{0}) (A B : Set S) (hA : IsClopen A) (hB : IsClopen B) :
    partMap S A B hA hB true = Work.CONDMV.clopenIncl S B hB := rfl

/-- The computation rule for the two inclusions: the copairing of the two inclusions applied to a
point of one of the pieces is the inclusion of that point. -/
lemma partMap_iota (S : LightProfinite.{0}) (A B : Set S) (hA : IsClopen A) (hB : IsClopen B)
    (i : Bool) (x : ↥(partFam S A B hA hB i)) :
    (Sigma.desc (partMap S A B hA hB)) (Sigma.ι (partFam S A B hA hB) i x)
      = (partMap S A B hA hB i) x := by
  rw [Sigma.ι_comp_desc_apply]

/-- The `false` piece is included into `S` by the underlying map of the subtype. -/
lemma partMap_false_apply (S : LightProfinite.{0}) (A B : Set S) (hA : IsClopen A)
    (hB : IsClopen B) (x : ↥(partFam S A B hA hB false)) :
    (partMap S A B hA hB false) x = Subtype.val x :=
  Work.CONDMV.clopenIncl_apply S A hA x

/-- The `true` piece is included into `S` by the underlying map of the subtype. -/
lemma partMap_true_apply (S : LightProfinite.{0}) (A B : Set S) (hA : IsClopen A)
    (hB : IsClopen B) (x : ↥(partFam S A B hA hB true)) :
    (partMap S A B hA hB true) x = Subtype.val x :=
  Work.CONDMV.clopenIncl_apply S B hB x

/-- Both inclusions of the pieces of a clopen partition are monomorphisms. -/
lemma mono_partMap_false (S : LightProfinite.{0}) (A B : Set S) (hA : IsClopen A)
    (hB : IsClopen B) : Mono (partMap S A B hA hB false) := by
  rw [CompHausLike.mono_iff_injective, partMap]
  exact Subtype.val_injective

lemma mono_partMap_true (S : LightProfinite.{0}) (A B : Set S) (hA : IsClopen A)
    (hB : IsClopen B) : Mono (partMap S A B hA hB true) := by
  rw [CompHausLike.mono_iff_injective, partMap]
  exact Subtype.val_injective

/-- A dependent family of elements indexed by `Bool` is the same thing as a pair of elements. -/
def partEquiv (Z : LightCondSet.{0}) (S : LightProfinite.{0}) (A B : Set S) (hA : IsClopen A)
    (hB : IsClopen B) :
    ((i : Bool) → Z.obj.obj (op (partFam S A B hA hB i))) ≃
      (Z.obj.obj (op (Work.CONDMV.clopenLP S A hA)) ×
        Z.obj.obj (op (Work.CONDMV.clopenLP S B hB))) where
  toFun x := (x false, x true)
  invFun p := fun i => match i with
    | false => p.1
    | true => p.2
  left_inv x := by funext i; cases i <;> rfl
  right_inv p := by ext <;> rfl

/-! ## A sheaf takes an empty light profinite set to a point -/

/-- The empty family of light profinite sets. -/
def emptyFam : Empty → LightProfinite.{0} := Empty.elim

/-- The empty family of morphisms into a light profinite set. -/
def emptyMap (T : LightProfinite.{0}) : (a : Empty) → emptyFam a ⟶ T :=
  fun a => Empty.instIsEmpty.elim a

/-- The empty family is an effective epimorphic family of an empty light profinite set: this is
the statement that an empty light profinite set is the initial object. -/
lemma effectiveEpiFamily_emptyMap (T : LightProfinite.{0}) (hT : IsEmpty ↥T) :
    EffectiveEpiFamily emptyFam (emptyMap T) := by
  rw [← effectiveEpi_desc_iff_effectiveEpiFamily, LightProfinite.effectiveEpi_iff_surjective]
  intro s
  exact (hT.false s).elim

/-- The empty sieve is a covering sieve of an empty light profinite set. -/
lemma sieve_ofArrows_emptyMap_mem (T : LightProfinite.{0}) (hT : IsEmpty ↥T) :
    Sieve.ofArrows emptyFam (emptyMap T) ∈ coherentTopology LightProfinite T := by
  apply coherentTopology.mem_sieves_of_hasEffectiveEpiFamily
  exact ⟨Empty, inferInstance, emptyFam, emptyMap T, effectiveEpiFamily_emptyMap T hT,
    fun a => a.elim⟩

/-- Sections of a light condensed set over an empty light profinite set form a point. -/
theorem subsingleton_of_isEmpty (Z : LightCondSet.{0}) {T : LightProfinite.{0}}
    (hT : IsEmpty ↥T) : Subsingleton (Z.obj.obj (op T)) := by
  have hSF := Presheaf.IsSheaf.isSheafFor Z.property (Sieve.ofArrows emptyFam (emptyMap T))
    (sieve_ofArrows_emptyMap_mem T hT)
  have hSF' : Presieve.IsSheafFor Z.obj
      (Presieve.ofArrows Empty.elim (fun a => Empty.instIsEmpty.elim a) : Presieve T) :=
    (Presieve.isSheafFor_iff_generate _).2 hSF
  have hterm : IsTerminal (Z.obj.obj (op T)) :=
    Presieve.isTerminal_of_isSheafFor_empty_presieve T Z.obj hSF'
  have hU : Unique (Z.obj.obj (op T)) := Types.isTerminalEquivUnique _ hterm
  exact Subsingleton.intro fun a b => (hU.uniq a).trans (hU.uniq b).symm

/-! ## The main statement -/

theorem restrict_bijective_of_clopen_partition (Z : LightCondSet.{0}) (S : LightProfinite.{0})
    (A B : Set S) (hA : IsClopen A) (hB : IsClopen B) (hcov : A ∪ B = (Set.univ : Set S))
    (hdisj : Disjoint A B) :
    Function.Bijective (fun z : Z.obj.obj (Opposite.op S) =>
      (Work.CONDMV.restrict Z S A hA z, Work.CONDMV.restrict Z S B hB z)) := by
  haveI monoA : Mono (partMap S A B hA hB false) := mono_partMap_false S A B hA hB
  haveI monoB : Mono (partMap S A B hA hB true) := mono_partMap_true S A B hA hB
  -- the two inclusions form a covering family
  have hsurj : Function.Surjective
      ⇑(ConcreteCategory.hom (Sigma.desc (partMap S A B hA hB))) := by
    intro s
    rcases (Set.mem_union _ _ _).1 (Set.eq_univ_iff_forall.1 hcov s) with hsA | hsB
    · refine ⟨Sigma.ι (partFam S A B hA hB) false
        (show ↥(partFam S A B hA hB false) from ⟨s, hsA⟩), ?_⟩
      rw [Sigma.ι_comp_desc_apply]
      exact Work.CONDMV.clopenIncl_apply S A hA ⟨s, hsA⟩
    · refine ⟨Sigma.ι (partFam S A B hA hB) true
        (show ↥(partFam S A B hA hB true) from ⟨s, hsB⟩), ?_⟩
      rw [Sigma.ι_comp_desc_apply]
      exact Work.CONDMV.clopenIncl_apply S B hB ⟨s, hsB⟩
  have hEff : EffectiveEpiFamily (partFam S A B hA hB) (partMap S A B hA hB) :=
    (effectiveEpi_desc_iff_effectiveEpiFamily (partFam S A B hA hB)
      (partMap S A B hA hB)).mp
      ((LightProfinite.effectiveEpi_iff_surjective (Sigma.desc (partMap S A B hA hB))).mpr hsurj)
  -- the sieve generated by the two inclusions is a covering sieve
  have hmem : Sieve.ofArrows (partFam S A B hA hB) (partMap S A B hA hB)
      ∈ coherentTopology LightProfinite S := by
    apply coherentTopology.mem_sieves_of_hasEffectiveEpiFamily
    exact ⟨Bool, inferInstance, partFam S A B hA hB, partMap S A B hA hB, hEff,
      fun i => Sieve.le_generate (Presieve.ofArrows (partFam S A B hA hB)
        (partMap S A B hA hB)) (partFam S A B hA hB i) (partMap S A B hA hB i)
        (Presieve.ofArrows.mk i)⟩
  -- hence `Z` is a sheaf for the corresponding presieve
  have hSF : Presieve.IsSheafFor Z.obj
      (Presieve.ofArrows (partFam S A B hA hB) (partMap S A B hA hB)) :=
    (Presieve.isSheafFor_iff_generate _).2
      (Presheaf.IsSheaf.isSheafFor Z.property _ hmem)
  have key := (Presieve.isSheafFor_arrows_iff Z.obj (partMap S A B hA hB)).1 hSF
  -- every pair of sections is compatible: this is where the empty intersection is used
  have hcompat : ∀ x, Presieve.Arrows.Compatible Z.obj (partMap S A B hA hB) x := by
    intro x i j T gi gj hij
    cases i <;> cases j
    · rw [(cancel_mono (partMap S A B hA hB false)).mp hij]
    · haveI hTe : IsEmpty ↥T := ⟨fun t => by
        have ht : (partMap S A B hA hB false) (gi t) = (partMap S A B hA hB true) (gj t) := by
          have h := congrArg (fun f : T ⟶ S => ⇑(ConcreteCategory.hom f)) hij
          exact congrFun h t
        have h1 : (partMap S A B hA hB false) (gi t) ∈ A := by
          rw [partMap_false]
          exact (gi t).2
        have h2 : (partMap S A B hA hB true) (gj t) ∈ B := by
          rw [partMap_true]
          exact (gj t).2
        exact Set.disjoint_left.mp hdisj h1 (ht.symm ▸ h2)⟩
      haveI : Subsingleton (Z.obj.obj (op T)) := subsingleton_of_isEmpty Z hTe
      exact Subsingleton.elim _ _
    · haveI hTe : IsEmpty ↥T := ⟨fun t => by
        have ht : (partMap S A B hA hB true) (gi t) = (partMap S A B hA hB false) (gj t) := by
          have h := congrArg (fun f : T ⟶ S => ⇑(ConcreteCategory.hom f)) hij
          exact congrFun h t
        have h1 : (partMap S A B hA hB true) (gi t) ∈ B := by
          rw [partMap_true]
          exact (gi t).2
        have h2 : (partMap S A B hA hB false) (gj t) ∈ A := by
          rw [partMap_false]
          exact (gj t).2
        exact Set.disjoint_left.mp hdisj h2 (ht ▸ h1)⟩
      haveI : Subsingleton (Z.obj.obj (op T)) := subsingleton_of_isEmpty Z hTe
      exact Subsingleton.elim _ _
    · rw [(cancel_mono (partMap S A B hA hB true)).mp hij]
  -- so the map `Z(S) ⟶ ∏_i Z(X i)` is a bijection
  have hbij : Function.Bijective
      (fun t : Z.obj.obj (op S) => fun i => Z.obj.map (partMap S A B hA hB i).op t) := by
    constructor
    · intro t t' h
      obtain ⟨u, -, huniq⟩ := key (fun i => Z.obj.map (partMap S A B hA hB i).op t) (hcompat _)
      exact (huniq t fun i => rfl).trans
        ((huniq t' fun i => (congrFun h i).symm).symm)
    · intro x
      obtain ⟨t, ht, -⟩ := key x (hcompat x)
      exact ⟨t, funext ht⟩
  -- composing with the description of the product gives the statement
  have hcomp := (partEquiv Z S A B hA hB).bijective.comp hbij
  have heq : (⇑(partEquiv Z S A B hA hB) ∘ fun t : Z.obj.obj (op S) =>
      fun i => Z.obj.map (partMap S A B hA hB i).op t)
      = fun z => (Work.CONDMV.restrict Z S A hA z, Work.CONDMV.restrict Z S B hB z) := by
    funext z
    rfl
  rwa [heq] at hcomp

end Work.CONDMV.ClopenSheaf
