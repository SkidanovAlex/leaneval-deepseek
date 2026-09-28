import Mathlib
import Submission.Work.Serre.DiscPair.cylPreimageDefs

/-!
# The identification of the restricted mapping cylinder is a quotient map

For `q : C(X, Γ')` and `S ⊆ Γ'`, the map
`Work.Serre.DiscPair.cylPreimageLift q S : cyl (q|_S) → (cylRetract q) ⁻¹' S` identifies the
mapping cylinder of the restricted map `q|_S : q ⁻¹' S → S` with the part of the mapping cylinder
of `q` lying over `S`.  Here we show that it is a **quotient map**, assuming that the restriction
`cylPreSetRestrict q S` of the quotient map `cylMk q` to the saturated set
`cylPreSet q S = cylMk q ⁻¹' ((cylRetract q) ⁻¹' S)` is one (which it always is, see
`cylRestrictQuotient`).

The argument is the standard one for a composite of quotient maps.  Writing `ι` for the bijection
`(↥(q ⁻¹' S) × I) ⊕ ↥S → ↥(cylPreSet q S)` induced by `cylEmb q S` (which is a *homeomorphism*:
`cylEmb q S` is the sum of two embeddings with separated ranges), the square

  `cyl (q|_S) --cylPreimageLift--> (cylRetract q) ⁻¹' S`
      `↑cylMk`                              `↑`
  `(↥(q ⁻¹' S) × I) ⊕ ↥S --cylPreSetRestrict ∘ ι--> (cylRetract q) ⁻¹' S`

commutes.  Since `cylMk (q|_S)` is a quotient map, `cylPreimageLift q S` is a quotient map as
soon as `cylPreSetRestrict q S ∘ ι` is one, i.e. as soon as `ι` is one.
-/

set_option maxHeartbeats 1000000

open scoped Topology unitInterval

namespace Work.Serre.DiscPair

noncomputable section

variable {X Γ' : Type} [TopologicalSpace X] [TopologicalSpace Γ']

/-! ## The presentation of `cylPreSet` by the presenting sum of `cyl (q|_S)` -/

/-- The map from the presenting disjoint union of `cyl (q|_S)` to the saturated subset
`cylPreSet q S` of the presenting disjoint union of `cyl q`, induced by `cylEmb q S`.  It is a
bijection because `cylEmb q S` has image exactly `cylPreSet q S`. -/
def cylEmbSet (q : C(X, Γ')) (S : Set Γ') :
    (↥(q ⁻¹' S) × unitInterval) ⊕ ↥S → ↥(cylPreSet q S) :=
  fun a => ⟨cylEmb q S a, mem_cylPreSet_emb q S a⟩

@[simp] lemma cylEmbSet_apply (q : C(X, Γ')) (S : Set Γ')
    (a : (↥(q ⁻¹' S) × unitInterval) ⊕ ↥S) :
    (cylEmbSet q S a : (X × unitInterval) ⊕ Γ') = cylEmb q S a := rfl

/-- The image of the presenting map `cylEmb q S` is the saturated set `cylPreSet q S`. -/
lemma range_cylEmb (q : C(X, Γ')) (S : Set Γ') : Set.range (cylEmb q S) = cylPreSet q S := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩; exact mem_cylPreSet_emb q S b
  · intro ha
    rcases a with ⟨p, t⟩ | y
    · exact ⟨Sum.inl (⟨p, (mem_cylPreSet_inl q S p t).mp ha⟩, t), rfl⟩
    · exact ⟨Sum.inr ⟨y, (mem_cylPreSet_inr q S y).mp ha⟩, rfl⟩

/-- `cylEmb q S` is an embedding: it is the sum of the two embeddings
`↥(q ⁻¹' S) × I → X × I → (X × I) ⊕ Γ'` and `↥S → Γ' → (X × I) ⊕ Γ'`, whose ranges lie in the
two disjoint clopen summands. -/
lemma isEmbedding_cylEmb (q : C(X, Γ')) (S : Set Γ') : Topology.IsEmbedding (cylEmb q S) := by
  have h1 : Topology.IsEmbedding
      (fun z : ↥(q ⁻¹' S) × unitInterval =>
        (Sum.inl (z.1.1, z.2) : (X × unitInterval) ⊕ Γ')) := by
    have hh : Topology.IsEmbedding
        (Prod.map (Subtype.val) (id : unitInterval → unitInterval)) :=
      (Topology.IsEmbedding.subtypeVal (p := fun x : X => q x ∈ S)).prodMap
        Topology.IsEmbedding.id
    exact (Topology.IsEmbedding.inl (X := X × unitInterval) (Y := Γ')).comp hh
  have h2 : Topology.IsEmbedding
      (fun y : ↥S => (Sum.inr y.1 : (X × unitInterval) ⊕ Γ')) :=
    (Topology.IsEmbedding.inr (X := X × unitInterval) (Y := Γ')).comp
      (Topology.IsEmbedding.subtypeVal (p := fun y : Γ' => y ∈ S))
  have hsep : SeparatedNhds
      (Set.range (fun z : ↥(q ⁻¹' S) × unitInterval =>
        (Sum.inl (z.1.1, z.2) : (X × unitInterval) ⊕ Γ')))
      (Set.range (fun y : ↥S => (Sum.inr y.1 : (X × unitInterval) ⊕ Γ'))) := by
    refine ⟨Set.range Sum.inl, Set.range Sum.inr, isOpen_range_inl, isOpen_range_inr, ?_, ?_, ?_⟩
    · rintro _ ⟨z, rfl⟩; exact ⟨(z.1.1, z.2), rfl⟩
    · rintro _ ⟨y, rfl⟩; exact ⟨y.1, rfl⟩
    · rw [Set.disjoint_left]
      rintro x ⟨a, rfl⟩ ⟨b, hb⟩
      exact Sum.inl_ne_inr hb.symm
  have h := Topology.IsEmbedding.sumElim_of_separatedNhds h1 h2 hsep
  rw [show cylEmb q S = Sum.elim
        (fun z : ↥(q ⁻¹' S) × unitInterval =>
          (Sum.inl (z.1.1, z.2) : (X × unitInterval) ⊕ Γ'))
        (fun y : ↥S => (Sum.inr y.1 : (X × unitInterval) ⊕ Γ'))
      from funext (fun a => by cases a <;> rfl)]
  exact h

/-- `cylEmbSet q S` is an embedding: it is the corestriction of the embedding `cylEmb q S` to its
range. -/
lemma isEmbedding_cylEmbSet (q : C(X, Γ')) (S : Set Γ') :
    Topology.IsEmbedding (cylEmbSet q S) := by
  refine (Topology.IsEmbedding.of_comp_iff (f := cylEmbSet q S)
    (g := (Subtype.val : ↥(cylPreSet q S) → (X × unitInterval) ⊕ Γ'))
    (Topology.IsEmbedding.subtypeVal (p := fun a => a ∈ cylPreSet q S))).mp ?_
  exact isEmbedding_cylEmb q S

/-- `cylEmbSet q S` is surjective, because the image of `cylEmb q S` is `cylPreSet q S`. -/
lemma surjective_cylEmbSet (q : C(X, Γ')) (S : Set Γ') :
    Function.Surjective (cylEmbSet q S) := by
  intro b
  have hb : b.1 ∈ Set.range (cylEmb q S) := by rw [range_cylEmb]; exact b.2
  obtain ⟨a, ha⟩ := hb
  exact ⟨a, Subtype.ext ha⟩

/-- The main auxiliary statement: `cylEmbSet q S` is a quotient map (it is even a homeomorphism
onto `cylPreSet q S`). -/
lemma isQuotientMap_cylEmbSet (q : C(X, Γ')) (S : Set Γ') :
    Topology.IsQuotientMap (cylEmbSet q S) := by
  have hι := isEmbedding_cylEmbSet q S
  have hs := surjective_cylEmbSet q S
  have ho : Topology.IsOpenEmbedding (cylEmbSet q S) := hι.isOpenEmbedding_of_surjective hs
  exact IsOpenMap.isQuotientMap ho.isOpenMap ho.continuous hs

/-! ## The target -/

theorem isQuotientMap_cylPreimageLift {X Γ' : Type} [TopologicalSpace X] [TopologicalSpace Γ']
    (q : C(X, Γ')) (S : Set Γ')
    (h : Topology.IsQuotientMap (Work.Serre.DiscPair.cylPreSetRestrict q S)) :
    Topology.IsQuotientMap (Work.Serre.DiscPair.cylPreimageLift q S) := by
  -- `cylMk (q|_S)` is a quotient map
  have hq : Topology.IsQuotientMap (Work.Serre.cylMk (qS q S)) := isQuotientMap_quotient_mk'
  -- `cylEmbSet q S` is a quotient map, so the composite below is
  have hι : Topology.IsQuotientMap (cylEmbSet q S) := isQuotientMap_cylEmbSet q S
  have hcomp : Topology.IsQuotientMap (cylPreSetRestrict q S ∘ cylEmbSet q S) := h.comp hι
  -- the square commutes
  have hEq : (cylPreimageLift q S ∘ Work.Serre.cylMk (qS q S))
      = (cylPreSetRestrict q S ∘ cylEmbSet q S) := by
    funext a
    show cylPreimageLift q S (Work.Serre.cylMk (qS q S) a)
      = cylPreSetRestrict q S (cylEmbSet q S a)
    rw [cylPreimageLift_cylMk]
    cases a with
    | inl z => rfl
    | inr y => rfl
  have hcomp' : Topology.IsQuotientMap (cylPreimageLift q S ∘ Work.Serre.cylMk (qS q S)) :=
    hEq ▸ hcomp
  exact (Topology.IsQuotientMap.of_comp_iff (f := Work.Serre.cylMk (qS q S))
    (g := cylPreimageLift q S) hq).mp hcomp'

end

end Work.Serre.DiscPair
