import Mathlib
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.RatHurewicz.AttachPush.CellInterior

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Open data on a cell attachment

Let `attachCells n Y ι f` be the space obtained from `Y` by attaching `(n+2)`-cells along the maps
`f : ι → C(S^{n+1}, Y)` (a quotient of `Y ⊕ (ι × D^{n+2})`).  The main result of this file,

`attachCells_openData`,

is the *open-data* description of the topology of that quotient: given an open `AY ⊆ Y` and opens
`Ai i ⊆ D^{n+2}` which are *compatible* along the gluing, i.e.
`f i z ∈ AY ↔ cellSphereToDisk n z ∈ Ai i` for every `i` and every `z ∈ S^{n+1}`, there is an open
`V ⊆ attachCells n Y ι f` whose preimages under the inclusions `attachIncl` and the characteristic
maps `cellMap i` are exactly `AY` and `Ai i`.

The set `V` is simply the image, under the quotient map, of the saturated set
`Sum.inl '' AY ∪ Sum.inr '' (⋃ i, Sigma.mk i '' Ai i)`; the compatibility hypothesis `hcomp` is
exactly what makes this set saturated for the gluing relation.
-/

namespace Work.StemsB

open Work.RatHurewicz

/-- A point of the left summand `Y ⊕ X` is in `A ⊕ B` iff it is in `A`. -/
private lemma mem_sum_inl_image_union {Y X : Type} {A : Set Y} {B : Set X} {y : Y} :
    Sum.inl y ∈ (Sum.inl '' A ∪ Sum.inr '' B : Set (Y ⊕ X)) ↔ y ∈ A := by
  simp [Set.mem_union, Set.mem_image]

/-- A point of the right summand `Y ⊕ X` is in `A ⊕ B` iff it is in `B`. -/
private lemma mem_sum_inr_image_union {Y X : Type} {A : Set Y} {B : Set X} {x : X} :
    Sum.inr x ∈ (Sum.inl '' A ∪ Sum.inr '' B : Set (Y ⊕ X)) ↔ x ∈ B := by
  simp [Set.mem_union, Set.mem_image]

/-- Membership in the union of the pieces `{i} × A i` of a sigma type. -/
private lemma mem_iUnion_sigma_image {ι : Type} {X : ι → Type} {A : ∀ i, Set (X i)}
    {i : ι} {x : X i} :
    (⟨i, x⟩ : Sigma X) ∈ (⋃ j, Sigma.mk j '' A j) ↔ x ∈ A i := by
  rw [Set.mem_iUnion]
  constructor
  · rintro ⟨j, hj⟩
    rw [Set.mem_image] at hj
    obtain ⟨a, ha, heq⟩ := hj
    rw [Sigma.mk.injEq] at heq
    obtain ⟨hji, hEq⟩ := heq
    subst hji
    rw [eq_of_heq hEq] at ha
    exact ha
  · intro hx
    exact ⟨i, ⟨x, hx, rfl⟩⟩

theorem attachCells_openData (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (AY : Set Y)
    (Ai : ∀ i : ι, Set (Work.RatHurewicz.cellDisk n))
    (hY : IsOpen AY) (hi : ∀ i : ι, IsOpen (Ai i))
    (hcomp : ∀ (i : ι) (z : Work.RatHurewicz.cellSphere n),
      f i z ∈ AY ↔ Work.RatHurewicz.cellSphereToDisk n z ∈ Ai i) :
    ∃ V : Set (Work.RatHurewicz.attachCells n Y ι f), IsOpen V ∧
      Work.RatHurewicz.attachIncl n Y ι f ⁻¹' V = AY ∧
      ∀ i : ι, Work.RatHurewicz.cellMap n Y ι f i ⁻¹' V = Ai i := by
  classical
  -- the data on the pieces of the disjoint union
  let T : Set (Σ _ : ι, cellDisk n) := ⋃ i, Sigma.mk i '' Ai i
  let S : Set (Y ⊕ (Σ _ : ι, cellDisk n)) := Sum.inl '' AY ∪ Sum.inr '' T
  -- the quotient map
  let q : (Y ⊕ (Σ _ : ι, cellDisk n)) → attachCells n Y ι f := Quotient.mk''
  have hmem_inl : ∀ y : Y, Sum.inl y ∈ S ↔ y ∈ AY := by
    intro y
    show Sum.inl y ∈ Sum.inl '' AY ∪ Sum.inr '' T ↔ y ∈ AY
    exact mem_sum_inl_image_union
  have hmem_inr : ∀ (i : ι) (x : cellDisk n),
      (Sum.inr (⟨i, x⟩ : Σ _ : ι, cellDisk n) : Y ⊕ (Σ _ : ι, cellDisk n)) ∈ S ↔
        x ∈ Ai i := by
    intro i x
    show Sum.inr ⟨i, x⟩ ∈ Sum.inl '' AY ∪ Sum.inr '' T ↔ x ∈ Ai i
    rw [mem_sum_inr_image_union]
    exact mem_iUnion_sigma_image
  -- `hcomp` says precisely that `S` is invariant under the gluing relation
  have hsat : ∀ a b, attachRel n Y ι f a b → (a ∈ S ↔ b ∈ S) := by
    rintro a b ⟨i, z, rfl, rfl⟩
    rw [hmem_inl, hmem_inr]
    exact hcomp i z
  have hEqv : ∀ a b, Relation.EqvGen (attachRel n Y ι f) a b → (a ∈ S ↔ b ∈ S) := by
    intro a b hab
    induction hab with
    | rel x y h => exact hsat x y h
    | refl x => exact Iff.rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  -- hence `S` is saturated, i.e. it is the preimage of its image under the quotient map
  have hpre : q ⁻¹' (q '' S) = S := by
    ext x
    constructor
    · rintro ⟨s, hs, hsq⟩
      have hsr : Relation.EqvGen (attachRel n Y ι f) s x := Quotient.eq''.mp hsq
      exact (hEqv s x hsr).mp hs
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hq : Topology.IsQuotientMap q := isQuotientMap_quotient_mk'
  have hT : IsOpen T := by
    rw [isOpen_sigma_iff]
    intro i
    have h : Sigma.mk i ⁻¹' T = Ai i := by
      ext x
      exact mem_iUnion_sigma_image
    rw [h]
    exact hi i
  have hS : IsOpen S := by
    show IsOpen (Sum.inl '' AY ∪ Sum.inr '' T)
    exact (isOpenMap_inl AY hY).union (isOpenMap_inr T hT)
  refine ⟨q '' S, ?_, ?_, ?_⟩
  · exact hq.isCoinducing.isOpen_preimage.mp (hpre.symm ▸ hS)
  · ext y
    show Sum.inl y ∈ q ⁻¹' (q '' S) ↔ y ∈ AY
    rw [hpre]
    exact hmem_inl y
  · intro i
    ext x
    show Sum.inr ⟨i, x⟩ ∈ q ⁻¹' (q '' S) ↔ x ∈ Ai i
    rw [hpre]
    exact hmem_inr i x

end Work.StemsB
