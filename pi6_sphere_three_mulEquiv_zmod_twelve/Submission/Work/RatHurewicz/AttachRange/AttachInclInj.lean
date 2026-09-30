import Submission.Work.RatHurewicz.AttachCells

set_option synthInstance.maxHeartbeats 400000

open Work.RatHurewicz
open scoped Topology unitInterval

namespace Work.RatHurewicz.AttachRange

theorem cellSphereToDisk_injective (n : ℕ) : Function.Injective (cellSphereToDisk n) := by
  intro z z' h
  exact Subtype.ext (congrArg (fun p : cellDisk n => (p : EuclideanSpace ℝ (Fin (n + 2)))) h)

/-- The partition of `Y ⊕ (Σ i, D)` whose classes are the singletons of "interior" cell points and
the sets `{inl y} ∪ {inr (i,z) : cellSphereToDisk n z ∈ D_i, f i z = y}`. -/
def Cls (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellSphere n, Y))
    (a b : Y ⊕ (Σ _ : ι, cellDisk n)) : Prop :=
  a = b ∨ ∃ y : Y,
    (a = Sum.inl y ∨ ∃ (i : ι) (z : cellSphere n), a = Sum.inr ⟨i, cellSphereToDisk n z⟩ ∧ f i z = y) ∧
    (b = Sum.inl y ∨ ∃ (i : ι) (z : cellSphere n), b = Sum.inr ⟨i, cellSphereToDisk n z⟩ ∧ f i z = y)

theorem cls_rel (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellSphere n, Y)) :
    ∀ a b, attachRel n Y ι f a b → Cls n Y ι f a b := by
  rintro a b ⟨i, z, rfl, rfl⟩
  exact Or.inr ⟨f i z, Or.inl rfl, Or.inr ⟨i, z, rfl, rfl⟩⟩

theorem cls_refl (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellSphere n, Y))
    (a : Y ⊕ (Σ _ : ι, cellDisk n)) : Cls n Y ι f a a := Or.inl rfl

theorem cls_symm (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellSphere n, Y))
    {a b : Y ⊕ (Σ _ : ι, cellDisk n)} (h : Cls n Y ι f a b) : Cls n Y ι f b a := by
  rcases h with h | ⟨y, h1, h2⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨y, h2, h1⟩

theorem cls_trans (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellSphere n, Y))
    {a b c : Y ⊕ (Σ _ : ι, cellDisk n)} (hab : Cls n Y ι f a b) (hbc : Cls n Y ι f b c) :
    Cls n Y ι f a c := by
  rcases hab with h | ⟨y, h1, h2⟩
  · subst h; exact hbc
  rcases hbc with h' | ⟨y', h3, h4⟩
  · subst h'; exact Or.inr ⟨y, h1, h2⟩
  have hyy' : y = y' := by
    cases h2 with
    | inl h2inl =>
      cases h3 with
      | inl h3inl => exact Sum.inl.inj (h2inl.symm.trans h3inl)
      | inr h3inr =>
        obtain ⟨i', z', hz', -⟩ := h3inr
        exact absurd (Eq.trans (Eq.symm h2inl) hz') Sum.inl_ne_inr
    | inr h2inr =>
      obtain ⟨i, z, hz, hfz⟩ := h2inr
      cases h3 with
      | inl h3inl => exact absurd (Eq.trans (Eq.symm h3inl) hz) Sum.inl_ne_inr
      | inr h3inr =>
        obtain ⟨i', z', hz', hfz'⟩ := h3inr
        have hiz : (⟨i, cellSphereToDisk n z⟩ : Σ _ : ι, cellDisk n) =
            ⟨i', cellSphereToDisk n z'⟩ := Sum.inr.inj (hz.symm.trans hz')
        have hi : i = i' := congrArg (fun p : Σ _ : ι, cellDisk n => p.1) hiz
        have hzz : z = z' :=
          cellSphereToDisk_injective n (congrArg (fun p : Σ _ : ι, cellDisk n => p.2) hiz)
        subst hi
        rw [← hzz] at hfz'
        exact hfz.symm.trans hfz'
  subst hyy'
  exact Or.inr ⟨y, h1, h4⟩

theorem eqvGen_le_cls (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellSphere n, Y))
    {a b : Y ⊕ (Σ _ : ι, cellDisk n)} (h : Relation.EqvGen (attachRel n Y ι f) a b) :
    Cls n Y ι f a b := by
  induction h with
  | rel x x' hxx' => exact cls_rel n Y ι f x x' hxx'
  | refl x => exact cls_refl n Y ι f x
  | symm x x' _ ih => exact cls_symm n Y ι f ih
  | trans x x' x'' _ _ ih1 ih2 => exact cls_trans n Y ι f ih1 ih2

theorem attachIncl_injective (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) : Function.Injective (attachIncl n Y ι f) := by
  intro y y' h
  have h1 := eqvGen_le_cls n Y ι f (Quotient.exact h)
  rcases h1 with heq | ⟨w, h2, h3⟩
  · exact Sum.inl.inj heq
  · have hw : y = w := by
      cases h2 with
      | inl h2inl => exact Sum.inl.inj h2inl
      | inr h2inr => obtain ⟨i, z, hz, -⟩ := h2inr; exact absurd hz Sum.inl_ne_inr
    have hw' : y' = w := by
      cases h3 with
      | inl h3inl => exact Sum.inl.inj h3inl
      | inr h3inr => obtain ⟨i, z, hz, -⟩ := h3inr; exact absurd hz Sum.inl_ne_inr
    rw [hw, hw']

end Work.RatHurewicz.AttachRange
