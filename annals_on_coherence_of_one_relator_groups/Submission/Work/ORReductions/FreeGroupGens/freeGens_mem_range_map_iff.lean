import Mathlib
import Submission.Work.ORReductions.Basic

/-!
# `FreeGroup.gens` versus the range of the induced map of an injection

For a set `S : Set α` the map `Subtype.val : S → α` induces
`FreeGroup.map Subtype.val : FreeGroup S →* FreeGroup α`.
We prove that an element lies in the range of this map exactly when all the free
generators occurring in it lie in `S`.
-/

namespace Work.ORReductions.FreeGroupGens

/-- Relabel the letters of a word by a map `f : α → β`. -/
def mapWord {α β : Type*} (f : α → β) (L : List (α × Bool)) : List (β × Bool) :=
  L.map fun p => (f p.1, p.2)

lemma mapWord_eq {α β : Type*} (f : α → β) (L : List (α × Bool)) :
    mapWord f L = L.map (fun p => (f p.1, p.2)) := rfl

/-- Regard a word over `S` as a word over `α` via the inclusion `S ↪ α`. -/
def includeWord {α : Type*} (S : Set α) (L : List (S × Bool)) : List (α × Bool) :=
  L.map fun q => (Subtype.val q.1, q.2)

lemma includeWord_eq {α : Type*} (S : Set α) (L : List (S × Bool)) :
    includeWord S L = L.map (fun q => (Subtype.val q.1, q.2)) := rfl

/-- An injective relabelling of letters preserves reducedness. -/
lemma isReduced_mapWord {α β : Type*} {f : α → β} (hf : Function.Injective f) :
    ∀ {L : List (α × Bool)}, FreeGroup.IsReduced L → FreeGroup.IsReduced (mapWord f L)
  | [], _ => FreeGroup.IsReduced.nil
  | [_], _ => FreeGroup.IsReduced.singleton
  | a :: b :: t, h => by
      rw [mapWord_eq, List.map_cons, List.map_cons, FreeGroup.isReduced_cons_cons]
      rw [FreeGroup.isReduced_cons_cons] at h
      exact ⟨fun h1 => h.1 (hf h1), isReduced_mapWord hf h.2⟩

/-- `toWord` commutes with an injective relabelling of the letters. -/
lemma toWord_map_of_injective {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (y : FreeGroup α) :
    (FreeGroup.map f y).toWord = mapWord f y.toWord := by
  have hred : FreeGroup.IsReduced (mapWord f y.toWord) :=
    isReduced_mapWord hf FreeGroup.isReduced_toWord
  conv_lhs =>
    rw [← FreeGroup.mk_toWord (x := y), FreeGroup.map.mk, ← mapWord_eq, FreeGroup.toWord_mk]
  exact hred.reduce_eq

/-- Membership in `FreeGroup.gens` in terms of `toWord`. -/
lemma mem_gens_iff {α : Type*} (x : FreeGroup α) (a : α) :
    a ∈ FreeGroup.gens x ↔
      (a, true) ∈ @FreeGroup.toWord α (Classical.decEq α) x ∨
      (a, false) ∈ @FreeGroup.toWord α (Classical.decEq α) x := by
  simp only [FreeGroup.gens, Set.mem_ofPred_eq, List.singleton_sublist]

/-- Every letter of the reduced word of `x` lies in `gens x`. -/
lemma mem_gens_of_mem_toWord {α : Type*} {x : FreeGroup α} {p : α × Bool}
    (hp : p ∈ @FreeGroup.toWord α (Classical.decEq α) x) : p.1 ∈ FreeGroup.gens x := by
  obtain ⟨a, b⟩ := p
  cases b
  · exact (mem_gens_iff x a).mpr (Or.inr hp)
  · exact (mem_gens_iff x a).mpr (Or.inl hp)

/-- A letter of a word over `S`, viewed in `α`, lies in `S`. -/
lemma mem_of_mem_includeWord {α : Type*} {S : Set α} {L : List (S × Bool)}
    {a : α} {b : Bool} (h : (a, b) ∈ includeWord S L) : a ∈ S := by
  simp only [includeWord_eq, List.mem_map, Prod.mk.injEq] at h
  obtain ⟨p, -, hp1, -⟩ := h
  rw [← hp1]
  exact p.1.2

theorem freeGens_mem_range_map_iff {α : Type*} {S : Set α} (x : FreeGroup α) :
    x ∈ Set.range (FreeGroup.map (Subtype.val : S → α)) ↔ FreeGroup.gens x ⊆ S := by
  classical
  constructor
  · rintro ⟨y, rfl⟩ a ha
    rw [mem_gens_iff] at ha
    rw [toWord_map_of_injective Subtype.val_injective y] at ha
    rcases ha with h | h
    · exact mem_of_mem_includeWord h
    · exact mem_of_mem_includeWord h
  · intro hx
    let g : {p : α × Bool // p ∈ x.toWord} → S × Bool :=
      fun p => (⟨p.1.1, hx (mem_gens_of_mem_toWord p.2)⟩, p.1.2)
    let w : List (S × Bool) := x.toWord.attach.map g
    refine ⟨FreeGroup.mk w, ?_⟩
    have hw : includeWord S w = x.toWord := by
      dsimp only [includeWord_eq, includeWord, w, g]
      rw [List.map_map]
      conv_rhs => rw [← List.attach_map_subtype_val x.toWord]
      apply List.map_congr_left
      intro p _
      rfl
    conv_rhs => rw [← FreeGroup.mk_toWord (x := x)]
    rw [FreeGroup.map.mk]
    exact congrArg FreeGroup.mk hw

end Work.ORReductions.FreeGroupGens
