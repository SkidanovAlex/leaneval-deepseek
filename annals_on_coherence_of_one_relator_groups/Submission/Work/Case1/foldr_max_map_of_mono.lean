import Mathlib

namespace Work.Case1

/-- The maximum of a nonempty list of elements of a linear order, viewed inside `WithBot`, is
the lift of an element of the list. -/
private lemma foldr_max_lift_mem {γ : Type*} [LinearOrder γ] (L : List γ) (hL : L ≠ []) :
    ∃ c ∈ L, List.foldr max ⊥ (List.map (fun c : γ => (c : WithBot γ)) L) = (c : WithBot γ) := by
  revert hL
  induction L with
  | nil => intro h; exact absurd rfl h
  | cons a t ih =>
    intro hL
    by_cases ht : t = []
    · subst ht
      refine ⟨a, by simp, by simp⟩
    · obtain ⟨c, hc, hce⟩ := ih ht
      refine ⟨max a c, ?_, ?_⟩
      · rcases max_choice a c with h | h
        · rw [h]; exact List.mem_cons_self
        · rw [h]; exact List.mem_cons_of_mem a hc
      · rw [List.map_cons, List.foldr_cons, hce, WithBot.coe_max]

/-- `WithBot.map f` commutes with `max` on arguments that are either `⊥` or the lift of an
element of `s`, provided `f` preserves `max` on `s`. -/
private lemma withBot_map_max {α β : Type*} [LinearOrder α] [LinearOrder β] (f : α → β) (s : Set α)
    (hmax : ∀ a ∈ s, ∀ b ∈ s, f (max a b) = max (f a) (f b)) :
    ∀ {x y : WithBot α}, (x = ⊥ ∨ ∃ a ∈ s, x = (a : WithBot α)) →
      (y = ⊥ ∨ ∃ b ∈ s, y = (b : WithBot α)) →
      WithBot.map f (max x y) = max (WithBot.map f x) (WithBot.map f y) := by
  intro x y hx hy
  rcases hx with rfl | ⟨a, ha, rfl⟩
  · rcases hy with rfl | ⟨b, hb, rfl⟩ <;> simp
  · rcases hy with rfl | ⟨b, hb, rfl⟩
    · simp
    · rw [← WithBot.coe_max, WithBot.map_coe, hmax a ha b hb, WithBot.coe_max, WithBot.map_coe,
        WithBot.map_coe]

theorem foldr_max_map_of_mono {α β : Type*} [LinearOrder α] [LinearOrder β] (f : α → β)
    (l : List α) (s : Set α) (hl : ∀ a ∈ l, a ∈ s)
    (hf : ∀ a ∈ s, ∀ b ∈ s, f a < f b ↔ a < b) :
    (l.map (fun a => (f a : WithBot β))).foldr max ⊥ =
      ((l.map (fun a => (a : WithBot α))).foldr max ⊥).map f := by
  -- `f` is monotone (and reflects the order) on `s`
  have hle : ∀ a ∈ s, ∀ b ∈ s, (f a ≤ f b ↔ a ≤ b) := by
    intro a ha b hb
    constructor
    · intro h
      by_contra hcon
      exact not_le_of_gt ((hf b hb a ha).2 (lt_of_not_ge hcon)) h
    · intro h
      rcases lt_or_eq_of_le h with hlt | heq
      · exact le_of_lt ((hf a ha b hb).2 hlt)
      · rw [heq]
  -- hence `f` preserves `max` on `s`
  have hmaxf : ∀ a ∈ s, ∀ b ∈ s, f (max a b) = max (f a) (f b) := by
    intro a ha b hb
    rcases le_total a b with h | h
    · rw [max_eq_right h, max_eq_right ((hle a ha b hb).2 h)]
    · rw [max_eq_left h, max_eq_left ((hle b hb a ha).2 h)]
  -- the main induction, in the `List.foldr` form of the statement
  have key : ∀ L : List α, (∀ a ∈ L, a ∈ s) →
      List.foldr max ⊥ (List.map (fun a : α => (f a : WithBot β)) L) =
        WithBot.map f (List.foldr max ⊥ (List.map (fun a : α => (a : WithBot α)) L)) := by
    intro L
    induction L with
    | nil => intro _; simp
    | cons a t ih =>
      intro hL
      have ha : a ∈ s := hL a (by simp)
      have ht : ∀ b ∈ t, b ∈ s := fun b hb => hL b (by simp [hb])
      rw [List.map_cons, List.foldr_cons, List.map_cons, List.foldr_cons, ih ht]
      -- the maximum of the tail is `⊥` or the lift of an element of `s`
      have hM : (List.foldr max ⊥ (List.map (fun a : α => (a : WithBot α)) t) = ⊥
          ∨ ∃ b ∈ s, List.foldr max ⊥ (List.map (fun a : α => (a : WithBot α)) t)
              = (b : WithBot α)) := by
        by_cases htne : t = []
        · left; rw [htne]; simp
        · obtain ⟨c, hc, hce⟩ := foldr_max_lift_mem t htne
          exact Or.inr ⟨c, ht c hc, hce⟩
      have h := withBot_map_max f s hmaxf (Or.inr ⟨a, ha, rfl⟩) hM
      rw [WithBot.map_coe] at h
      exact h.symm
  rw [List.map_id', List.bind_eq_flatMap]
  have hfm : List.flatMap (fun a : α => pure ((a : WithBot α))) l =
      List.map (fun a : α => (a : WithBot α)) l :=
    List.flatMap_pure_eq_map (fun a : α => (a : WithBot α)) l
  rw [hfm]
  exact key l hl

end Work.Case1
