import Mathlib

namespace Work.Case1

/-- For an order-embedding-like `f` on `{a, b}` (given by the pointwise `↔`), `f` preserves `min`. -/
lemma f_min_eq {α β : Type*} [LinearOrder α] [LinearOrder β] {f : α → β} {a b : α}
    (h : f a < f b ↔ a < b) : f (min a b) = min (f a) (f b) := by
  rcases le_total a b with hab | hba
  · have hle : f a ≤ f b := by
      rcases lt_or_eq_of_le hab with hlt | heq
      · exact le_of_lt (h.mpr hlt)
      · rw [heq]
    rw [min_eq_left hab, min_eq_left hle]
  · have hle : f b ≤ f a := by
      rcases lt_or_eq_of_le hba with hlt | heq
      · have hf : ¬ (f a < f b) := (h.not).mpr (not_lt.mpr (le_of_lt hlt))
        exact not_lt.mp hf
      · rw [heq]
    rw [min_eq_right hba, min_eq_right hle]

/-- The `foldr min ⊤` of a list of coerced elements, when it is not `⊤`, is the coercion of a
member of the list. -/
lemma foldr_min_coe_mem {α : Type*} [LinearOrder α] (l : List α) :
    ∀ b : α, (l.map (fun a : α => (a : WithTop α))).foldr min ⊤ = (↑b : WithTop α) → b ∈ l := by
  induction l with
  | nil => intro b h; simp at h
  | cons a t ih =>
    intro b h
    rw [List.map_cons, List.foldr_cons] at h
    cases hM : (t.map (fun a : α => (a : WithTop α))).foldr min ⊤ with
    | top =>
      rw [hM, min_top_right] at h
      rw [WithTop.coe_eq_coe] at h
      rw [h]; exact List.mem_cons_self
    | coe c =>
      rw [hM, ← WithTop.coe_min] at h
      rw [WithTop.coe_eq_coe] at h
      rw [← h]
      rcases min_choice a c with hm | hm
      · rw [hm]; exact List.mem_cons_self
      · rw [hm]; exact List.mem_cons_of_mem a (ih c hM)

/-- Main auxiliary identity: for a function which is strictly increasing on the members of `l`,
taking the minimum of the image equals applying the function to the minimum (in `WithTop`). -/
lemma foldr_min_map_aux {α β : Type*} [LinearOrder α] [LinearOrder β] (f : α → β) :
    ∀ (l : List α), (∀ a ∈ l, ∀ b ∈ l, f a < f b ↔ a < b) →
      (l.map (fun a : α => (f a : WithTop β))).foldr min ⊤ =
        WithTop.map f ((l.map (fun a : α => (a : WithTop α))).foldr min ⊤) := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
    intro hf
    have ht : ∀ x ∈ t, ∀ y ∈ t, f x < f y ↔ x < y := by
      intro x hx y hy; exact hf x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy)
    rw [List.map_cons, List.foldr_cons, List.map_cons, List.foldr_cons]
    rw [ih ht]
    set M := (t.map (fun a : α => (a : WithTop α))).foldr min ⊤ with hM
    cases hMc : M with
    | top =>
      simp only [WithTop.map_top, min_top_right, WithTop.map_coe]
    | coe c =>
      have hc : c ∈ t := foldr_min_coe_mem t c (by rw [← hM, hMc])
      rw [WithTop.map_coe, ← WithTop.coe_min (f a) (f c), ← WithTop.coe_min a c,
          WithTop.map_coe, WithTop.coe_eq_coe]
      exact (f_min_eq (hf a List.mem_cons_self c (List.mem_cons_of_mem a hc))).symm

theorem foldr_min_map_of_mono {α β : Type*} [LinearOrder α] [LinearOrder β] (f : α → β)
    (l : List α) (s : Set α) (hl : ∀ a ∈ l, a ∈ s)
    (hf : ∀ a ∈ s, ∀ b ∈ s, f a < f b ↔ a < b) :
    (l.map (fun a => (f a : WithTop β))).foldr min ⊤ =
      ((l.map (fun a => (a : WithTop α))).foldr min ⊤).map f := by
  have hbridge : l.map (fun a => (a : WithTop α)) = l.map (fun a : α => (a : WithTop α)) := by
    rw [List.map_id', List.bind_eq_flatMap, List.map_eq_flatMap]
    congr 1
  rw [hbridge]
  exact foldr_min_map_aux f l (fun a ha b hb => hf a (hl a ha) b (hl b hb))

end Work.Case1
