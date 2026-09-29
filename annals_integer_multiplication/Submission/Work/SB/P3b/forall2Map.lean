import Mathlib

namespace Work.SB.P3b

theorem forall2Map {α β γ : Type*} (f : α → γ) (g : β → γ) (l : List α) (l' : List β)
    (h : List.Forall₂ (fun a b => g b = f a) l l') : l'.map g = l.map f := by
  induction h with
  | nil => rfl
  | cons h1 _ ih => simp [h1, ih]

end Work.SB.P3b
