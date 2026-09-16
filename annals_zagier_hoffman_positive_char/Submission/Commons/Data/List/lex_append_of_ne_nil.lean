import Mathlib

namespace Commons.Data.List

theorem lex_append_of_ne_nil {α : Type*} (r : α → α → Prop) (l rest : List α) (h : rest ≠ []) :
    List.Lex r l (l ++ rest) := by
  induction l with
  | nil =>
    cases rest with
    | nil => exact absurd rfl h
    | cons a t => exact List.Lex.nil
  | cons a t ih =>
    exact List.Lex.cons ih

end Commons.Data.List
