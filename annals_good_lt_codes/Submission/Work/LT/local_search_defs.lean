import Mathlib
import Submission.Work.LT.lr_sound_defs

/-! Auxiliary definitions and interface lemmas for `local_search`.

`updateAt W α β g w` is the assignment obtained from `W` by replacing the view at the single
vertex `(α,β,g)` by `w` (the single-vertex move of the DELLM local-search algorithm, Algorithm 1).
-/

namespace Work.LT

open Classical

variable {G : Type} {Δ : ℕ}

/-- Replace the view at the vertex `(α,β,g)` of the assignment `W` by `w`, leaving every other
view unchanged.  This is the single-vertex move of DELLM Algorithm 1. -/
noncomputable def updateAt (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (α β : Fin 2) (g : G)
    (w : Fin Δ × Fin Δ → ZMod 2) : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2) :=
  fun α' β' g' => if α' = α ∧ β' = β ∧ g' = g then w else W α' β' g'

/-- The updated assignment takes the value `w` at the updated vertex. -/
lemma updateAt_self (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (α β : Fin 2) (g : G)
    (w : Fin Δ × Fin Δ → ZMod 2) : updateAt W α β g w α β g = w := by
  simp [updateAt]

/-- The updated assignment agrees with `W` away from the updated vertex. -/
lemma updateAt_of_ne (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (α β : Fin 2) (g : G)
    (w : Fin Δ × Fin Δ → ZMod 2) {α' β' : Fin 2} {g' : G}
    (h : ¬(α' = α ∧ β' = β ∧ g' = g)) : updateAt W α β g w α' β' g' = W α' β' g' := by
  simp [updateAt, h]

/-- Replacing one view of a valid assignment by a tensor codeword keeps the assignment valid. -/
lemma updateAt_mem (CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2))
    {W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)}
    (hW : ∀ α β g, W α β g ∈ tensorCode CA CB) {w : Fin Δ × Fin Δ → ZMod 2}
    (hw : w ∈ tensorCode CA CB) (α β : Fin 2) (g : G) :
    ∀ α' β' g', updateAt W α β g w α' β' g' ∈ tensorCode CA CB := by
  intro α' β' g'
  by_cases h : α' = α ∧ β' = β ∧ g' = g
  · obtain ⟨rfl, rfl, rfl⟩ := h
    rw [updateAt_self]
    exact hw
  · rw [updateAt_of_ne W α β g w h]
    exact hW α' β' g'

end Work.LT
