import Mathlib

namespace Work.OROneRel

universe u

/-- If every triple of elements of `ι` contains a repeat (so `ι` has no three
pairwise distinct elements) and `ι` contains two distinct elements `x ≠ y`,
then `ι` is in bijection with `Fin 2`.  Indeed, any element equals `x` or `y`. -/
theorem nonempty_equiv_fin_two_of_forall_eq_or {ι : Type u}
    (h : ∀ a b c : ι, a = b ∨ a = c ∨ b = c) (x y : ι) (hxy : x ≠ y) :
    Nonempty (ι ≃ Fin 2) := by
  classical
  have hz : ∀ z : ι, z = x ∨ z = y := by
    intro z
    rcases h x y z with h1 | h1 | h1
    · exact absurd h1 hxy
    · exact Or.inl h1.symm
    · exact Or.inr h1.symm
  refine ⟨{ toFun := fun z => if z = x then 0 else 1
            invFun := fun n => if n = 0 then x else y
            left_inv := ?_
            right_inv := ?_ }⟩
  · intro z
    rcases hz z with rfl | rfl
    · simp
    · simp [Ne.symm hxy]
  · intro n
    fin_cases n
    · simp
    · simp [Ne.symm hxy]

end Work.OROneRel
