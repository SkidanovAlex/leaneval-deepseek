import Mathlib
import Submission.Work.OROneRel.letterCountHalfAux

namespace Work.OROneRel

universe u

/-- The exponent-sum homomorphism `expSum t` evaluates on the word `L` to the multiplicative
integer `ofAdd (ssum t L)`: at the level of the list of letters, the exponent sum of `t` is exactly
`ssum t L`.

This is the bridge between the group-theoretic `expSum` (defined via `FreeGroup.lift`) and the
list-combinatorial `ssum`. -/
theorem expSum_mk_eq_ofAdd_ssum {α : Type u} (t : α) (L : List (α × Bool)) :
    Work.OROneRel.expSum t (FreeGroup.mk L) = Multiplicative.ofAdd (Work.OROneRel.ssum t L) := by
  classical
  unfold expSum
  rw [FreeGroup.lift_mk]
  -- the value of the lifted map on a single letter is `ofAdd (gfun t x)`
  have hφ : ∀ x : α × Bool,
      (bif x.2 then (if x.1 = t then Multiplicative.ofAdd (1 : ℤ) else 1)
        else (if x.1 = t then Multiplicative.ofAdd (1 : ℤ) else 1)⁻¹)
      = Multiplicative.ofAdd (gfun t x) := by
    rintro ⟨a, b⟩
    cases b <;> by_cases h : a = t <;> simp [gfun, h]
  rw [List.map_congr_left (fun a _ => hφ a), ssum, ofAdd_list_prod]
  congr 1
  exact (List.map_map (g := Multiplicative.ofAdd) (f := gfun t) (l := L)).symm

end Work.OROneRel
