import Mathlib
import Submission.Work.OROneRel.MagnusGenDefs

namespace Work.OROneRel

universe u

/-- The list-level computation underlying `cohom_mk`: the product of the signed generators
`(x, true) ↦ c x`, `(x, false) ↦ -(c x)` reinterpreted multiplicatively is `ofAdd` of the
exponent sum. -/
theorem prod_map_cond_ofAdd {α : Type u} (c : α → ℤ) (L : List (α × Bool)) :
    (L.map fun x =>
        bif x.2 then Multiplicative.ofAdd (c x.1) else (Multiplicative.ofAdd (c x.1))⁻¹).prod
      = Multiplicative.ofAdd ((L.map fun x => bif x.2 then c x.1 else -(c x.1)).sum) := by
  rw [ofAdd_list_prod]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro x _
  obtain ⟨a, b⟩ := x
  cases b <;> simp

theorem cohom_mk {α : Type u} (c : α → ℤ) (L : List (α × Bool)) :
    Work.OROneRel.cohom c (FreeGroup.mk L) = Multiplicative.ofAdd (Work.OROneRel.lsig c L) := by
  rw [cohom, FreeGroup.lift_mk]
  rw [lsig, prod_map_cond_ofAdd]
  congr 1
  congr 1
  apply List.map_congr_left
  intro x _
  obtain ⟨a, b⟩ := x
  cases b <;> simp

end Work.OROneRel
