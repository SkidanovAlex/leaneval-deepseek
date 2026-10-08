import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.Wagner

set_option linter.style.haveILetI false

/-- The complement of a single point in a finite type has cardinality one less than the whole. -/
theorem natCard_subtype_ne {α : Type*} [Finite α] (z : α) :
    Nat.card {x : α // x ≠ z} = Nat.card α - 1 := by
  classical
  letI := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl (fun x => x = z), Fintype.card_subtype_eq z]

end Work.Hering.Wagner
