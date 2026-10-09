import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalAnabelian.Counting

/-- The set of non-identity elements of a finite group has cardinality one less
than the cardinality of the group. -/
theorem natCard_subtype_ne_one (A : Type*) [Group A] [Finite A] :
    Nat.card {x : A // x ≠ 1} = Nat.card A - 1 := by
  have hA : Fintype A := Fintype.ofFinite A
  have hS : Fintype {x : A // x ≠ 1} := Fintype.ofFinite _
  have hO : Fintype {x : A // x = 1} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl (fun x : A => x = 1)]
  congr 1
  exact Fintype.card_eq_one_iff.mpr ⟨⟨1, rfl⟩, fun b => Subtype.ext b.2⟩

end NK.LocalAnabelian.Counting
