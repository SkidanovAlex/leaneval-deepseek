import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GroupTheory.Abelian

set_option linter.style.haveILetI false in
/-- For a finite free `ℤ`-module `F` of rank `d`, the quotient `F / pF` has cardinality
`p ^ d`.  This is `ModN.natCard_eq` from Mathlib, specialised to the exact shape
`F ⧸ (LinearMap.lsmul ℤ F (p : ℤ)).range` required here. -/
theorem card_quot_lsmul_range_of_free {F : Type*} [AddCommGroup F] [Module.Free ℤ F]
    [Module.Finite ℤ F] (p : ℕ) (hp : p ≠ 0) :
    Nat.card (F ⧸ (LinearMap.lsmul ℤ F (p : ℤ)).range) = p ^ Module.finrank ℤ F := by
  haveI : NeZero p := ⟨hp⟩
  exact ModN.natCard_eq F p

end NK.GroupTheory.Abelian
