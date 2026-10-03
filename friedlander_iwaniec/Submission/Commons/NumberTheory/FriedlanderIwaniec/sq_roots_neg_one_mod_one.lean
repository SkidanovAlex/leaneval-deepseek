import Mathlib.Data.Set.Card

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- In the trivial ring `ZMod 1`, every element is `0` and `-1 = 0`, so the
unique element satisfies `α ^ 2 = -1`.  Hence the set of such roots is the
singleton `{0}`. -/
lemma sq_roots_neg_one_mod_one : ({α : ZMod 1 | α ^ 2 = -1}.ncard) = 1 := by
  have h : ({α : ZMod 1 | α ^ 2 = -1} : Set (ZMod 1)) = {0} := by
    ext α
    rw [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro _
      exact Subsingleton.elim α 0
    · intro hα
      rw [hα]
      decide
  rw [h, Set.ncard_singleton]

end Commons.NumberTheory.FriedlanderIwaniec