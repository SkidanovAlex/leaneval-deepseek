import Mathlib
import Submission.Work.CurveBasics.Place

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.Point

open CategoryTheory AlgebraicGeometry in
theorem coheight_eq_one_of_isClosed {k : Type*} [Field k] (C : Work.CurveBasics.Curve k) {z : C.left}
    (hz : IsClosed {z}) : Order.coheight z = 1 := by
  have hle : Order.coheight z ≤ 1 := C.coheight_le_one z
  have hne : Order.coheight z ≠ 0 := by
    intro h0
    have hzg : z = genericPoint C.left := C.eq_genericPoint_of_coheight_eq_zero h0
    have hcl : IsClosed ({genericPoint C.left} : Set C.left) := hzg ▸ hz
    have hsub : ({genericPoint C.left} : Set C.left) = Set.univ := by
      rw [← hcl.closure_eq, genericPoint_closure]
    obtain ⟨a, b, hab⟩ := exists_pair_ne C.left
    refine hab ?_
    have ha : a ∈ ({genericPoint C.left} : Set C.left) := by rw [hsub]; trivial
    have hb : b ∈ ({genericPoint C.left} : Set C.left) := by rw [hsub]; trivial
    simpa using ha.trans hb.symm
  rcases (Order.le_one_iff (α := ℕ∞)).mp hle with h | h
  · exact absurd h hne
  · exact h

end Work.CurveBasics.Point
