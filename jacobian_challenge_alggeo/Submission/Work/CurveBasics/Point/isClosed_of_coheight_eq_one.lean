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
/-- A point of a curve of coheight (i.e. Krull dimension of the local ring, codimension) one
is a closed point.

Indeed, if `z` were not closed, its closure would contain a second point `y ≠ z`, and then
`y < z` in the specialization order.  Since `coheight z = 1`, `z` has a strict upper bound
(the generic point), so `y < z` would be the beginning of a chain of length `2` above `y`,
forcing `coheight y ≥ 2`, contradicting that every point of a curve has coheight at most one. -/
theorem isClosed_of_coheight_eq_one {k : Type*} [Field k] (C : Work.CurveBasics.Curve k) {z : C.left}
    (hz : Order.coheight z = 1) : IsClosed {z} := by
  rw [← closure_subset_iff_isClosed]
  intro y hy
  by_contra hmem
  have hyne : y ≠ z := by simpa using hmem
  -- `y ∈ closure {z}` means `z ⤳ y`, i.e. `y ≤ z`.
  have hyz : y ≤ z := by
    rw [Scheme.le_iff_specializes]
    exact specializes_iff_mem_closure.mpr hy
  -- Together with `y ≠ z` and the T0 property of schemes this is a *strict* inequality.
  have hlt : y < z := (Preorder.lt_iff_le_not_ge y z).mpr ⟨hyz, fun hzy => hyne (by
    have h1 : y ⤳ z := (Scheme.le_iff_specializes).mp hzy
    have h2 : z ⤳ y := (Scheme.le_iff_specializes).mp hyz
    exact T0Space.t0 (inseparable_iff_specializes_and.mpr ⟨h1, h2⟩))⟩
  have h2 : Order.coheight z + 1 ≤ Order.coheight y := Order.coheight_add_one_le hlt
  have h1 : Order.coheight y ≤ 1 := Work.CurveBasics.Curve.coheight_le_one C y
  rw [hz] at h2
  have : (2 : ℕ∞) ≤ (1 : ℕ∞) := by
    calc (2 : ℕ∞) = (1 : ℕ∞) + 1 := by norm_num
      _ ≤ Order.coheight y := h2
      _ ≤ 1 := h1
  norm_num at this

end Work.CurveBasics.Point
