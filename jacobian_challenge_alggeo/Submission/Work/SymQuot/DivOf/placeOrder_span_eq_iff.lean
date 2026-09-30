import Mathlib
import Submission.Work.SymQuot.DivOf.le_placeOrder_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.SymQuot.DivOf

theorem placeOrder_span_eq_iff {F : Type u} [Field F] {C : Work.CurveBasics.Curve F}
    {V : C.left.Opens} [Nonempty V] (hV : AlgebraicGeometry.IsAffineOpen V)
    [IsDedekindDomain (C.left.presheaf.obj (Opposite.op V))]
    {a : C.left.presheaf.obj (Opposite.op V)} (ha : a ≠ 0)
    (z : Work.CurveBasics.Curve.Place C) (hz : z.point ∈ V) (k : ℕ) :
    Work.SymQuot.DivOf.placeOrder C V (Ideal.span {a}) z hz = k ↔
      a ∈ (Work.SymQuot.DivOf.placeIdeal C V z hz) ^ k ∧
        a ∉ (Work.SymQuot.DivOf.placeIdeal C V z hz) ^ (k + 1) := by
  have hJ : Ideal.span {a} ≠ ⊥ := fun h => ha (Ideal.span_singleton_eq_bot.mp h)
  have h1 := le_placeOrder_iff (C := C) (V := V) hV hJ z hz k
  have h2 := le_placeOrder_iff (C := C) (V := V) hV hJ z hz (k + 1)
  rw [Ideal.span_singleton_le_iff_mem] at h1 h2
  rw [← h1, ← h2]
  constructor
  · intro h
    omega
  · rintro ⟨h1', h2'⟩
    omega

end Work.SymQuot.DivOf
