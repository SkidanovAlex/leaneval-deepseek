import Mathlib
import Submission.Work.SymQuot.DivOf.AffineCurve
import Submission.Work.SymQuot.DivOf.placeIdeal_isMaximal

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open scoped Classical

universe u

namespace Work.SymQuot.DivOf

theorem le_placeOrder_iff {F : Type u} [Field F] {C : Work.CurveBasics.Curve F}
    {V : C.left.Opens} [Nonempty V] (hV : AlgebraicGeometry.IsAffineOpen V)
    [IsDedekindDomain ↥(C.left.presheaf.obj (Opposite.op V))]
    {J : Ideal ↥(C.left.presheaf.obj (Opposite.op V))} (hJ : J ≠ ⊥)
    (z : Work.CurveBasics.Curve.Place C) (hz : z.point ∈ V) (k : ℕ) :
    k ≤ Work.SymQuot.DivOf.placeOrder C V J z hz ↔
      J ≤ (Work.SymQuot.DivOf.placeIdeal C V z hz) ^ k := by
  by_cases hp : Work.SymQuot.DivOf.placeIdeal C V z hz = ⊥
  · -- Degenerate case: the ideal is zero, so `Associates.count` is zero.
    have hc : Work.SymQuot.DivOf.placeOrder C V J z hz = 0 := by
      rw [Work.SymQuot.DivOf.placeOrder, hp,
        show Associates.mk (⊥ : Ideal ↥(C.left.presheaf.obj (Opposite.op V))) = 0 from
          Associates.mk_eq_zero.mpr rfl]
      simp [Associates.count_reducible (not_irreducible_zero (M := Associates _))]
    rw [hc, hp]
    by_cases hk : k = 0
    · simp [hk]
    · rw [Ideal.bot_pow hk, le_bot_iff]
      exact ⟨fun h => absurd h (Nat.not_le.mpr (Nat.pos_of_ne_zero hk)), fun h => absurd h hJ⟩
  · -- Otherwise `placeIdeal` is a height one prime and we may use `idealOrder_le_iff`.
    let v : IsDedekindDomain.HeightOneSpectrum ↥(C.left.presheaf.obj (Opposite.op V)) :=
      { asIdeal := Work.SymQuot.DivOf.placeIdeal C V z hz
        isPrime := (Work.SymQuot.DivOf.placeIdeal_isMaximal hV z hz).isPrime
        ne_bot := hp }
    have hpo : Work.SymQuot.DivOf.placeOrder C V J z hz
        = Work.SymQuot.DivOf.idealOrder C V J v := rfl
    rw [hpo, Work.SymQuot.DivOf.idealOrder_le_iff C V hJ v k]

end Work.SymQuot.DivOf
