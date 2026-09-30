import Mathlib
import Submission.Work.SymQuot.DivOf.le_placeOrder_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.SymQuot.DivOf

theorem placeOrder_mono {F : Type u} [Field F] {C : Work.CurveBasics.Curve F}
    {V : C.left.Opens} [Nonempty V] (hV : AlgebraicGeometry.IsAffineOpen V)
    [IsDedekindDomain (C.left.presheaf.obj (Opposite.op V))]
    {K I : Ideal (C.left.presheaf.obj (Opposite.op V))} (hKI : K ≤ I) (hK : K ≠ ⊥)
    (z : Work.CurveBasics.Curve.Place C) (hz : z.point ∈ V) :
    Work.SymQuot.DivOf.placeOrder C V I z hz ≤ Work.SymQuot.DivOf.placeOrder C V K z hz := by
  by_cases hp : placeIdeal C V z hz = ⊥
  · -- Degenerate case: the place ideal is zero, so `Associates.count` is zero.
    have hzero : ∀ (J : Ideal ↥(C.left.presheaf.obj (Opposite.op V))),
        placeOrder C V J z hz = 0 := by
      intro J
      rw [placeOrder, hp,
        show Associates.mk (⊥ : Ideal ↥(C.left.presheaf.obj (Opposite.op V))) = 0 from
          Associates.mk_eq_zero.mpr rfl]
      simp [Associates.count_reducible (not_irreducible_zero (M := Associates _))]
    rw [hzero I, hzero K]
  · -- Otherwise `placeIdeal` is a height-one prime and `placeOrder = idealOrder`.
    let v : IsDedekindDomain.HeightOneSpectrum ↥(C.left.presheaf.obj (Opposite.op V)) :=
      { asIdeal := placeIdeal C V z hz
        isPrime := (placeIdeal_isMaximal hV z hz).isPrime
        ne_bot := hp }
    have hI : I ≠ ⊥ := fun h => hK (le_bot_iff.mp (h ▸ hKI))
    have e1 : placeOrder C V I z hz = idealOrder C V I v := rfl
    have e2 : placeOrder C V K z hz = idealOrder C V K v := rfl
    rw [e1, e2]
    -- `K ≤ I`, so `I ∣ K`, so the order of `I` is at most that of `K`.
    exact (idealOrder_le_iff C V hK v (idealOrder C V I v)).mpr
      (le_trans hKI ((idealOrder_le_iff C V hI v (idealOrder C V I v)).mp le_rfl))

end Work.SymQuot.DivOf
