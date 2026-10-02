import Mathlib
import Submission.Work.Bottcher.LogLift.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.LogLift

open Work.Bottcher.Contraction

theorem liftChange_revC (δ : C(unitInterval, ℂ)) (h : ∀ t, δ t ≠ 0)
    (hall : ∀ t, Work.Bottcher.LogLift.revC δ t ≠ 0) :
    Work.Bottcher.Contraction.liftChange (Work.Bottcher.LogLift.revC δ) hall =
      - Work.Bottcher.Contraction.liftChange δ h := by
  have he' : Complex.exp (Complex.log (revC δ 0)) = revC δ 0 := Complex.exp_log (hall 0)
  have he : Complex.exp (Complex.log (δ 0)) = δ 0 := Complex.exp_log (h 0)
  -- A lift of `revC δ` is obtained by running a lift of `δ` backwards.
  have hkey : (fun t => liftOf δ h (Complex.log (δ 0)) he (unitInterval.symm t)
        + (Complex.log (revC δ 0) - liftOf δ h (Complex.log (δ 0)) he 1))
      = fun t => liftOf (revC δ) hall (Complex.log (revC δ 0)) he' t := by
    refine (Complex.isCoveringMap_exp.eq_liftPath_iff (γ := pathSubtype (revC δ) hall)
      (e := Complex.log (revC δ 0)) (γ_0 := Subtype.ext he'.symm)).mpr ⟨?_, ?_, ?_⟩
    · exact ((liftOf δ h (Complex.log (δ 0)) he).continuous.comp
        unitInterval.continuous_symm).add_const _
    · funext t
      apply Subtype.ext
      show Complex.exp (liftOf δ h (Complex.log (δ 0)) he (unitInterval.symm t)
        + (Complex.log (revC δ 0) - liftOf δ h (Complex.log (δ 0)) he 1)) = revC δ t
      rw [Complex.exp_add, exp_liftOf δ h (Complex.log (δ 0)) he (unitInterval.symm t)]
      have h1 : Complex.exp (Complex.log (revC δ 0) - liftOf δ h (Complex.log (δ 0)) he 1) = 1 := by
        rw [Complex.exp_sub, he', exp_liftOf δ h (Complex.log (δ 0)) he 1]
        rw [revC_apply, unitInterval.symm_zero]
        exact div_self (h 1)
      rw [h1, mul_one]
      rfl
    · show liftOf δ h (Complex.log (δ 0)) he (unitInterval.symm 0)
          + (Complex.log (revC δ 0) - liftOf δ h (Complex.log (δ 0)) he 1) = Complex.log (revC δ 0)
      rw [unitInterval.symm_zero]
      ring
  rw [liftChange_eq_liftOf (revC δ) hall (Complex.log (revC δ 0)) he']
  rw [liftChange_eq_liftOf δ h (Complex.log (δ 0)) he]
  rw [← congrFun hkey 1]
  show liftOf δ h (Complex.log (δ 0)) he (unitInterval.symm 1)
      + (Complex.log (revC δ 0) - liftOf δ h (Complex.log (δ 0)) he 1) - Complex.log (revC δ 0)
    = - (liftOf δ h (Complex.log (δ 0)) he 1 - Complex.log (δ 0))
  rw [unitInterval.symm_one, liftOf_apply_zero]
  ring

end Work.Bottcher.LogLift
