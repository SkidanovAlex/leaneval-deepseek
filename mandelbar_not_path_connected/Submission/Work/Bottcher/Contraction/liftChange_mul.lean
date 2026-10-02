import Mathlib
import Submission.Work.Bottcher.Contraction.LiftCoreDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.Contraction

/-- **Additivity of the lift change under pointwise products.**

The lift change of a nowhere-zero path is the endpoint difference of a lift through
`Complex.exp`; since `t ↦ L(t) + M(t)` is a lift of the product `δ₁ * δ₂` whenever `L`, `M`
lift `δ₁`, `δ₂`, the lift changes add. -/
theorem liftChange_mul (δ₁ δ₂ : C(unitInterval, ℂ)) (h₁ : ∀ t, δ₁ t ≠ 0) (h₂ : ∀ t, δ₂ t ≠ 0)
    (h : ∀ t, (δ₁ * δ₂) t ≠ 0) :
    Work.Bottcher.Contraction.liftChange (δ₁ * δ₂) h =
      Work.Bottcher.Contraction.liftChange δ₁ h₁ + Work.Bottcher.Contraction.liftChange δ₂ h₂ := by
  have he : Complex.exp (Complex.log (δ₁ 0) + Complex.log (δ₂ 0)) = (δ₁ * δ₂) 0 := by
    rw [Complex.exp_add, Complex.exp_log (h₁ 0), Complex.exp_log (h₂ 0), ContinuousMap.mul_apply]
  -- `L + M` is the lift of `δ₁ * δ₂` starting at `log (δ₁ 0) + log (δ₂ 0)`.
  have hkey : (fun t => liftOf δ₁ h₁ (Complex.log (δ₁ 0)) (Complex.exp_log (h₁ 0)) t
        + liftOf δ₂ h₂ (Complex.log (δ₂ 0)) (Complex.exp_log (h₂ 0)) t)
      = fun t => liftOf (δ₁ * δ₂) h (Complex.log (δ₁ 0) + Complex.log (δ₂ 0)) he t := by
    refine (Complex.isCoveringMap_exp.eq_liftPath_iff (γ := pathSubtype (δ₁ * δ₂) h)
      (e := Complex.log (δ₁ 0) + Complex.log (δ₂ 0)) (γ_0 := Subtype.ext he.symm)).mpr
      ⟨?_, ?_, ?_⟩
    · exact ((liftOf δ₁ h₁ _ _).continuous.add (liftOf δ₂ h₂ _ _).continuous)
    · funext t
      apply Subtype.ext
      show Complex.exp (liftOf δ₁ h₁ (Complex.log (δ₁ 0)) (Complex.exp_log (h₁ 0)) t
          + liftOf δ₂ h₂ (Complex.log (δ₂ 0)) (Complex.exp_log (h₂ 0)) t) = (δ₁ * δ₂) t
      rw [Complex.exp_add, exp_liftOf, exp_liftOf, ContinuousMap.mul_apply]
    · show liftOf δ₁ h₁ (Complex.log (δ₁ 0)) (Complex.exp_log (h₁ 0)) 0
          + liftOf δ₂ h₂ (Complex.log (δ₂ 0)) (Complex.exp_log (h₂ 0)) 0
        = Complex.log (δ₁ 0) + Complex.log (δ₂ 0)
      rw [liftOf_apply_zero, liftOf_apply_zero]
  rw [liftChange_eq_liftOf (δ₁ * δ₂) h (Complex.log (δ₁ 0) + Complex.log (δ₂ 0)) he]
  rw [liftChange, liftChange]
  rw [← congrFun hkey 1]
  ring

end Work.Bottcher.Contraction
