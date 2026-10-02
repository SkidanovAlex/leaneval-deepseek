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

noncomputable section

open scoped Topology

/-- The lift change is additive under concatenation of nowhere-zero paths.

The concatenation `concatC δ₁ δ₂ h` traverses `δ₁` on `[0, 1/2]` and `δ₂` on `[1/2, 1]`.
The (unique) lift of the concatenation starting at `Complex.log (δ₁ 0)` is obtained by
gluing the lift of `δ₁` (starting at `Complex.log (δ₁ 0)`) to the lift of `δ₂` starting at the
endpoint of the former.  Reading off the endpoint differences gives additivity of the lift
change. -/
theorem liftChange_concatC (δ₁ δ₂ : C(unitInterval, ℂ)) (h₁ : ∀ t, δ₁ t ≠ 0)
    (h₂ : ∀ t, δ₂ t ≠ 0) (h : δ₁ 1 = δ₂ 0)
    (hall : ∀ t, Work.Bottcher.LogLift.concatC δ₁ δ₂ h t ≠ 0) :
    Work.Bottcher.Contraction.liftChange (Work.Bottcher.LogLift.concatC δ₁ δ₂ h) hall =
      Work.Bottcher.Contraction.liftChange δ₁ h₁ +
        Work.Bottcher.Contraction.liftChange δ₂ h₂ := by
  -- Starting point of the lift of `δ₁`.
  let e₁ : ℂ := Complex.log (δ₁ 0)
  have he₁ : Complex.exp e₁ = δ₁ 0 := Complex.exp_log (h₁ 0)
  -- Lift of `δ₁` starting at `e₁`.
  let L₁ : C(unitInterval, ℂ) := liftOf δ₁ h₁ e₁ he₁
  have hL₁_0 : L₁ 0 = e₁ := liftOf_apply_zero δ₁ h₁ e₁ he₁
  have hL₁_exp : ∀ t, Complex.exp (L₁ t) = δ₁ t := fun t => exp_liftOf δ₁ h₁ e₁ he₁ t
  -- Starting point of the lift of `δ₂`: the endpoint of the lift of `δ₁`.
  let e₂ : ℂ := L₁ 1
  have he₂exp : Complex.exp e₂ = δ₂ 0 := by
    show Complex.exp (L₁ 1) = δ₂ 0
    rw [hL₁_exp 1, h]
  -- Lift of `δ₂` starting at `e₂`.
  let L₂ : C(unitInterval, ℂ) := liftOf δ₂ h₂ e₂ he₂exp
  have hL₂_0 : L₂ 0 = e₂ := liftOf_apply_zero δ₂ h₂ e₂ he₂exp
  have hL₂_exp : ∀ t, Complex.exp (L₂ t) = δ₂ t := fun t => exp_liftOf δ₂ h₂ e₂ he₂exp t
  -- The two lifts glue to a continuous nowhere-zero-by-construction path.
  have hglue : L₁ 1 = L₂ 0 := by rw [hL₂_0]
  -- The glued lift of the concatenation.
  let τ : C(unitInterval, ℂ) := concatC L₁ L₂ hglue
  have he₀ : Complex.exp e₁ = concatC δ₁ δ₂ h 0 :=
    he₁.trans (concatC_zero δ₁ δ₂ h).symm
  -- `τ` is a lift of the concatenation starting at `e₁`, hence it is *the* lift of the
  -- concatenation starting at `e₁` (uniqueness of path liftings through the exponential
  -- covering).
  have hτ : (fun t : unitInterval => τ t) = ⇑(liftOf (concatC δ₁ δ₂ h) hall e₁ he₀) := by
    refine (Complex.isCoveringMap_exp.eq_liftPath_iff (γ := pathSubtype (concatC δ₁ δ₂ h) hall)
      (e := e₁) (γ_0 := Subtype.ext he₀.symm)).mpr ⟨?_, ?_, ?_⟩
    · exact τ.continuous
    · funext t
      apply Subtype.ext
      by_cases ht : (t : ℝ) ≤ 1 / 2
      · rw [Function.comp_apply, concatC_apply_le L₁ L₂ hglue t ht]
        simp only [pathSubtype_apply]
        rw [concatC_apply_le δ₁ δ₂ h t ht, hL₁_exp]
      · rw [Function.comp_apply, concatC_apply_gt L₁ L₂ hglue t ht]
        simp only [pathSubtype_apply]
        rw [concatC_apply_gt δ₁ δ₂ h t ht, hL₂_exp]
    · show τ 0 = e₁
      rw [concatC_zero L₁ L₂ hglue, hL₁_0]
  -- Endpoint of the glued lift.
  have hτ1 : τ 1 = L₂ 1 := concatC_one L₁ L₂ hglue
  rw [liftChange_eq_liftOf (concatC δ₁ δ₂ h) hall e₁ he₀,
    liftChange_eq_liftOf δ₁ h₁ e₁ he₁,
    liftChange_eq_liftOf δ₂ h₂ e₂ he₂exp]
  rw [← congrFun hτ 1, hτ1]
  show L₂ 1 - e₁ = L₁ 1 - e₁ + (L₂ 1 - L₁ 1)
  ring

end

end Work.Bottcher.LogLift
