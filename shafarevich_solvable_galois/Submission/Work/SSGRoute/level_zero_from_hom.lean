import Submission.Work.SSGRoute.level_decomp_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The degree-zero level decomposition from the `Hom`-level statement

If the localisation map on `Hom` (`thetaL0Map`) is bijective, then the degree-zero level
decomposition `thetaL k K R M 0 S` is bijective.  The reduction uses `Ext^0 ≃ Hom`
(`Abelian.Ext.addEquiv₀`) and the computation of `thetaL` in degree zero.
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module
attribute [local instance 1] ULift.module ULift.smulLeft ULift.mulAction ULift.smulZeroClass
attribute [local instance 1] ULift.distribSMul ULift.distribMulAction ULift.smulWithZero
attribute [local instance 1] ULift.mulActionWithZero

noncomputable section

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

variable (R : Set (NK.GlobalCFT.Place K))
  (M : Rep.{0,0,0} Coeff (K ≃ₐ[k] K)) (S : NK.HassePrinciple.GStableSet k K)

include R

/-- **The degree-zero level decomposition from the `Hom`-level statement.** -/
theorem thetaL_zero_bijective
    (h0 : Function.Bijective (thetaL0Map k K R M S)) :
    Function.Bijective (thetaL k K R M 0 S) := by
  have hmk : ∀ (G : Type) [Group G] (A B : Rep Coeff G) (f : A ⟶ B),
      Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ f) = f := by
    intro G _ A B f
    have h1 : Abelian.Ext.mk₀ f = Abelian.Ext.addEquiv₀.symm f := by
      conv_lhs => rw [← AddEquiv.apply_symm_apply Abelian.Ext.addEquiv₀ f]
      exact Abelian.Ext.mk₀_addEquiv₀_apply _
    rw [h1, AddEquiv.apply_symm_apply]
  constructor
  · intro x y hxy
    have hx : x = Abelian.Ext.mk₀ (Abelian.Ext.addEquiv₀ x) :=
      (Abelian.Ext.mk₀_addEquiv₀_apply x).symm
    have hy : y = Abelian.Ext.mk₀ (Abelian.Ext.addEquiv₀ y) :=
      (Abelian.Ext.mk₀_addEquiv₀_apply y).symm
    rw [hx, hy] at hxy
    have hφψ : thetaL0Map k K R M S (Abelian.Ext.addEquiv₀ x)
        = thetaL0Map k K R M S (Abelian.Ext.addEquiv₀ y) := by
      funext w
      have hc := congrFun hxy w
      rw [thetaL_zero_eq_mk₀, thetaL_zero_eq_mk₀] at hc
      have hc2 : Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀
            (thetaL0Map k K R M S (Abelian.Ext.addEquiv₀ x) w))
          = Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀
            (thetaL0Map k K R M S (Abelian.Ext.addEquiv₀ y) w)) :=
        congrArg Abelian.Ext.addEquiv₀ hc
      exact (hmk _ _ _ _).symm.trans (hc2.trans (hmk _ _ _ _))
    rw [hx, hy, h0.injective hφψ]
  · intro y
    obtain ⟨φ, hφ⟩ := h0.surjective (fun w => Abelian.Ext.addEquiv₀ (y w))
    refine ⟨Abelian.Ext.mk₀ φ, ?_⟩
    rw [thetaL_zero_eq_mk₀]
    funext w
    rw [congrFun hφ w, Abelian.Ext.mk₀_addEquiv₀_apply]

end

end Work.SSGRoute
