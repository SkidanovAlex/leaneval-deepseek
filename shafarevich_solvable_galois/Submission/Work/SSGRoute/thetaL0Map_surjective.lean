import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Submission.Work.SSGRoute.glue_hom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Surjectivity of the degree-zero level decomposition map

The glued morphism `glueHom k K R hR M S hS a` (built in `glue_hom.lean` from the local data `a`)
realises every family of local maps as the localisation of a global level class: this file proves
`thetaL0Map k K R M S` is surjective.
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module
attribute [local instance 1] ULift.module ULift.smulLeft ULift.mulAction ULift.smulZeroClass
attribute [local instance 1] ULift.distribSMul ULift.distribMulAction ULift.smulWithZero
attribute [local instance 1] ULift.mulActionWithZero

noncomputable section

/-- Universe-polymorphic `cast_symm_self`: cancelling two inverse transports of an element. -/
theorem thetaL0_cast_symm_self {α : Sort*} {F : α → Sort*} {a b : α} (h : a = b) (x : F a) :
    h.symm ▸ (h ▸ x) = x := by cases h; rfl

set_option backward.isDefEq.respectTransparency false in
theorem thetaL0Map_surjective (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (M : Rep.{0, 0, 0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) (S : NK.HassePrinciple.GStableSet k K)
    (hS : S.carrier.Finite) :
    Function.Surjective (Work.SSGRoute.thetaL0Map k K R M S) := by
  intro b
  refine ⟨glueHom k K R hR M S hS b, ?_⟩
  funext w
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  ext m
  let X : (Rep.res (decompK (k := k) w.1).subtype (lvl k K S)).V :=
    (Rep.Hom.hom (glueHom k K R hR M S hS b)) m
  show (Rep.Hom.hom (levelEval k K w.1 S)) X = (Rep.Hom.hom (b w)) m
  have hX : X = (Rep.Hom.hom (Rep.resMap (decompK (k := k) w.1).subtype
      (glueHom k K R hR M S hS b))) m := rfl
  by_cases hw : (w : NK.GlobalCFT.Place K) ∈ S.carrier
  · rw [levelEval, dif_pos hw]
    rw [Rep.comp_apply]
    rw [levelEvalA_apply]
    rw [toMul_ofMul]
    rw [hX, Rep.resMap_hom_apply, glueHom_apply]
    rw [toMul_ofMul]
    rw [glueIdele_apply_repr k K R hR M S hS b w m]
    rw [BOfIncl_of_mem (k := k) (K := K) hw]
    rw [repEqToHom_hom_apply]
    rw [repEqToHom_hom_apply]
    rw [show toLocal k K (w : NK.GlobalCFT.Place K) (BOf_of_mem (k := k) (K := K) hw ▸ ((b w).hom m))
        = Additive.ofMul (toLocal k K (w : NK.GlobalCFT.Place K)
            (BOf_of_mem (k := k) (K := K) hw ▸ ((b w).hom m))) from rfl]
    simp only [toLocal, ofMul_toMul]
    exact thetaL0_cast_symm_self (BOf_of_mem (k := k) (K := K) hw) ((b w).hom m)
  · rw [levelEval, dif_neg hw]
    rw [Rep.comp_apply]
    rw [levelEvalSub_apply]
    simp only [hX, Rep.resMap_hom_apply, glueHom_apply, toMul_ofMul]
    rw [repEqToHom_hom_apply]
    simp only [glueIdele_apply_repr, BOfIncl_of_notMem (k := k) (K := K) hw, Rep.comp_apply,
      repEqToHom_hom_apply, toLocal]
    exact thetaL0_cast_symm_self (BOf_of_notMem (k := k) (K := K) hw) ((b w).hom m)

end

end Work.SSGRoute
