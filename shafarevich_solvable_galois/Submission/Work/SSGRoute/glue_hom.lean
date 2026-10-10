import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Submission.Work.SSGRoute.glueIdele_smul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The glued morphism `M ⟶ 𝕀_K^S`

Combining `glueIdele` (the glued idèle) with its additivity and equivariance, we obtain the
`Gal(K/k)`-equivariant morphism `M ⟶ lvl k K S` exhibiting the surjectivity of `thetaL0Map`.
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
  (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
  (M : Rep.{0,0,0} Coeff (K ≃ₐ[k] K)) (S : NK.HassePrinciple.GStableSet k K)
  (hS : S.carrier.Finite)
  (a : ∀ w : R, Rep.res (decompK (k := k) w.1).subtype M ⟶ BOf k K w.1 S)

/-- **The glued morphism** `M ⟶ lvl k K S`, assembled from the local data on a transversal `R` of
the `Gal(K/k)`-orbits. -/
noncomputable def glueHom : M ⟶ lvl k K S :=
  glueHomOf k K R hR M S hS a (fun m τ => glueIdele_smul k K R hR M S hS a m τ)

/-- The value of the glued morphism. -/
theorem glueHom_apply (m : M.V) :
    (glueHom k K R hR M S hS a).hom m
      = Additive.ofMul (α := ↥(NK.HassePrinciple.levelSubgroup S.carrier))
          ⟨glueIdele k K R hR M S hS a m, glueIdele_mem k K R hR M S hS a m⟩ := rfl

end

end Work.SSGRoute
