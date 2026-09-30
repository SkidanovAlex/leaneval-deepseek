import Mathlib
import Submission.Work.SSSR.Cohomology.Chains
import Submission.Work.Cohomology.sphereVanishing
import Submission.Work.Cohomology.sphereHomologyTop
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option synthInstance.maxHeartbeats 400000

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open CategoryTheory Limits AlgebraicTopology Simplicial
open scoped Simplicial TensorProduct
namespace Work.SSSR.StemsB.SphRat

noncomputable section

/-! ## 1. Extension of scalars is additive -/

/-- `LinearMap.baseChange` is additive in its linear-map argument. -/
lemma baseChange_add {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (g h : M →ₗ[R] N) :
    LinearMap.baseChange S (g + h) = LinearMap.baseChange S g + LinearMap.baseChange S h := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
      rw [LinearMap.baseChange_tmul, LinearMap.add_apply, LinearMap.add_apply, TensorProduct.tmul_add,
          LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
  | add x y hx hy =>
      rw [map_add, LinearMap.add_apply, map_add, map_add, hx, hy, LinearMap.add_apply,
        LinearMap.add_apply]
      abel

/-- **Extension of scalars along a ring homomorphism is an additive functor.** -/
instance extendScalarsAdditive {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (ModuleCat.extendScalars f).Additive where
  map_add {M N} g h := by
    letI : Algebra R S := f.toAlgebra
    apply ModuleCat.hom_ext
    show LinearMap.baseChange S (ModuleCat.Hom.hom (g + h)) =
        LinearMap.baseChange S (ModuleCat.Hom.hom g) + LinearMap.baseChange S (ModuleCat.Hom.hom h)
    rw [ModuleCat.hom_add, baseChange_add]

/-! ## 2. Coproducts and the functor `sigmaConst` -/

/-- **A functor preserving coproducts commutes with `sigmaConst`.**  The coproduct of copies of `R`
indexed by a type, mapped by `F`, is the coproduct of copies of `F.obj R`. -/
noncomputable def sigmaConstObjCompIso {C : Type*} [Category* C] {D : Type*} [Category* D]
    [HasCoproducts.{0} C] [HasCoproducts.{0} D] (F : C ⥤ D)
    [∀ (S : Type), PreservesColimitsOfShape (Discrete S) F] (R : C) :
    Limits.sigmaConst.obj R ⋙ F ≅ Limits.sigmaConst.obj (F.obj R) :=
  NatIso.ofComponents (fun S => PreservesCoproduct.iso F (fun _ : S ↦ R)) (by
    intro S T g
    have key : ∀ (U : Type) (t : U),
        F.map (Sigma.ι (fun _ : U ↦ R) t) ≫ (PreservesCoproduct.iso F (fun _ : U ↦ R)).hom
          = Sigma.ι (fun _ : U ↦ F.obj R) t := by
      intro U t
      have h2 : inv (sigmaComparison F (fun _ : U ↦ R)) =
          (PreservesCoproduct.iso F (fun _ : U ↦ R)).hom := by
        refine IsIso.inv_eq_of_hom_inv_id ?_
        rw [← PreservesCoproduct.inv_hom, Iso.inv_hom_id]
      have h := map_ι_comp_inv_sigmaComparison F (fun _ : U ↦ R) t
      rw [h2] at h
      exact h
    apply (isColimitOfHasCoproductOfPreservesColimit F (fun _ : S ↦ R)).hom_ext
    rintro ⟨s⟩
    simp only [Functor.comp_obj, Functor.comp_map, Cofan.mk_ι_app]
    dsimp only [Limits.sigmaConst]
    rw [← Category.assoc, ← F.map_comp, Sigma.ι_comp_map', Category.id_comp, key T (g s),
      ← Category.assoc, key S s, Sigma.ι_comp_map', Category.id_comp])

end

end Work.SSSR.StemsB.SphRat

namespace Work.SSSR.StemsB

open SphRat
end Work.SSSR.StemsB
