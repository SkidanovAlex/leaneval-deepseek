import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Homological.Resolution

namespace Commons.RepresentationTheory.GroupCohomology

open CategoryTheory Limits Representation

open scoped MonoidAlgebra

variable {k : Type} [CommRing k]

lemma standardComplex_eps_single {G : Type} [Group G] (f : Fin 1 → G) (r : k) :
    Rep.standardComplex.ε k G (MonoidAlgebra.single f r) = r := by
  simp only [Rep.standardComplex.ε, Rep.hom_ofHom, IntertwiningMap.coe_mk, LinearMap.coe_comp,
    Function.comp_apply, MonoidAlgebra.coeffLinearEquiv_apply, Finsupp.linearCombination]
  simp

set_option backward.isDefEq.respectTransparency false in
lemma standardComplex_epsToSingle0_f_zero {G : Type} [Group G] :
    (Rep.standardComplex.εToSingle₀ k G).f 0 = Rep.standardComplex.ε k G := by
  unfold Rep.standardComplex.εToSingle₀
  exact ChainComplex.toSingle₀Equiv_symm_apply_f_zero (C := Rep.standardComplex k G)
    (X := Rep.trivial k G k) (Rep.standardComplex.ε k G) _

set_option maxHeartbeats 800000 in
lemma diagonalSuccIsoFree_inv_single_single {G : Type} [Group G] (m : ℕ)
    (f : Fin m → G) (g : G) (r : k) :
    (Rep.diagonalSuccIsoFree k G m).inv.hom
        (Finsupp.single f (MonoidAlgebra.single g r)) =
      MonoidAlgebra.single (g • Fin.partialProd f) r := by
  simp only [Rep.diagonalSuccIsoFree, Rep.diagonalSuccIsoTensorTrivial, Iso.trans_inv,
    Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  have step1 : (Rep.Hom.hom (Rep.leftRegularTensorTrivialIsoFree k G (Fin m → G)).inv)
      (Finsupp.single f (MonoidAlgebra.single g r)) =
        (MonoidAlgebra.single g (1 : k)) ⊗ₜ[k] (MonoidAlgebra.single f r) :=
    Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single f g r
  rw [step1]
  simp only [Rep.mkIso_inv, Representation.linearizeOfMulActionIso, Representation.Equiv.mk_symm,
    LinearEquiv.refl_symm, ConcreteCategory.hom_ofHom, Action.tensorObj_V, Action.trivial_V,
    Functor.mapIso_inv, Rep.tensor_V, Rep.tensor_ρ, Iso.symm_inv, Functor.Monoidal.μIso_hom,
    Rep.μ_hom, MonoidalCategory.tensorIso_inv, Representation.linearizeTrivialIso,
    Rep.hom_tensorHom, Representation.IntertwiningMap.tensor_apply,
    Representation.Equiv.coe_toIntertwiningMap, Representation.Equiv.mk_apply,
    LinearEquiv.refl_apply]
  have key₁ := Representation.linearizeMap_single (k := k)
    (Action.diagonalSuccIsoTensorTrivial G m).inv (g, f) ((1 : k) * r)
  have key₂ := Representation.LinearizeMonoidal.μ_apply_single_single (k := k)
    (X := Action.leftRegular G) (Y := Action.trivial G (Fin m → G)) g f 1 r
  refine ((congrArg (fun z => (Representation.linearizeMap
    (Action.diagonalSuccIsoTensorTrivial G m).inv) z) key₂).trans key₁).trans ?_
  rw [Action.diagonalSuccIsoTensorTrivial_inv_hom_apply, one_mul]

lemma singleMapHomologicalComplex_f_zero {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
    (F : C ⥤ D) [F.Additive] [F.PreservesZeroMorphisms] (X : C) :
    ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).hom.app X).f 0
      = 𝟙 (F.obj X) := by
  rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]

lemma mapProjectiveResolution_pi_f_zero {G : Type} [Group G] (S : Subgroup G) :
    ((Rep.resFunctor S.subtype).mapProjectiveResolution (Rep.barResolution k G)).π.f 0
    = (Rep.resFunctor S.subtype).map ((Rep.barResolution k G).π.f 0) := by
  rw [Functor.mapProjectiveResolution_π, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, singleMapHomologicalComplex_f_zero]
  simp only [Category.comp_id]
  rfl

lemma barResolution_pi_f_zero_eq {G : Type} [Group G] :
    (Rep.barResolution k G).π.f 0
      = (Rep.diagonalSuccIsoFree k G 0).inv ≫ Rep.standardComplex.ε k G := by
  rw [show (Rep.barResolution k G).π.f 0
      = (Rep.diagonalSuccIsoFree k G 0).inv ≫ (Rep.standardComplex.εToSingle₀ k G).f 0 from rfl]
  rw [standardComplex_epsToSingle0_f_zero]
  rfl

lemma barResolution_pi0_apply {G : Type} [Group G] (x : Fin 0 → G) (g : G) (r : k) :
    (Rep.barResolution k G).π.f 0 (Finsupp.single x (MonoidAlgebra.single g r)) = r := by
  rw [barResolution_pi_f_zero_eq]
  show (Rep.Hom.hom ((Rep.diagonalSuccIsoFree k G 0).inv ≫ Rep.standardComplex.ε k G))
      (Finsupp.single x (MonoidAlgebra.single g r)) = r
  rw [Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  rw [diagonalSuccIsoFree_inv_single_single]
  exact standardComplex_eps_single (g • Fin.partialProd x) r

theorem barComplex_res_comp_pi {k G : Type} [CommRing k] [Group G] (S : Subgroup G) :
    (Rep.freeLift k S ((Rep.resFunctor S.subtype).obj (Rep.free k G (Fin 0 → G)))
        (fun x : Fin 0 → S => Finsupp.single (S.subtype ∘ x) (1 : MonoidAlgebra k G)))
      ≫ ((Rep.resFunctor S.subtype).mapProjectiveResolution (Rep.barResolution k G)).π.f 0
    = (Rep.barResolution k S).π.f 0 := by
  apply Rep.free_ext
  intro a
  rw [mapProjectiveResolution_pi_f_zero]
  erw [Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  simp only [Rep.freeLift, Rep.hom_ofHom]
  rw [Representation.freeLift_single_single]
  simp only [map_one, one_smul, Module.End.one_apply]
  erw [Rep.resMap_hom_apply]
  rw [show (1 : MonoidAlgebra k G) = MonoidAlgebra.single 1 1 from rfl]
  rw [barResolution_pi0_apply]
  erw [barResolution_pi0_apply]

end Commons.RepresentationTheory.GroupCohomology