import Mathlib
import Submission.Work.SSGRoute.ext2_iso_cohomology_defs
import Submission.Work.SSGRoute.module_free_ulift_int
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The augmentation `C_• ⊗ R ⟶ R` of the tensored bar resolution is a quasi-isomorphism

For a group `G` and a `Rep Coeff G` (`Coeff = ULift ℤ`) whose underlying abelian group is a
finitely generated free `ℤ`-module, the augmentation

`stdTensorAug G R : stdTensorComplex G R ⟶ (single₀ C).obj R`

(tensoring the bar resolution of the trivial module with `R`) is a quasi-isomorphism.  This is the
statement that `stdTensorComplex G R` is a projective resolution of `R`.

The proof goes through the `ℤ`-flatness of `R.V`:

* `R.V` is free over `ℤ`, hence (by `module_flat_ulift_int`) free — in particular flat — over
  `Coeff`, so `- ⊗ R` is exact on `Rep Coeff G`;
* abstractly, exactness of `- ⊗ R` says that `tensorRight R` preserves homology, so whiskering the
  quasi-isomorphism `π : barResolution.complex ⟶ ℤ[0]` with `R` stays a quasi-isomorphism;
* finally `stdTensorAug` is `π ▷ R` followed by the canonical identification
  `ℤ ⊗ R ≅ R` (`stdTensorAug_eq`), and an isomorphism of complexes does not change
  quasi-isomorphisms.

The exactness input is transported through the forgetful functor `Rep Coeff G ⥤ ModuleCat Coeff`,
whose target is where Mathlib's flatness API lives.
-/

namespace Work.SSGRoute

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module
attribute [local instance 1] ULift.module ULift.smulLeft ULift.mulAction ULift.smulZeroClass
attribute [local instance 1] ULift.distribSMul ULift.distribMulAction ULift.smulWithZero
attribute [local instance 1] ULift.mulActionWithZero ZSMul.toSMul

noncomputable section

open CategoryTheory MonoidalCategory Limits
open scoped TensorProduct ZeroObject

set_option backward.isDefEq.respectTransparency false

variable (G : Type) [Group G]

/-- The forgetful functor `Rep Coeff G ⥤ ModuleCat Coeff`. -/
abbrev stdTensorAugPhi (G : Type) [Group G] :
    Rep.{0} SSGRoute.PTExt.Coeff G ⥤ ModuleCat.{0} SSGRoute.PTExt.Coeff := forget₂ _ _

/-- The `ULift ℤ`-module structure of a `Rep Coeff G` and its canonical `ℤ`-module structure
agree: `s • m = s.down • m`. -/
lemma rep_ulift_smul_eq (R : Rep.{0} SSGRoute.PTExt.Coeff G) (s : ULift.{0} ℤ) (m : R.V) :
    s • m = s.down • m := by
  obtain ⟨k⟩ := s
  have h1 : ∀ (k : ℤ), (ULift.up k) • m = k • (ULift.up (1 : ℤ) • m) := by
    intro k
    let f : ℤ →+ R.V :=
      { toFun := fun k => (ULift.up k) • m
        map_zero' := by rw [show ULift.up (0 : ℤ) = (0 : ULift ℤ) from rfl, zero_smul]
        map_add' := fun a b => by
          rw [show ULift.up (a + b) = ULift.up a + ULift.up b from rfl, add_smul] }
    have h := AddMonoidHom.map_zsmul f k (1 : ℤ)
    rw [show (k : ℤ) • (1 : ℤ) = k from by simp] at h
    exact h
  have h2 : (ULift.up (1 : ℤ)) • m = m := by
    rw [show ULift.up (1 : ℤ) = (1 : ULift ℤ) from rfl, one_smul]
  rw [h1 k, h2]

/-- The underlying `Coeff`-module of a `Rep Coeff G` with `ℤ`-free underlying abelian group is
flat (it is even free). -/
lemma rep_flat_coeff (R : Rep.{0} SSGRoute.PTExt.Coeff G) [Module.Free ℤ R.V] :
    Module.Flat SSGRoute.PTExt.Coeff R.V :=
  module_flat_ulift_int (fun s m => rep_ulift_smul_eq G R s m) (inferInstance)

/-- `tensorRight R` composed with the bar resolution is `stdTensorComplex G R`. -/
noncomputable def tensorRight_barResolution_iso (R : Rep.{0} SSGRoute.PTExt.Coeff G) :
    ((tensorRight R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      ((Rep.barResolution SSGRoute.PTExt.Coeff G).complex) ≅ stdTensorComplex G R := by
  refine HomologicalComplex.Hom.isoOfComponents (fun n => Iso.refl _) ?_
  intro i j hij
  obtain rfl : i = j + 1 := hij.symm
  simp [stdTensorComplex_d]

lemma tensorRight_barResolution_iso_hom_f_zero (R : Rep.{0} SSGRoute.PTExt.Coeff G) :
    (tensorRight_barResolution_iso G R).hom.f 0 = 𝟙 _ := rfl

lemma whisker_f_zero (R : Rep.{0} SSGRoute.PTExt.Coeff G) :
    (((tensorRight R).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (Rep.barResolution SSGRoute.PTExt.Coeff G).π).f 0 =
      (Rep.barResolution SSGRoute.PTExt.Coeff G).π.f 0 ▷ R := rfl

lemma isZero_tensor_zero (X : Rep.{0} SSGRoute.PTExt.Coeff G) :
    IsZero ((0 : Rep.{0} SSGRoute.PTExt.Coeff G) ⊗ X) := by
  rw [IsZero.iff_id_eq_zero, ← MonoidalCategory.id_tensorHom_id]
  have h : (𝟙 (0 : Rep.{0} SSGRoute.PTExt.Coeff G)) = 0 := IsZero.eq_of_src (isZero_zero _) _ _
  rw [h, MonoidalPreadditive.zero_tensor]

/-- The canonical identification `((single₀ C).obj 𝟙_C) ⊗ R ≅ (single₀ C).obj R`: this is the
unitor in degree `0` and the (unique) isomorphism between zero objects in positive degrees. -/
noncomputable def single₀TensorIso (R : Rep.{0} SSGRoute.PTExt.Coeff G) :
    ((tensorRight R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      ((ChainComplex.single₀ (Rep.{0} SSGRoute.PTExt.Coeff G)).obj
        (𝟙_ (Rep.{0} SSGRoute.PTExt.Coeff G))) ≅
      (ChainComplex.single₀ (Rep.{0} SSGRoute.PTExt.Coeff G)).obj R := by
  refine HomologicalComplex.Hom.isoOfComponents (fun n => ?_) ?_
  · rcases n with _ | k
    · exact asIso (eqToHom (by rfl : (((ChainComplex.single₀ (Rep.{0} SSGRoute.PTExt.Coeff G)).obj
        (𝟙_ (Rep.{0} SSGRoute.PTExt.Coeff G))).X 0) = 𝟙_ (Rep.{0} SSGRoute.PTExt.Coeff G)) ▷ R ≫
        (λ_ R).hom)
    · exact IsZero.iso (isZero_tensor_zero G R) (isZero_zero _)
  · intro i j hij
    rcases i with _ | i <;> rcases j with _ | j
    all_goals simp [HomologicalComplex.single_obj_d, Functor.mapHomologicalComplex_obj_d]

lemma single₀TensorIso_hom_f_zero (R : Rep.{0} SSGRoute.PTExt.Coeff G) :
    (single₀TensorIso G R).hom.f 0 =
      (eqToHom (by rfl : (((ChainComplex.single₀ (Rep.{0} SSGRoute.PTExt.Coeff G)).obj
        (𝟙_ (Rep.{0} SSGRoute.PTExt.Coeff G))).X 0) = 𝟙_ (Rep.{0} SSGRoute.PTExt.Coeff G))) ▷ R ≫
        (λ_ R).hom := rfl

/-- `stdTensorAug` is the whiskered augmentation followed by the canonical identification
`ℤ ⊗ R ≅ R`. -/
lemma stdTensorAug_eq (R : Rep.{0} SSGRoute.PTExt.Coeff G) :
    (tensorRight_barResolution_iso G R).hom ≫ stdTensorAug G R =
      ((tensorRight R).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (Rep.barResolution SSGRoute.PTExt.Coeff G).π ≫ (single₀TensorIso G R).hom := by
  apply (ChainComplex.toSingle₀Equiv (((tensorRight R).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj ((Rep.barResolution SSGRoute.PTExt.Coeff G).complex)) R).injective
  apply Subtype.ext
  simp only [ChainComplex.toSingle₀Equiv_apply_coe, HomologicalComplex.comp_f]
  rw [stdTensorAug_f_zero, tensorRight_barResolution_iso_hom_f_zero, whisker_f_zero,
    single₀TensorIso_hom_f_zero]
  simp only [Category.id_comp, Category.assoc]

/-- Forgetful functors are monoidal for the levelwise tensor product: the `stdTensorAugPhi`-image of the map
`π ▷ R` is the map `stdTensorAugPhi π` tensored with `stdTensorAugPhi R`. -/
lemma Phi_whisker_eq (R : Rep.{0} SSGRoute.PTExt.Coeff G) :
    ((stdTensorAugPhi G).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (((tensorRight R).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (Rep.barResolution SSGRoute.PTExt.Coeff G).π) =
      ((tensorRight ((stdTensorAugPhi G).obj R)).mapHomologicalComplex (ComplexShape.down ℕ)).map
        ((stdTensorAugPhi G).mapHomologicalComplex (ComplexShape.down ℕ) |>.map
          (Rep.barResolution SSGRoute.PTExt.Coeff G).π) := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [Functor.mapHomologicalComplex_map_f]
  rfl

/-- The main quasi-isomorphism: whiskering the bar resolution augmentation with a flat
representation `R` gives a quasi-isomorphism. -/
theorem quasiIso_whisker (R : Rep.{0} SSGRoute.PTExt.Coeff G) [Module.Free ℤ R.V] :
    QuasiIso (((tensorRight R).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (Rep.barResolution SSGRoute.PTExt.Coeff G).π) := by
  haveI hflat : Module.Flat SSGRoute.PTExt.Coeff ((stdTensorAugPhi G).obj R) := rep_flat_coeff G R
  have : PreservesFiniteLimits (tensorRight ((stdTensorAugPhi G).obj R)) := inferInstance
  have : PreservesFiniteColimits (tensorRight ((stdTensorAugPhi G).obj R)) := inferInstance
  have : (tensorRight ((stdTensorAugPhi G).obj R)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  have h1 : QuasiIso (((tensorRight ((stdTensorAugPhi G).obj R)).mapHomologicalComplex
      (ComplexShape.down ℕ)).map ((stdTensorAugPhi G).mapHomologicalComplex (ComplexShape.down ℕ) |>.map
        (Rep.barResolution SSGRoute.PTExt.Coeff G).π)) := inferInstance
  have h2 : QuasiIso (((stdTensorAugPhi G).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (((tensorRight R).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (Rep.barResolution SSGRoute.PTExt.Coeff G).π)) := by
    rw [Phi_whisker_eq G R]
    exact h1
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ (stdTensorAugPhi G)).mp h2

theorem stdTensorAug_quasiIso (G : Type) [Group G] (R : Rep.{0} SSGRoute.PTExt.Coeff G)
    [Module.Free ℤ R.V] [Module.Finite ℤ R.V] :
    QuasiIso (stdTensorAug G R) := by
  have hπ : QuasiIso (((tensorRight R).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (Rep.barResolution SSGRoute.PTExt.Coeff G).π) := quasiIso_whisker G R
  have hcomp : QuasiIso ((tensorRight_barResolution_iso G R).inv ≫
      (((tensorRight R).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (Rep.barResolution SSGRoute.PTExt.Coeff G).π)) :=
    (quasiIso_iff_comp_left _ _).mpr hπ
  have hw : QuasiIso ((((tensorRight R).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (Rep.barResolution SSGRoute.PTExt.Coeff G).π) ≫ (single₀TensorIso G R).hom) :=
    (quasiIso_iff_comp_right _ _).mpr hπ
  have hcomp' : QuasiIso ((tensorRight_barResolution_iso G R).inv ≫
      (((tensorRight R).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (Rep.barResolution SSGRoute.PTExt.Coeff G).π) ≫ (single₀TensorIso G R).hom) :=
    (quasiIso_iff_comp_left _ _).mpr hw
  have heq : (tensorRight_barResolution_iso G R).inv ≫
      (((tensorRight R).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (Rep.barResolution SSGRoute.PTExt.Coeff G).π) ≫ (single₀TensorIso G R).hom =
      stdTensorAug G R := by
    rw [← stdTensorAug_eq G R, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rwa [heq] at hcomp'

end

end Work.SSGRoute
