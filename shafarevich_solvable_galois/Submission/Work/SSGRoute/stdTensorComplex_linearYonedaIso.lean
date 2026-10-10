import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.Resolution
import Submission.Work.SSGRoute.ext2_iso_cohomology_defs

/-!
# The `Hom`-complex of the resolution `barResolution.complex ⊗ R`

For a commutative ring `k`, a group `G` and representations `R X : Rep k G`, the complex
`stdTensorComplex k G R` (the bar resolution of the trivial module tensored with `R`) has terms
`C_n ⊗ R`, where `C_n` is the `n`-th term of the bar resolution.  Levelwise the tensor–hom
adjunction of the closed monoidal structure on `Rep k G` gives isomorphisms

`Hom_G(C_n ⊗ R, X) ≅ Hom_G(C_n, R ⟹ X)`,

where `R ⟹ X = (Rep.ihom R).obj X` is the internal hom.  This file shows that these levelwise
bijections assemble into an isomorphism of cochain complexes

`(stdTensorComplex k G R).linearYonedaObj k X ≅
  (barResolution.complex).linearYonedaObj k ((Rep.ihom R).obj X)`.

The only input beyond the currying equivalence is the naturality of the currying
`(A ⊗ B ⟶ C) ≃ (A ⟶ B ⟹ C)` in the variable `A`, proved here by an explicit elementwise
computation (`linearHomEquivComm_whiskerRight_comp`).

## Main results

* `Work.SSGRoute.tensorComplex`: the levelwise tensor complex `K ⊗ R` of a chain complex of
  representations with a representation `R`.
* `Work.SSGRoute.tensorComplex_linearYonedaIso`: the general statement, for an arbitrary chain
  complex `K` and its levelwise tensor `tensorComplex K R` with `R`.
* `Work.SSGRoute.stdTensorComplex_linearYonedaIso`: the statement for the bar resolution.
-/

open CategoryTheory MonoidalCategory

namespace Work.SSGRoute

noncomputable section

variable {k : Type} [CommRing k] {G : Type} [Group G]

/-- The "levelwise tensor" complex `K ⊗ R`: the complex with terms `K.X n ⊗ R` and differentials
`K.d (n + 1) n ▷ R`.  For `K` the bar complex this is `stdTensorComplex`. -/
noncomputable def tensorComplex (K : ChainComplex (Rep.{0} k G) ℕ) (R : Rep.{0} k G) :
    ChainComplex (Rep.{0} k G) ℕ :=
  ChainComplex.of (fun n => K.X n ⊗ R) (fun n => K.d (n + 1) n ▷ R) (fun n => by
    rw [← MonoidalCategory.comp_whiskerRight, K.d_comp_d,
      MonoidalPreadditive.zero_whiskerRight])

@[simp] lemma tensorComplex_X (K : ChainComplex (Rep.{0} k G) ℕ) (R : Rep.{0} k G) (n : ℕ) :
    (tensorComplex K R).X n = K.X n ⊗ R := rfl

@[simp] lemma tensorComplex_d (K : ChainComplex (Rep.{0} k G) ℕ) (R : Rep.{0} k G) (n : ℕ) :
    (tensorComplex K R).d (n + 1) n = K.d (n + 1) n ▷ R := by
  simp [tensorComplex]

variable {A A' B C : Rep.{0} k G}

/-- **Naturality of the tensor–hom currying in the first variable**: composing with `f ▷ B` before
currying is the same as composing with `f` after currying. -/
lemma linearHomEquivComm_whiskerRight_comp (f : A' ⟶ A) (g : A ⊗ B ⟶ C) :
    Rep.MonoidalClosed.linearHomEquivComm A' B C ((f ▷ B) ≫ g) =
      f ≫ Rep.MonoidalClosed.linearHomEquivComm A B C g := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  rw [Rep.hom_comp_toLinearMap, Rep.MonoidalClosed.linearHomEquivComm_hom,
    Rep.MonoidalClosed.linearHomEquivComm_hom]
  ext a' b
  simp only [LinearMap.comp_apply, TensorProduct.curry_apply, Rep.hom_comp_toLinearMap,
    Rep.hom_whiskerRight]
  change (Rep.Hom.hom g).toLinearMap
      (LinearMap.rTensor (↑B) (Rep.Hom.hom f).toLinearMap (a' ⊗ₜ[k] b))
    = TensorProduct.curry (Rep.Hom.hom g).toLinearMap ((Rep.Hom.hom f).toLinearMap a') b
  rw [LinearMap.rTensor_tmul, TensorProduct.curry_apply]

/-- The differential of `Hom(K_•, Y)` is precomposition with the differential of `K`. -/
lemma linearYonedaObj_d_apply_precomp (K : ChainComplex (Rep.{0} k G) ℕ) (Y : Rep.{0} k G)
    {i j : ℕ} (hij : i + 1 = j) (f : K.X i ⟶ Y) :
    (K.linearYonedaObj k Y).d i j f = (K.d j i) ≫ f := by
  subst hij
  rfl

set_option backward.isDefEq.respectTransparency false

/-- **The comparison isomorphism of complexes.**  For any chain complex `K` of representations
and representations `R`, `X` there is an isomorphism of cochain complexes
`Hom(K ⊗ R, X) ≅ Hom(K, R ⟹ X)` given degreewise by currying (the tensor–hom adjunction). -/
theorem tensorComplex_linearYonedaIso (K : ChainComplex (Rep.{0} k G) ℕ) (R X : Rep.{0} k G) :
    Nonempty ((tensorComplex K R).linearYonedaObj k X ≅
      K.linearYonedaObj k ((Rep.ihom R).obj X)) := by
  refine ⟨HomologicalComplex.Hom.isoOfComponents
    (fun n => (Rep.MonoidalClosed.linearHomEquivComm (K.X n) R X).toModuleIso) ?_⟩
  intro i j hij
  rw [ComplexShape.up_Rel] at hij
  subst hij
  apply ModuleCat.hom_ext
  ext g
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.toModuleIso_hom, LinearEquiv.toModuleIso_hom,
    ModuleCat.hom_ofHom, ModuleCat.hom_ofHom]
  rw [ChainComplex.linearYonedaObj_d, ChainComplex.linearYonedaObj_d,
    ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, tensorComplex_d]
  change (K.d (i + 1) i) ≫ (Rep.MonoidalClosed.linearHomEquivComm (K.X i) R X) g
    = (Rep.MonoidalClosed.linearHomEquivComm (K.X (i + 1)) R X) ((K.d (i + 1) i ▷ R) ≫ g)
  exact (linearHomEquivComm_whiskerRight_comp (K.d (i + 1) i) g).symm

/-- `stdTensorComplex` is the levelwise tensor of the bar complex with `R`. -/
lemma stdTensorComplex_eq_tensorComplex (G : Type) [Group G]
    (R : Rep.{0} SSGRoute.PTExt.Coeff G) :
    stdTensorComplex G R = tensorComplex ((Rep.barResolution SSGRoute.PTExt.Coeff G).complex) R :=
  rfl

/-- The comparison isomorphism for the resolution `stdTensorComplex` used to compute
`Ext²_G(R, X)`: its `Hom`-complex is the bar complex of `X` twisted by the internal hom `R ⟹ -`. -/
theorem stdTensorComplex_linearYonedaIso (G : Type) [Group G]
    (R X : Rep.{0} SSGRoute.PTExt.Coeff G) :
    Nonempty ((stdTensorComplex G R).linearYonedaObj SSGRoute.PTExt.Coeff X ≅
      (Rep.barResolution SSGRoute.PTExt.Coeff G).complex.linearYonedaObj SSGRoute.PTExt.Coeff
        ((Rep.ihom R).obj X)) := by
  rw [stdTensorComplex_eq_tensorComplex G R]
  exact tensorComplex_linearYonedaIso _ R X

end

end Work.SSGRoute
