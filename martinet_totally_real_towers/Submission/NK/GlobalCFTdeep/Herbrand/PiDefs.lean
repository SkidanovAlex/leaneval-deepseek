/-
Auxiliary definitions and lemmas for the proof that homology commutes with products
of cochain complexes of modules (used for `NK.GlobalCFTdeep.Herbrand.homology_prod_iso`).
-/

import Mathlib

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace LinearMap

variable {R : Type*} [Semiring R] {ι : Type} {M : ι → Type*}
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
variable {N : ι → Type*} [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
variable {D : ι → Type*} [∀ i, AddCommMonoid (D i)] [∀ i, Module R (D i)]

lemma ker_piMap (f : ∀ i, M i →ₗ[R] N i) :
    (LinearMap.piMap f).ker = Submodule.pi Set.univ (fun i => (f i).ker) := by
  rw [LinearMap.piMap, LinearMap.ker_pi]
  conv_rhs => rw [← Submodule.iInf_comap_proj]
  exact iInf_congr fun i => LinearMap.ker_comp (LinearMap.proj i) (f i)

lemma range_piMap (f : ∀ i, M i →ₗ[R] N i) :
    (LinearMap.piMap f).range = Submodule.pi Set.univ (fun i => (f i).range) := by
  ext x
  simp only [Submodule.mem_pi, Set.mem_univ, true_imp_iff, LinearMap.mem_range,
    LinearMap.coe_piMap]
  constructor
  · rintro ⟨y, hy⟩ i
    exact ⟨y i, congr_fun hy i⟩
  · intro h
    choose y hy using h
    exact ⟨y, funext hy⟩

lemma piMap_comp_eq_zero (f : ∀ i, M i →ₗ[R] N i) (g : ∀ i, N i →ₗ[R] D i)
    (h : ∀ i, g i ∘ₗ f i = 0) : (LinearMap.piMap g).comp (LinearMap.piMap f) = 0 := by
  ext x i
  simpa using LinearMap.congr_fun (h i) (x i)

end LinearMap

namespace Submodule

variable {R : Type*} [Semiring R] {ι : Type*} {M : ι → Type*}

/-- The product of a family of submodules is the product of the submodules. -/
noncomputable def piEquiv [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    (p : ∀ i, Submodule R (M i)) : (Submodule.pi Set.univ p) ≃ₗ[R] (∀ i, p i) where
  toFun x i := ⟨x.1 i, x.2 i trivial⟩
  map_add' _ _ := by ext i; rfl
  map_smul' _ _ := by ext i; rfl
  invFun y := ⟨fun i => (y i : M i), fun i _ => (y i).2⟩
  left_inv x := by ext i; rfl
  right_inv y := by ext i; rfl

end Submodule

/-- The quotient of a product by a product of submodules is the product of the quotients. -/
noncomputable def Submodule.quotientPiEquiv {R : Type*} [Ring R] {ι : Type*} {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (p : ∀ i, Submodule R (M i)) :
    ((∀ i, M i) ⧸ Submodule.pi Set.univ p) ≃ₗ[R] (∀ i, M i ⧸ p i) := by
  let Φ : (∀ i, M i) →ₗ[R] (∀ i, M i ⧸ p i) :=
    LinearMap.pi fun i => (p i).mkQ.comp (LinearMap.proj i)
  have hker : Φ.ker = Submodule.pi Set.univ p := by
    rw [show Φ = LinearMap.pi (fun i => (p i).mkQ.comp (LinearMap.proj i)) from rfl,
      LinearMap.ker_pi]
    conv_rhs => rw [← Submodule.iInf_comap_proj]
    exact iInf_congr fun i => by rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hsurj : Function.Surjective Φ := fun y => by
    choose x hx using fun i => Submodule.mkQ_surjective (p i) (y i)
    exact ⟨x, by funext i; simpa [Φ] using hx i⟩
  exact (Submodule.quotEquivOfEq _ _ hker).symm.trans (Φ.quotKerEquivOfSurjective hsurj)

namespace NK.GlobalCFTdeep.Herbrand

/-- Given linear maps `f i : A i → B i` and `g i : B i → D i` with `g i ∘ f i = 0`,
the product of the short complexes `A i → B i → D i`, in explicit form. -/
noncomputable abbrev piModuleCatMk {R : Type*} [Ring R] {ι : Type}
    {A B D : ι → Type}
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module R (B i)]
    [∀ i, AddCommGroup (D i)] [∀ i, Module R (D i)]
    (f : ∀ i, A i →ₗ[R] B i) (g : ∀ i, B i →ₗ[R] D i)
    (h : ∀ i, g i ∘ₗ f i = 0) : ShortComplex (ModuleCat R) :=
  CategoryTheory.ShortComplex.moduleCatMk (LinearMap.piMap f) (LinearMap.piMap g)
    (LinearMap.piMap_comp_eq_zero f g h)

namespace HomologicalComplex

variable {R : Type*} [Ring R] {ι : Type}

/-- The degreewise product of a family of cochain complexes. -/
noncomputable abbrev piX (C : ι → CochainComplex (ModuleCat R) ℤ) : ℤ → ModuleCat R :=
  fun n => ModuleCat.of R (∀ i, (C i).X n)

/-- The degreewise product of the differentials of a family of cochain complexes. -/
noncomputable abbrev piD (C : ι → CochainComplex (ModuleCat R) ℤ) (n m : ℤ) :
    piX C n ⟶ piX C m :=
  ModuleCat.ofHom (LinearMap.piMap (fun i => ((C i).d n m).hom))

/-- The product of a family of cochain complexes of `R`-modules, in explicit form. -/
noncomputable abbrev piCochainComplex (C : ι → CochainComplex (ModuleCat R) ℤ) :
    CochainComplex (ModuleCat R) ℤ where
  X := piX C
  d := piD C
  shape n m h := by
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_ofHom, ModuleCat.hom_zero]
    ext x i
    rw [LinearMap.zero_apply, Pi.zero_apply, LinearMap.coe_piMap, Pi.map_apply]
    exact LinearMap.congr_fun (congr_arg ModuleCat.Hom.hom (HomologicalComplex.shape (C i) n m h)) (x i)
  d_comp_d' n m k hnm hmk := by
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, ModuleCat.hom_zero]
    ext x i
    rw [LinearMap.zero_apply, Pi.zero_apply, LinearMap.comp_apply, LinearMap.coe_piMap, Pi.map_apply,
      LinearMap.coe_piMap, Pi.map_apply]
    have key := LinearMap.congr_fun (congr_arg ModuleCat.Hom.hom
      (HomologicalComplex.d_comp_d (C i) n m k)) (x i)
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at key
    exact key

/-- The projection from the degreewise product to one factor. -/
noncomputable abbrev piCochainComplexπ (C : ι → CochainComplex (ModuleCat R) ℤ) (i : ι) :
    piCochainComplex C ⟶ C i where
  f := fun n => ModuleCat.ofHom (LinearMap.proj i : (∀ j, (C j).X n) →ₗ[R] (C i).X n)
  comm' n m _ := by
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom]
    ext x
    simp only [piCochainComplex, piD, ModuleCat.hom_ofHom, LinearMap.comp_apply, LinearMap.coe_piMap,
      Pi.map_apply, LinearMap.proj_apply]

/-- The explicit product complex, exhibited as a product cone over the family. -/
noncomputable abbrev piCochainComplexFan (C : ι → CochainComplex (ModuleCat R) ℤ) : Fan C :=
  Fan.mk (piCochainComplex C) (piCochainComplexπ C)

/-- The explicit product complex is a product of the family in the category of cochain complexes. -/
noncomputable def piCochainComplexFan_isLimit (C : ι → CochainComplex (ModuleCat R) ℤ) :
    IsLimit (piCochainComplexFan C) :=
  HomologicalComplex.isLimitOfEval (Discrete.functor C) (piCochainComplexFan C) (fun n =>
    (isLimitMapConeFanMkEquiv (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n)
      C (piCochainComplexπ C)).symm
      (ModuleCat.productConeIsLimit (fun i => (C i).X n)))

/-- The explicit product complex is isomorphic to the categorical product. -/
noncomputable abbrev piCochainComplexIso (C : ι → CochainComplex (ModuleCat R) ℤ) :
    piCochainComplex C ≅ ∏ᶜ C :=
  IsLimit.conePointUniqueUpToIso (piCochainComplexFan_isLimit C)
    (limit.isLimit (Discrete.functor C))

end HomologicalComplex

end NK.GlobalCFTdeep.Herbrand
