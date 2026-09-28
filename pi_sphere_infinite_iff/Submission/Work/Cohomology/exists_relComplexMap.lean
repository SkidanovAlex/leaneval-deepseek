import Mathlib
import Submission.Work.Cohomology.RelCupTransfer
import Submission.Work.Cohomology.Pullback

/-!
# Functoriality of the relative singular cochain complex

For a continuous map `f : X₁ ⟶ X₂` of topological spaces and subsets `A₁ ⊆ X₁`, `A₂ ⊆ X₂`
satisfying `f '' A₁ ⊆ A₂`, the pair map `(X₁, A₁) → (X₂, A₂)` induces a cochain map of relative
singular cochain complexes

`φ : C^*(X₂, A₂) ⟶ C^*(X₁, A₁)`

which is compatible with the inclusions `relIncl` of the relative into the absolute complexes:

`φ ≫ relIncl X₁ A₁ = relIncl X₂ A₂ ≫ dualChainMap f`.

Degreewise, `φ` is the map induced by `dualChainMap f` on the kernels of the restriction maps
`restr X₂ A₂` and `restr X₁ A₁`; the hypothesis `f '' A₁ ⊆ A₂` is exactly what makes the
pullback send cochains vanishing on `A₂` to cochains vanishing on `A₁`.  This is the
"contravariant functoriality of the pair `(X, A)`" statement used to compare relative cohomology
classes along a map of pairs.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R]

/-! ## The induced map of pairs and the compatibility with the restriction -/

/-- The map of pairs `(X₁, A₁) → (X₂, A₂)` induced by a continuous map `f` sending `A₁` into `A₂`,
as a continuous map `TopCat.of A₁ ⟶ TopCat.of A₂` on the subspaces. -/
def relMapSub {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) : TopCat.of A₁ ⟶ TopCat.of A₂ :=
  TopCat.ofHom ⟨fun a => ⟨f a, h a a.2⟩,
    Continuous.subtype_mk ((ConcreteCategory.hom f).continuous_toFun.comp continuous_subtype_val)
      (fun a => h a a.2)⟩

/-- The restriction of `f` to the subspaces is the map of pairs. -/
lemma relMapSub_spec {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) :
    subtypeIncl X₁ A₁ ≫ f = relMapSub A₁ A₂ f h ≫ subtypeIncl X₂ A₂ := by
  apply TopCat.ext; intro a; rfl

/-- The pullback `dualChainMap f` intertwines the two restriction maps via the induced map of
pairs: `dualChainMap f ≫ restr X₁ A₁ = restr X₂ A₂ ≫ dualChainMap (relMapSub …)`. -/
lemma dualChainMap_restr_comp {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) :
    dualChainMap R X₁ X₂ f ≫ restr R X₁ A₁ =
      restr R X₂ A₂ ≫ dualChainMap R (TopCat.of A₁) (TopCat.of A₂) (relMapSub A₁ A₂ f h) := by
  rw [restr, restr]
  rw [← dualChainMap_comp, relMapSub_spec, dualChainMap_comp]

/-- A cochain vanishing on `A₂` pulls back along `f` to a cochain vanishing on `A₁`. -/
lemma relKern_map_mem {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) (n : ℕ) (x : relKern R X₂ A₂ n) :
    ((dualChainMap R X₁ X₂ f).f n).hom x.1 ∈ relKern R X₁ A₁ n := by
  rw [relKern, LinearMap.mem_ker]
  have hcomp := congrArg (fun φ => φ.f n) (dualChainMap_restr_comp R A₁ A₂ f h)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f] at hcomp
  have h2 := congrArg ModuleCat.Hom.hom hcomp
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h2
  have h3 := LinearMap.congr_fun h2 x.1
  simp only [LinearMap.comp_apply] at h3
  have hx : ((restr R X₂ A₂).f n).hom x.1 = 0 := x.2
  rw [hx, map_zero] at h3
  exact h3

/-! ## The induced cochain map of relative complexes -/

/-- The `n`-th component of the induced map of relative complexes: the restriction of the
pullback `dualChainMap f` to the kernel of the restriction map. -/
def relMapLM {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) (n : ℕ) :
    relKern R X₂ A₂ n →ₗ[R] relKern R X₁ A₁ n where
  toFun x := ⟨((dualChainMap R X₁ X₂ f).f n).hom x.1, relKern_map_mem R A₁ A₂ f h n x⟩
  map_add' x y := by apply Subtype.ext; simp
  map_smul' c x := by apply Subtype.ext; simp

/-- The underlying cochain of `relMapLM` is the pullback. -/
lemma relMapLM_coe {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) (n : ℕ) (x : relKern R X₂ A₂ n) :
    (relMapLM R A₁ A₂ f h n x).1 = ((dualChainMap R X₁ X₂ f).f n).hom x.1 := rfl

/-- The cochain map of relative complexes `C^*(X₂, A₂) ⟶ C^*(X₁, A₁)` induced by a pair map
`(X₁, A₁) → (X₂, A₂)`. -/
def relComplexMap {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) :
    relComplex R X₂ A₂ ⟶ relComplex R X₁ A₁ :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (relMapLM R A₁ A₂ f h n)) (fun n => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom, relComplex_d]
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      ((dualChainMap R X₁ X₂ f).comm n (n+1))) x.1)

/-- The `n`-th component of `relComplexMap`. -/
lemma relComplexMap_f {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) (n : ℕ) :
    (relComplexMap R A₁ A₂ f h).f n = ModuleCat.ofHom (relMapLM R A₁ A₂ f h n) := rfl

/-- **The relative cochain complex is contravariantly functorial in the pair.**  A continuous map
`f : X₁ ⟶ X₂` with `f '' A₁ ⊆ A₂` induces a cochain map `C^*(X₂, A₂) ⟶ C^*(X₁, A₁)` compatible
with the inclusions into the absolute complexes. -/
theorem exists_relComplexMap (R : Type) [CommRing R] {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂)
    (f : X₁ ⟶ X₂) (h : ∀ x ∈ A₁, f x ∈ A₂) :
    ∃ (φ : Work.Cohomology.relComplex R X₂ A₂ ⟶ Work.Cohomology.relComplex R X₁ A₁),
      CategoryTheory.CategoryStruct.comp φ (Work.Cohomology.relIncl R X₁ A₁) =
        CategoryTheory.CategoryStruct.comp (Work.Cohomology.relIncl R X₂ A₂)
          (Work.Cohomology.dualChainMap R X₁ X₂ f) := by
  refine ⟨relComplexMap R A₁ A₂ f h, ?_⟩
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, relComplexMap_f, relIncl_f, relIncl_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
  exact relMapLM_coe R A₁ A₂ f h n x

end

end Work.Cohomology
