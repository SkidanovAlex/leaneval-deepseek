import Mathlib
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.Pullback
import Submission.Work.Cohomology.Singular

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The short exact sequence of relative singular cochains

For a topological space `X` and a subset `A ⊆ X`, this file constructs the **relative singular
cochain complex** `C^*(X, A)` as a cochain complex of `R`-modules together with an inclusion
`ι : C^*(X,A) ⟶ C^*(X)` into the singular cochain complex of `X`, such that on every degree

`0 ⟶ C^n(X,A) ⟶ C^n(X) ⟶ C^n(A) ⟶ 0`

is a short exact sequence.  Here the map `C^n(X) ⟶ C^n(A)` is the restriction (pullback) map
`Work.Cohomology.dualChainMap R (TopCat.of A) X (subtype inclusion)`, so the statement combines

* `ι ≫ (restriction) = 0` (the composite is the zero cochain map),
* `ι.f n` injective,
* the restriction `(dualChainMap …).f n` surjective — the extension of a cochain on `A` to one on
  `X` (a singular simplex either lies in `A`, in which case evaluate, or it does not, in which case
  return `0`),
* `range (ι.f n) = ker ((dualChainMap …).f n)`.

The relative complex is of course the degreewise kernel of the restriction map, with the
differentials induced from those of `C^*(X)`: because the restriction is a cochain map, the
differential of `C^*(X)` preserves the kernels.

The surjectivity is proved by exhibiting a **splitting** of the underlying chain map
`C_*(A) ⟶ C_*(X)`: since singular chains are free on the singular simplices and the inclusion
`A ↪ X` is injective on simplices, the induced map on chains is a coproduct inclusion, hence a split
monomorphism, hence its transpose is a split (in particular surjective) epimorphism.  The splitting
`chainRetract` is built from the explicit coproduct presentation of singular chains
(`SSet.isColimitChainComplexXCofan`).
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R]

/-! ## The inclusion of a subspace and its effect on singular simplicial sets -/

/-- The inclusion `A ⊆ X` of a subset, as a morphism of topological spaces. -/
def subtypeIncl (X : TopCat) (A : Set X) : TopCat.of A ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The restriction (pullback) map on singular cochains induced by the inclusion `A ⊆ X`. -/
def restr (X : TopCat) (A : Set X) :
    singularCochainComplex R X ⟶ singularCochainComplex R (TopCat.of A) :=
  dualChainMap R (TopCat.of A) X (subtypeIncl X A)

/-- The `n`-simplices of the singular simplicial set are continuous maps out of the standard
simplex; the identification `TopCat.toSSetObjEquiv` is natural in the space. -/
lemma toSSetObjEquiv_naturality_space {X Y : TopCat} (f : X ⟶ Y) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    (TopCat.toSSetObjEquiv Y (Opposite.op (SimplexCategory.mk n)))
        ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk n)) σ)
      = (ConcreteCategory.hom f).comp
          ((TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n))) σ) := rfl

/-- A degreewise injective continuous map induces a degreewise injective map of singular
simplicial sets. -/
lemma injective_toSSet_map {X Y : TopCat} (f : X ⟶ Y)
    (hf : Function.Injective (ConcreteCategory.hom f)) (n : ℕ) :
    Function.Injective ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk n))) := by
  intro σ τ h
  apply (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n))).injective
  apply ContinuousMap.ext
  intro z
  apply hf
  have h2 := congrArg (fun g : C(Convexity.StdSimplex ℝ (Fin (n+1)), Y) => g z)
    (congrArg (TopCat.toSSetObjEquiv Y (Opposite.op (SimplexCategory.mk n))) h)
  rw [toSSetObjEquiv_naturality_space, toSSetObjEquiv_naturality_space] at h2
  simpa only [ContinuousMap.comp_apply] using h2

/-- The underlying map of the subspace inclusion is injective. -/
lemma subtypeIncl_injective (X : TopCat) (A : Set X) :
    Function.Injective (ConcreteCategory.hom (subtypeIncl X A)) :=
  fun _ _ h => Subtype.ext h

/-! ## A splitting of the chain map `C_*(A) ⟶ C_*(X)`

Singular `n`-chains are the coproduct of one copy of `R` per singular `n`-simplex
(`SSet.isColimitChainComplexXCofan`), and the inclusion `A ⊆ X` is injective on simplices.  Hence
the induced map on chains sends the coproduct inclusion to a coproduct inclusion and admits a
retraction: a singular simplex of `X` that comes from `A` is sent back to (the unique) simplex it
comes from, and every other simplex is sent to `0`. -/

/-- The retraction of the chain map induced by the inclusion `A ⊆ X`: on the summand of a singular
simplex `y` of `X` lying in the image of `A`'s simplices, it is the (unique) simplex of `A` mapping
to `y`; on all other summands it is zero. -/
def chainRetract (X : TopCat) (A : Set X) (n : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).X n ⟶
    ((TopCat.toSSet.obj (TopCat.of A)).chainComplex (ModuleCat.of R R)).X n := by
  classical
  exact ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of R R) n).desc
    (Cofan.mk (((TopCat.toSSet.obj (TopCat.of A)).chainComplex (ModuleCat.of R R)).X n)
      (fun y => if hy : ∃ x, (TopCat.toSSet.map (subtypeIncl X A)).app
              (Opposite.op (SimplexCategory.mk n)) x = y
                then (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex (Classical.choose hy)
                else 0))

/-- `chainRetract` is a retraction of the chain map induced by the inclusion `A ⊆ X`. -/
theorem chainRetract_spec (X : TopCat) (A : Set X) (n : ℕ) :
    (SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A)) (ModuleCat.of R R)).f n
      ≫ chainRetract R X A n = 𝟙 _ := by
  classical
  apply SSet.chainComplex_hom_ext
  intro x
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, Category.comp_id]
  rw [chainRetract]
  refine (Cofan.IsColimit.fac ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of R R) n)
      (fun y => if hy : ∃ x', (TopCat.toSSet.map (subtypeIncl X A)).app
              (Opposite.op (SimplexCategory.mk n)) x' = y
                then (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex (Classical.choose hy)
                else 0)
      ((TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op (SimplexCategory.mk n)) x)).trans ?_
  have hy : ∃ x', (TopCat.toSSet.map (subtypeIncl X A)).app
        (Opposite.op (SimplexCategory.mk n)) x' =
      (TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op (SimplexCategory.mk n)) x := ⟨x, rfl⟩
  rw [dif_pos hy]
  congr 1
  exact (injective_toSSet_map (subtypeIncl X A) (subtypeIncl_injective X A) n)
    (Classical.choose_spec hy)

/-- If `g ≫ s = 𝟙` then the transpose `gᵛ` of `g` is surjective: a functional of the source of `g`
extends by `s` to a functional of the target of `g`. -/
lemma surjective_dualMap_of_split {M N : ModuleCat R} (f : M ⟶ N) (s : N ⟶ M)
    (h : f ≫ s = 𝟙 M) : Function.Surjective f.hom.dualMap := by
  intro ψ
  refine ⟨ψ.comp s.hom, ?_⟩
  have hcomp : s.hom.comp f.hom = LinearMap.id := by
    have hh := congrArg ModuleCat.Hom.hom h
    rwa [ModuleCat.hom_comp, ModuleCat.hom_id] at hh
  have hsf : ∀ x : M, s.hom (f.hom x) = x := by
    intro x
    have h2 := LinearMap.congr_fun hcomp x
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h2
  apply LinearMap.ext
  intro x
  simp only [LinearMap.dualMap_apply, LinearMap.comp_apply, hsf]

/-- The `n`-th component of `dualChainMap` is the transpose of the `n`-th component of `chainMap`. -/
lemma dualChainMap_f_hom (X Y : TopCat) (f : X ⟶ Y) (n : ℕ) :
    ((dualChainMap R X Y f).f n).hom = ((chainMap R X Y f).f n).hom.dualMap := rfl

/-- `chainMap` is the chain map induced by the corresponding map of singular simplicial sets. -/
lemma chainMap_f_eq (X Y : TopCat) (f : X ⟶ Y) (n : ℕ) :
    (chainMap R X Y f).f n =
      (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R)).f n := rfl

/-- The restriction map on singular `n`-cochains of the poset of `R`-valued functions on
`n`-chains is surjective (at the level of simplicial sets). -/
lemma surjective_restr_sset (X : TopCat) (A : Set X) (n : ℕ) :
    Function.Surjective
      ((SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A))
        (ModuleCat.of R R)).f n).hom.dualMap :=
  surjective_dualMap_of_split R _ _ (chainRetract_spec R X A n)

/-- **The restriction of singular cochains is surjective**: every singular `n`-cochain on `A`
extends to one on `X`. -/
theorem surjective_restr (X : TopCat) (A : Set X) (n : ℕ) :
    Function.Surjective (((restr R X A).f n).hom) := by
  rw [restr, dualChainMap_f_hom, chainMap_f_eq]
  exact surjective_restr_sset R X A n

/-! ## The relative cochain complex

On degree `n` the relative cochains are the kernel of the restriction `C^n(X) ⟶ C^n(A)`.  Since the
restriction is a cochain map, the differential of `C^*(X)` restricts to the kernels, giving a
subcomplex `C^*(X,A)` together with its inclusion into `C^*(X)`. -/

/-- The relative `n`-cochains `C^n(X,A)`: the kernel of the restriction `C^n(X) ⟶ C^n(A)`. -/
def relKern (X : TopCat) (A : Set X) (n : ℕ) :
    Submodule R ((singularCochainComplex R X).X n) :=
  LinearMap.ker (((restr R X A).f n).hom)

/-- The differential of the relative cochain complex: the restriction of the differential of
`C^*(X)` to the kernels. -/
def relDiffLM (X : TopCat) (A : Set X) (n : ℕ) :
    (relKern R X A n) →ₗ[R] (relKern R X A (n+1)) :=
  (((singularCochainComplex R X).d n (n+1)).hom.comp
      (Submodule.subtype (relKern R X A n))).codRestrict (relKern R X A (n+1))
    (fun x => by
      rw [relKern, LinearMap.mem_ker]
      have hx0 : ((restr R X A).f n).hom x.1 = 0 := x.2
      have hc := congrArg ModuleCat.Hom.hom ((restr R X A).comm n (n+1))
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hc
      have hcx := LinearMap.congr_fun hc x.1
      simp only [LinearMap.comp_apply] at hcx
      simp only [hx0, map_zero] at hcx
      exact hcx.symm)

/-- The underlying element of `relDiffLM`. -/
@[simp] lemma relDiffLM_coe (X : TopCat) (A : Set X) (n : ℕ) (x : relKern R X A n) :
    (relDiffLM R X A n x).1 = ((singularCochainComplex R X).d n (n+1)).hom x.1 :=
  rfl

/-- The differential of the relative cochain complex, as a morphism of modules. -/
def relDiff (X : TopCat) (A : Set X) (n : ℕ) :
    ModuleCat.of R (relKern R X A n) ⟶ ModuleCat.of R (relKern R X A (n+1)) :=
  ModuleCat.ofHom (relDiffLM R X A n)

/-- **The relative singular cochain complex** `C^*(X,A)`: the subcomplex of `C^*(X)` consisting of
the cochains vanishing on chains lying in `A`. -/
def relComplex (X : TopCat) (A : Set X) : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (relKern R X A n)) (fun n => relDiff R X A n)
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply,
        Submodule.coe_zero]
      show ((relDiffLM R X A (n+1)) ((relDiffLM R X A n) x)).1 = 0
      rw [relDiffLM_coe, relDiffLM_coe]
      have h := congrArg ModuleCat.Hom.hom
        (HomologicalComplex.d_comp_d (singularCochainComplex R X) n (n+1) (n+2))
      rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
      have h2 := LinearMap.congr_fun h x.1
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h2
      exact h2)

/-- The differential of the relative complex is `relDiff`. -/
@[simp] lemma relComplex_d (X : TopCat) (A : Set X) (n : ℕ) :
    (relComplex R X A).d n (n+1) = relDiff R X A n :=
  CochainComplex.of_d (fun n => ModuleCat.of R (relKern R X A n)) (fun n => relDiff R X A n) n

/-- The inclusion `C^*(X,A) ⟶ C^*(X)` of the relative cochain complex. -/
def relIncl (X : TopCat) (A : Set X) :
    relComplex R X A ⟶ singularCochainComplex R X :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (Submodule.subtype (relKern R X A n)))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
        relComplex_d]
      change ((singularCochainComplex R X).d n (n+1)).hom x.1 = ((relDiffLM R X A n) x).1
      rw [relDiffLM_coe])

/-- The `n`-th component of `relIncl` is the inclusion of the kernel submodule. -/
@[simp] lemma relIncl_f (X : TopCat) (A : Set X) (n : ℕ) :
    (relIncl R X A).f n = ModuleCat.ofHom (Submodule.subtype (relKern R X A n)) := rfl

end

/-! ## The short exact sequence -/

theorem relCochain_shortExact (R : Type) [CommRing R] (X : TopCat) (A : Set X) :
    ∃ (Crel : CochainComplex (ModuleCat R) ℕ)
      (ι : Crel ⟶ singularCochainComplex R X),
      CategoryTheory.CategoryStruct.comp ι
        (dualChainMap R (TopCat.of A) X
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)) = 0 ∧
      (∀ n, Function.Injective (ι.f n).hom) ∧
      (∀ n, Function.Surjective
        ((dualChainMap R (TopCat.of A) X
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)).f n).hom) ∧
      (∀ n, LinearMap.range (ι.f n).hom =
        LinearMap.ker ((dualChainMap R (TopCat.of A) X
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)).f n).hom) := by
  refine ⟨relComplex R X A, relIncl R X A, ?_, ?_, ?_, ?_⟩
  · apply HomologicalComplex.hom_ext
    intro n
    rw [HomologicalComplex.comp_f]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, HomologicalComplex.zero_f_apply,
      ModuleCat.hom_zero, LinearMap.zero_apply]
    change ((restr R X A).f n).hom x.1 = 0
    exact x.2
  · intro n
    exact fun a b h => Subtype.ext h
  · intro n
    exact surjective_restr R X A n
  · intro n
    rw [relIncl_f, ModuleCat.hom_ofHom]
    exact Submodule.range_subtype (relKern R X A n)

end Work.Cohomology
