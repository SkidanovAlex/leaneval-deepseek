import Mathlib
import Submission.Work.Cohomology.PairSequence
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Cohomology.exists_relComplexMap

/-!
# The cochain-level short exact sequence of a triple

For subsets `S ⊆ T ⊆ X` of a topological space, the relative cochain complexes fit in the short
exact sequence

`0 ⟶ C^*(X,T) ⟶ C^*(X,S) ⟶ C^*(T,S) ⟶ 0`

(first map: the inclusion of the cochains vanishing on `T` into those vanishing on `S`; second map:
restriction to `T`).  Its long exact sequence in cohomology is the long exact sequence of the
triple,

`⋯ ⟶ H^n(X,T) ⟶ H^n(X,S) ⟶ H^n(T,S) ⟶ H^{n+1}(X,T) ⟶ ⋯`.

This file contains the *definitions* and the elementary parts (the inclusion of the kernels and the
composite is zero); the short exactness and the exactness of the long exact sequence are proved in
`Submission/Work/Serre/TripleCohLES.lean`.
-/



open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section


variable (R : Type) [CommRing R]

/-! ## The inclusion `S → T` of subsets -/

/-- The inclusion `S → T` of subsets `S ⊆ T ⊆ X`, as a morphism of topological spaces. -/
def subIncl {X : TopCat} (S T : Set X) (hST : S ⊆ T) : TopCat.of S ⟶ TopCat.of T :=
  TopCat.ofHom ⟨fun x => ⟨x.1, hST x.2⟩,
    Continuous.subtype_mk continuous_subtype_val (fun x => hST x.2)⟩

/-- The inclusion `S → T` followed by `T ⊆ X` is the inclusion `S ⊆ X`. -/
theorem subIncl_subtypeIncl {X : TopCat} (S T : Set X) (hST : S ⊆ T) :
    subIncl S T hST ≫ Work.Cohomology.subtypeIncl X T = Work.Cohomology.subtypeIncl X S := by
  ext x
  rfl

/-! ## Functoriality of the singular chain map, over an arbitrary ring -/

/-- The singular chain map is functorial: `chainMap (f ≫ g) = chainMap f ≫ chainMap g`. -/
theorem chainMap_comp_gen {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Work.Cohomology.chainMap R X Y f ≫ Work.Cohomology.chainMap R Y Z g =
      Work.Cohomology.chainMap R X Z (f ≫ g) :=
  (CategoryTheory.Functor.map_comp _ _ _).symm

/-! ## The inclusion of the relative cochains -/

/-- **The relative `n`-cochains vanishing on `T` vanish on `S`**, for `S ⊆ T`. -/
theorem relKern_le (X : TopCat) (S T : Set X) (hST : S ⊆ T) (n : ℕ) :
    Work.Cohomology.relKern R X T n ≤ Work.Cohomology.relKern R X S n := by
  intro x hx
  rw [Work.Cohomology.relKern, LinearMap.mem_ker] at hx ⊢
  have hfact : Work.Cohomology.restr R X S
      = Work.Cohomology.restr R X T ≫
        Work.Cohomology.dualChainMap R (TopCat.of S) (TopCat.of T) (subIncl S T hST) := by
    rw [Work.Cohomology.restr, Work.Cohomology.restr, ← subIncl_subtypeIncl S T hST,
      Work.Cohomology.dualChainMap_comp]
  have hfactn : (Work.Cohomology.restr R X S).f n
      = (Work.Cohomology.restr R X T).f n ≫
        (Work.Cohomology.dualChainMap R (TopCat.of S) (TopCat.of T) (subIncl S T hST)).f n := by
    rw [hfact, HomologicalComplex.comp_f]
  rw [hfactn, ModuleCat.hom_comp, LinearMap.comp_apply, hx, map_zero]

/-- The `n`-th component of the inclusion `C^n(X,T) → C^n(X,S)` of relative cochains. -/
def tripleInclLM (X : TopCat) (S T : Set X) (hST : S ⊆ T) (n : ℕ) :
    Work.Cohomology.relKern R X T n →ₗ[R] Work.Cohomology.relKern R X S n :=
  (Submodule.subtype _).codRestrict _ (fun x => relKern_le R X S T hST n x.2)

@[simp] theorem tripleInclLM_coe (X : TopCat) (S T : Set X) (hST : S ⊆ T) (n : ℕ)
    (x : Work.Cohomology.relKern R X T n) :
    ((tripleInclLM R X S T hST n x : Work.Cohomology.relKern R X S n) :
      (Work.Cohomology.singularCochainComplex R X).X n) = x.1 := rfl

/-- The inclusion commutes with the differentials. -/
theorem relDiffLM_tripleInclLM (X : TopCat) (S T : Set X) (hST : S ⊆ T) (n : ℕ)
    (x : Work.Cohomology.relKern R X T n) :
    (tripleInclLM R X S T hST (n+1)) (Work.Cohomology.relDiffLM R X T n x)
      = (Work.Cohomology.relDiffLM R X S n) (tripleInclLM R X S T hST n x) := by
  apply Subtype.ext
  simp only [Work.Cohomology.relDiffLM_coe, tripleInclLM_coe]

/-- **The inclusion `C^*(X,T) → C^*(X,S)`** of relative cochain complexes, for `S ⊆ T`. -/
def tripleIncl (X : TopCat) (S T : Set X) (hST : S ⊆ T) :
    Work.Cohomology.relComplex R X T ⟶ Work.Cohomology.relComplex R X S :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (tripleInclLM R X S T hST n)) (fun n => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    show (ModuleCat.Hom.hom ((Work.Cohomology.relComplex R X S).d n (n+1)))
        (ModuleCat.Hom.hom (ModuleCat.ofHom (tripleInclLM R X S T hST n))
          (x : ↥(Work.Cohomology.relKern R X T n)))
      = ModuleCat.Hom.hom (ModuleCat.ofHom (tripleInclLM R X S T hST (n+1)))
          (ModuleCat.Hom.hom ((Work.Cohomology.relComplex R X T).d n (n+1))
            (x : ↥(Work.Cohomology.relKern R X T n)))
    rw [Work.Cohomology.relComplex_d, Work.Cohomology.relComplex_d]
    show (Work.Cohomology.relDiffLM R X S n)
        (tripleInclLM R X S T hST n (x : ↥(Work.Cohomology.relKern R X T n)))
      = (tripleInclLM R X S T hST (n+1))
          (Work.Cohomology.relDiffLM R X T n (x : ↥(Work.Cohomology.relKern R X T n)))
    exact relDiffLM_tripleInclLM R X S T hST n (x : ↥(Work.Cohomology.relKern R X T n)))

@[simp] theorem tripleIncl_f (X : TopCat) (S T : Set X) (hST : S ⊆ T) (n : ℕ) :
    (tripleIncl R X S T hST).f n = ModuleCat.ofHom (tripleInclLM R X S T hST n) := rfl

/-! ## The restriction to `T` -/

/-- The compatibility condition of the restriction map to `T`, as a named function (so that it can
be referred to in the computation rules below). -/
def tripleRestrPred (X : TopCat) (S T : Set X) (hST : S ⊆ T) :
    ∀ x ∈ ({x : ↥T | (x : X) ∈ S} : Set ↥T),
      (ConcreteCategory.hom (Work.Cohomology.subtypeIncl X T)) x ∈ S :=
  fun _ hx => hx

/-- The `n`-th component of the restriction `C^n(X,S) → C^n(T,S)`, as a linear map. -/
def tripleRestrLM (X : TopCat) (S T : Set X) (hST : S ⊆ T) (n : ℕ) :
    Work.Cohomology.relKern R X S n →ₗ[R]
      Work.Cohomology.relKern R (TopCat.of T) {x : ↥T | (x : X) ∈ S} n :=
  Work.Cohomology.relMapLM (X₁ := TopCat.of T) (X₂ := X) R
    {x : ↥T | (x : X) ∈ S} S (Work.Cohomology.subtypeIncl X T) (tripleRestrPred X S T hST) n

@[simp] theorem tripleRestrLM_coe (X : TopCat) (S T : Set X) (hST : S ⊆ T) (n : ℕ)
    (x : Work.Cohomology.relKern R X S n) :
    ((tripleRestrLM R X S T hST n x :
        Work.Cohomology.relKern R (TopCat.of T) {x : ↥T | (x : X) ∈ S} n) :
      (Work.Cohomology.singularCochainComplex R (TopCat.of T)).X n)
      = ((Work.Cohomology.restr R X T).f n).hom x.1 := by
  rw [tripleRestrLM, Work.Cohomology.relMapLM_coe (X₁ := TopCat.of T) (X₂ := X) R
    {x : ↥T | (x : X) ∈ S} S (Work.Cohomology.subtypeIncl X T) (tripleRestrPred X S T hST) n x]
  rfl

/-- **The restriction `C^*(X,S) → C^*(T,S)`** of relative cochains to `T`. -/
def tripleRestr (X : TopCat) (S T : Set X) (hST : S ⊆ T) :
    Work.Cohomology.relComplex R X S ⟶
      Work.Cohomology.relComplex R (TopCat.of T) {x : ↥T | (x : X) ∈ S} :=
  Work.Cohomology.relComplexMap (X₁ := TopCat.of T) (X₂ := X) R
    {x : ↥T | (x : X) ∈ S} S (Work.Cohomology.subtypeIncl X T) (tripleRestrPred X S T hST)

@[simp] theorem tripleRestr_f (X : TopCat) (S T : Set X) (hST : S ⊆ T) (n : ℕ) :
    (tripleRestr R X S T hST).f n = ModuleCat.ofHom (tripleRestrLM R X S T hST n) := rfl

/-! ## The short complex -/

/-- The restriction kills the image of the inclusion. -/
theorem tripleRestrLM_tripleInclLM (X : TopCat) (S T : Set X) (hST : S ⊆ T) (n : ℕ)
    (x : Work.Cohomology.relKern R X T n) :
    tripleRestrLM R X S T hST n (tripleInclLM R X S T hST n x) = 0 := by
  apply Subtype.ext
  rw [tripleRestrLM_coe, tripleInclLM_coe]
  show ((Work.Cohomology.restr R X T).f n).hom x.1 = 0
  exact x.2

/-- The composite `C^*(X,T) → C^*(X,S) → C^*(T,S)` is zero. -/
theorem tripleIncl_comp_tripleRestr (X : TopCat) (S T : Set X) (hST : S ⊆ T) :
    tripleIncl R X S T hST ≫ tripleRestr R X S T hST = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f_apply]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  show tripleRestrLM R X S T hST n
      (tripleInclLM R X S T hST n (x : ↥(Work.Cohomology.relKern R X T n))) = 0
  exact tripleRestrLM_tripleInclLM R X S T hST n (x : ↥(Work.Cohomology.relKern R X T n))


/-- **The short complex of the triple `S ⊆ T ⊆ X`**:
`0 ⟶ C^*(X,T) ⟶ C^*(X,S) ⟶ C^*(T,S) ⟶ 0`. -/
def tripleShortCoh (X : TopCat) (S T : Set X) (hST : S ⊆ T) :
    ShortComplex (CochainComplex (ModuleCat R) ℕ) :=
  ShortComplex.mk (tripleIncl R X S T hST) (tripleRestr R X S T hST)
    (tripleIncl_comp_tripleRestr R X S T hST)

@[simp] theorem tripleShortCoh_f (X : TopCat) (S T : Set X) (hST : S ⊆ T) :
    (tripleShortCoh R X S T hST).f = tripleIncl R X S T hST := rfl

@[simp] theorem tripleShortCoh_g (X : TopCat) (S T : Set X) (hST : S ⊆ T) :
    (tripleShortCoh R X S T hST).g = tripleRestr R X S T hST := rfl

end

end Work.Serre
