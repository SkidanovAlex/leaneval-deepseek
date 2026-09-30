import Mathlib
import Submission.Work.Serre.TripleCohDefs
import Submission.Work.Thom.Cohomology

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false



/-!
# The long exact sequence of a triple (singular cohomology)

The short exact sequence of cochain complexes `0 → C^*(X,T) → C^*(X,S) → C^*(T,S) → 0`
(`Work.Serre.tripleShortCoh`, defined in `Submission/Work/Serre/TripleCohDefs.lean`) is proved short
exact here; the exactness of the associated long exact sequence follows from the general theory of
the homology sequence of a short exact sequence of cochain complexes.

The only non-formal input is the surjectivity of the restriction `C^n(X,S) → C^n(T,S)` at the level
of modules: a cochain on `T` vanishing on `S` extends to a cochain on `X` vanishing on `S`.  The
explicit extension is `w.1 ∘ chainRetract` where `w` is any extension of the cochain to `X`
(existing by `Work.Cohomology.surjective_restr`), which is exactly how the composite
`C^n(X,S) → C^n(T,S)` is split.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

variable (R : Type) [CommRing R]

/-! ## The inclusion `S → T` and its factorization -/

/-- The inclusion `S → T`, viewed as a map into the subtype `{x : ↥T | ↑x ∈ S}`. -/
def subToA1 (X : TopCat) (S T : Set X) (hST : S ⊆ T) :
    TopCat.of S ⟶ TopCat.of {x : ↥T | (x : X) ∈ S} :=
  TopCat.ofHom ⟨fun x => ⟨⟨x.1, hST x.2⟩, x.2⟩, by
    refine Continuous.subtype_mk ?_ _
    exact Continuous.subtype_mk continuous_subtype_val (fun x => hST x.2)⟩

/-- The factorization of the inclusion `S → T` through the subtype `{x : ↥T | ↑x ∈ S}`. -/
theorem subToA1_comp (X : TopCat) (S T : Set X) (hST : S ⊆ T) :
    subToA1 X S T hST ≫ Work.Cohomology.subtypeIncl (TopCat.of T) {x : ↥T | (x : X) ∈ S}
      = subIncl S T hST := by
  ext x
  rfl

/-- The factorization `S → T → X` through the subtype `{x : ↥T | ↑x ∈ S}`. -/
theorem subtypeIncl_fac (X : TopCat) (S T : Set X) (hST : S ⊆ T) :
    Work.Cohomology.subtypeIncl X S
      = subToA1 X S T hST ≫ Work.Cohomology.subtypeIncl (TopCat.of T) {x : ↥T | (x : X) ∈ S}
        ≫ Work.Cohomology.subtypeIncl X T := by
  ext x
  rfl

/-- The chain-level factorization of the inclusion `S → X`. -/
theorem chainMap_subtypeIncl_fac (X : TopCat) (S T : Set X) (hST : S ⊆ T) :
    Work.Cohomology.chainMap R (TopCat.of S) X (Work.Cohomology.subtypeIncl X S)
      = Work.Cohomology.chainMap R (TopCat.of S) (TopCat.of {x : ↥T | (x : X) ∈ S})
          (subToA1 X S T hST)
        ≫ Work.Cohomology.chainMap R (TopCat.of {x : ↥T | (x : X) ∈ S}) (TopCat.of T)
            (Work.Cohomology.subtypeIncl (TopCat.of T) {x : ↥T | (x : X) ∈ S})
        ≫ Work.Cohomology.chainMap R (TopCat.of T) X (Work.Cohomology.subtypeIncl X T) := by
  rw [subtypeIncl_fac X S T hST,
    ← chainMap_comp_gen R (subToA1 X S T hST)
      (Work.Cohomology.subtypeIncl (TopCat.of T) {x : ↥T | (x : X) ∈ S}
        ≫ Work.Cohomology.subtypeIncl X T),
    ← chainMap_comp_gen R (Work.Cohomology.subtypeIncl (TopCat.of T) {x : ↥T | (x : X) ∈ S})
      (Work.Cohomology.subtypeIncl X T)]

/-- The `n`-th component of the chain-level factorization. -/
theorem chainMap_subtypeIncl_fac_f (X : TopCat) (S T : Set X) (hST : S ⊆ T) (n : ℕ) :
    (Work.Cohomology.chainMap R (TopCat.of S) X (Work.Cohomology.subtypeIncl X S)).f n
      = (Work.Cohomology.chainMap R (TopCat.of S) (TopCat.of {x : ↥T | (x : X) ∈ S})
            (subToA1 X S T hST)).f n
        ≫ (Work.Cohomology.chainMap R (TopCat.of {x : ↥T | (x : X) ∈ S}) (TopCat.of T)
            (Work.Cohomology.subtypeIncl (TopCat.of T) {x : ↥T | (x : X) ∈ S})).f n
        ≫ (Work.Cohomology.chainMap R (TopCat.of T) X (Work.Cohomology.subtypeIncl X T)).f n := by
  have h := congrArg (fun K => K.f n) (chainMap_subtypeIncl_fac R X S T hST)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f] at h
  exact h

/-! ## Surjectivity of the restriction -/

/-- **The restriction `C^n(X,S) → C^n(T,S)` is surjective.**  A cochain `z` on `T` vanishing on `S`
extends to a cochain `w` on `X` (by `Work.Cohomology.surjective_restr`), and any such extension
vanishes on `S` because the inclusion `S → X` factors through `T` as
`S → {x : ↥T | ↑x ∈ S} → T → X` and `z` vanishes on the middle term. -/
theorem surjective_tripleRestrLM (X : TopCat) (S T : Set X) (hST : S ⊆ T) (n : ℕ) :
    Function.Surjective (tripleRestrLM R X S T hST n) := by
  intro z
  obtain ⟨w, hw⟩ := Work.Cohomology.surjective_restr R X T n z.1
  have hmem : ((Work.Cohomology.restr R X S).f n).hom w = 0 := by
    have hfact : Work.Cohomology.restr R X S
        = Work.Cohomology.restr R X T ≫
          Work.Cohomology.dualChainMap R (TopCat.of S) (TopCat.of T) (subIncl S T hST) := by
      rw [Work.Cohomology.restr, Work.Cohomology.restr, ← subIncl_subtypeIncl S T hST,
        Work.Cohomology.dualChainMap_comp]
    rw [hfact, HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply, hw]
    have hfact2 : Work.Cohomology.dualChainMap R (TopCat.of S) (TopCat.of T) (subIncl S T hST)
        = Work.Cohomology.dualChainMap R (TopCat.of {x : ↥T | (x : X) ∈ S}) (TopCat.of T)
            (Work.Cohomology.subtypeIncl (TopCat.of T) {x : ↥T | (x : X) ∈ S})
          ≫ Work.Cohomology.dualChainMap R (TopCat.of S)
              (TopCat.of {x : ↥T | (x : X) ∈ S}) (subToA1 X S T hST) := by
      rw [← subToA1_comp X S T hST]
      exact Work.Cohomology.dualChainMap_comp R (subToA1 X S T hST)
        (Work.Cohomology.subtypeIncl (TopCat.of T) {x : ↥T | (x : X) ∈ S})
    have hz2 : ((Work.Cohomology.dualChainMap R (TopCat.of {x : ↥T | (x : X) ∈ S}) (TopCat.of T)
        (Work.Cohomology.subtypeIncl (TopCat.of T) {x : ↥T | (x : X) ∈ S})).f n).hom z.1 = 0 := z.2
    rw [hfact2, HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply, hz2,
      map_zero]
  exact ⟨⟨w, hmem⟩, by
    apply Subtype.ext
    rw [tripleRestrLM_coe, hw]⟩

/-- The `n`-th component of the `f` of the degreewise short complex. -/
theorem tripleShortCoh_map_f (X : TopCat) (S T : Set X) (hST : S ⊆ T) (n : ℕ) :
    ((tripleShortCoh R X S T hST).map
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) n)).f
      = ModuleCat.ofHom (tripleInclLM R X S T hST n) := by
  rw [show ((tripleShortCoh R X S T hST).map
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) n)).f
      = (tripleIncl R X S T hST).f n from rfl]
  exact tripleIncl_f R X S T hST n

/-- The `n`-th component of the `g` of the degreewise short complex. -/
theorem tripleShortCoh_map_g (X : TopCat) (S T : Set X) (hST : S ⊆ T) (n : ℕ) :
    ((tripleShortCoh R X S T hST).map
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) n)).g
      = ModuleCat.ofHom (tripleRestrLM R X S T hST n) := by
  rw [show ((tripleShortCoh R X S T hST).map
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) n)).g
      = (tripleRestr R X S T hST).f n from rfl]
  exact tripleRestr_f R X S T hST n

/-- **The short complex of the triple `S ⊆ T ⊆ X` is short exact.** -/
theorem tripleShortCoh_shortExact (X : TopCat) (S T : Set X) (hST : S ⊆ T) :
    (tripleShortCoh R X S T hST).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · rw [tripleShortCoh_map_f R X S T hST n, tripleShortCoh_map_g R X S T hST n]
    show Function.Exact (tripleInclLM R X S T hST n) (tripleRestrLM R X S T hST n)
    intro y
    constructor
    · intro hy
      have hy' : ((Work.Cohomology.restr R X T).f n).hom y.1 = 0 := by
        have h := congrArg Subtype.val hy
        rw [tripleRestrLM_coe] at h
        simpa using h
      exact ⟨⟨y.1, hy'⟩, Subtype.ext rfl⟩
    · rintro ⟨x, rfl⟩
      exact tripleRestrLM_tripleInclLM R X S T hST n x
  · rw [tripleShortCoh_map_f R X S T hST n]
    show Function.Injective (tripleInclLM R X S T hST n)
    intro a b h
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    rw [tripleInclLM_coe, tripleInclLM_coe] at h'
    exact h'
  · rw [tripleShortCoh_map_g R X S T hST n]
    exact surjective_tripleRestrLM R X S T hST n

/-! ## The long exact sequence of the triple -/

/-- The connecting homomorphism `H^n(T,S) ⟶ H^{n+1}(X,T)` of the triple `S ⊆ T ⊆ X`. -/
def tripleCohδ (X : TopCat) (S T : Set X) (hST : S ⊆ T) (n : ℕ) :
    Work.Thom.RelCoh R n (TopCat.of T) {x : ↥T | (x : X) ∈ S} ⟶
      Work.Thom.RelCoh R (n + 1) X T :=
  (tripleShortCoh_shortExact R X S T hST).δ n (n + 1) (by simp [ComplexShape.up])

/-- The connecting homomorphism followed by the forgetful map is zero. -/
theorem tripleCohδ_comp (X : TopCat) (S T : Set X) (hST : S ⊆ T) (n : ℕ) :
    CategoryTheory.CategoryStruct.comp (tripleCohδ R X S T hST n)
      (HomologicalComplex.homologyMap (tripleIncl R X S T hST) (n + 1)) = 0 :=
  (tripleShortCoh_shortExact R X S T hST).δ_comp n (n + 1) (by simp [ComplexShape.up])

/-- The restriction followed by the connecting homomorphism is zero. -/
theorem tripleCoh_comp_δ (X : TopCat) (S T : Set X) (hST : S ⊆ T) (n : ℕ) :
    CategoryTheory.CategoryStruct.comp
      (HomologicalComplex.homologyMap (tripleRestr R X S T hST) n)
      (tripleCohδ R X S T hST n) = 0 :=
  (tripleShortCoh_shortExact R X S T hST).comp_δ n (n + 1) (by simp [ComplexShape.up])

/-- Exactness of the long exact sequence of the triple at `H^{n+1}(X,T)`. -/
theorem tripleCoh_exact₁ (X : TopCat) (S T : Set X) (hST : S ⊆ T) (n : ℕ) :
    (ShortComplex.mk (tripleCohδ R X S T hST n)
      (HomologicalComplex.homologyMap (tripleIncl R X S T hST) (n + 1))
      (tripleCohδ_comp R X S T hST n)).Exact :=
  (tripleShortCoh_shortExact R X S T hST).homology_exact₁ n (n + 1)
    (by simp [ComplexShape.up])

/-- Exactness of the long exact sequence of the triple at `H^n(X,S)`. -/
theorem tripleCoh_exact₂ (X : TopCat) (S T : Set X) (hST : S ⊆ T) (n : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (tripleIncl R X S T hST) n)
      (HomologicalComplex.homologyMap (tripleRestr R X S T hST) n)
      (by rw [← HomologicalComplex.homologyMap_comp,
        Work.Serre.tripleIncl_comp_tripleRestr, HomologicalComplex.homologyMap_zero])).Exact :=
  (tripleShortCoh_shortExact R X S T hST).homology_exact₂ n

/-- Exactness of the long exact sequence of the triple at `H^n(T,S)`. -/
theorem tripleCoh_exact₃ (X : TopCat) (S T : Set X) (hST : S ⊆ T) (n : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (tripleRestr R X S T hST) n)
      (tripleCohδ R X S T hST n) (tripleCoh_comp_δ R X S T hST n)).Exact :=
  (tripleShortCoh_shortExact R X S T hST).homology_exact₃ n (n + 1)
    (by simp [ComplexShape.up])

/-- Exactness at the middle term, in the `range = ker` form. -/
theorem tripleCoh_exact₂_range (X : TopCat) (S T : Set X) (hST : S ⊆ T) (n : ℕ) :
    LinearMap.range (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (tripleIncl R X S T hST) n)) =
      LinearMap.ker (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (tripleRestr R X S T hST) n)) :=
  (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp (tripleCoh_exact₂ R X S T hST n)

/-- Exactness at the third term, in the `range = ker` form. -/
theorem tripleCoh_exact₃_range (X : TopCat) (S T : Set X) (hST : S ⊆ T) (n : ℕ) :
    LinearMap.range (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (tripleRestr R X S T hST) n)) =
      LinearMap.ker (ModuleCat.Hom.hom (tripleCohδ R X S T hST n)) :=
  (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp (tripleCoh_exact₃ R X S T hST n)

/-- Exactness at the first term, in the `range = ker` form. -/
theorem tripleCoh_exact₁_range (X : TopCat) (S T : Set X) (hST : S ⊆ T) (n : ℕ) :
    LinearMap.range (ModuleCat.Hom.hom (tripleCohδ R X S T hST n)) =
      LinearMap.ker (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (tripleIncl R X S T hST) (n + 1))) :=
  (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp (tripleCoh_exact₁ R X S T hST n)

end

end Work.Serre
