import Mathlib
import Submission.Work.Cohomology.wsfDefs
import Submission.Work.Cohomology.chainRetract_mem_range_inclChains
import Submission.Work.Cohomology.cokerSmallAux
import Submission.Work.Cohomology.exists_relComplexMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-! ## Surjectivity of the restriction of relative cochains

The restriction `C^n(T, T∩A) → C^n(S, S∩A)` along an inclusion `S ⊆ T` is surjective: a relative
cochain on `S` extends to `T` by evaluating on the *retraction* of the chains of `T` onto the
chains of `S` (`chainRetract`), which is well defined because singular chains are free on singular
simplices.  The extension of a cochain vanishing on the chains of `S ∩ A` still vanishes on the
chains of `T ∩ A` because the retraction sends chains supported in `A` to chains supported in `A`.

The two properties of the retraction that are used are isolated in the general lemma
`relMapLM_surjective_of_retract`. -/

/-- The kernel condition defining the relative cochains `C^n(X,A)`: a relative cochain vanishes on
every chain supported in `A`, i.e. on the image of `C_*(A)`. -/
lemma relKern_apply_inclChains {X : TopCat} (A : Set X) {n : ℕ}
    (α : (singularChains ℤ X).X n →ₗ[ℤ] ℤ) (hα : α ∈ relKern ℤ X A n)
    (x : (singularChains ℤ (TopCat.of A)).X n) :
    α (((inclChains X A).f n).hom x) = 0 := by
  have h1 : ((SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A))
      (ModuleCat.of ℤ ℤ)).f n).hom.dualMap α = 0 := by
    have hh := hα
    rw [relKern, LinearMap.mem_ker, restr, dualChainMap_f_hom, chainMap_f_eq] at hh
    exact hh
  have h2 := LinearMap.congr_fun h1 x
  rw [LinearMap.dualMap_apply, LinearMap.zero_apply] at h2
  have hbr : ((SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A))
        (ModuleCat.of ℤ ℤ)).f n).hom x = ((inclChains X A).f n).hom x := rfl
  rwa [hbr] at h2

/-- **Surjectivity of the restriction of relative cochains, from a retraction of the chains.**
Let `f : X₁ ⟶ X₂` be a map of pairs `(X₁,A₁) → (X₂,A₂)`.  If the chain map `C_*(X₁) ⟶ C_*(X₂)`
induced by `f` admits a retraction `s` in degree `n` which carries chains supported in `A₂` to
chains supported in `A₁`, then the induced map on relative `n`-cochains
`C^n(X₂,A₂) → C^n(X₁,A₁)` is surjective: a relative cochain on `X₁` extends along `s`. -/
theorem relMapLM_surjective_of_retract {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂)
    (f : X₁ ⟶ X₂) (h : ∀ x ∈ A₁, f x ∈ A₂) (n : ℕ)
    (s : (singularChains ℤ X₂).X n →ₗ[ℤ] (singularChains ℤ X₁).X n)
    (hsec : s.comp ((chainMap ℤ X₁ X₂ f).f n).hom = LinearMap.id)
    (hsupp : ∀ c, c ∈ LinearMap.range ((inclChains X₂ A₂).f n).hom →
      s c ∈ LinearMap.range ((inclChains X₁ A₁).f n).hom) :
    Function.Surjective (relMapLM ℤ A₁ A₂ f h n) := by
  intro y
  set Y : (singularChains ℤ X₁).X n →ₗ[ℤ] ℤ := y.1 with hY
  have hYmem : Y ∈ relKern ℤ X₁ A₁ n := y.2
  have hykill : ∀ c, c ∈ LinearMap.range ((inclChains X₁ A₁).f n).hom → Y c = 0 := by
    intro c hc
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hc
    exact relKern_apply_inclChains A₁ Y hYmem z
  refine ⟨⟨Y.comp s, ?_⟩, ?_⟩
  · have hmem : ((restr ℤ X₂ A₂).f n).hom (Y.comp s) = 0 := by
      rw [restr, dualChainMap_f_hom, chainMap_f_eq]
      apply LinearMap.ext
      intro z
      simp only [LinearMap.zero_apply]
      exact hykill _ (hsupp _ (LinearMap.mem_range.mpr ⟨z, rfl⟩))
    exact LinearMap.mem_ker.mpr hmem
  · apply Subtype.ext
    rw [relMapLM_coe, dualChainMap_f_hom]
    change ((ModuleCat.Hom.hom ((chainMap ℤ X₁ X₂ f).f n)).dualMap (Y.comp s)) = Y
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun hsec x
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hx
    rw [LinearMap.dualMap_apply, LinearMap.comp_apply, hx]

/-- The chains of `T ∩ A`, included into the chains of `T` and then into the chains of `X`,
factor through the chains of `A`. -/
lemma inclChains_relSubset_comp_inclChains {X : Type} [TopologicalSpace X] (A T : Set X) :
    inclChains (TopCat.of T) (relSubset (X := TopCat.of X) A T) ≫ inclChains (TopCat.of X) T
      = chainMap ℤ (TopCat.of (relSubset (X := TopCat.of X) A T)) (TopCat.of A)
          (overlapIncl (X := TopCat.of X) A T) ≫ inclChains (TopCat.of X) A := by
  rw [inclChains, inclChains, inclChains, chainMap_compPD, chainMap_compPD,
    ← overlapIncl_comp_subtypeIncl (X := TopCat.of X) A T]

/-- The previous identity in degree `n`. -/
lemma inclChains_relSubset_comp_inclChains_f {X : Type} [TopologicalSpace X] (A T : Set X) (n : ℕ) :
    ((inclChains (TopCat.of T) (relSubset (X := TopCat.of X) A T)).f n
        ≫ (inclChains (TopCat.of X) T).f n)
      = ((chainMap ℤ (TopCat.of (relSubset (X := TopCat.of X) A T)) (TopCat.of A)
            (overlapIncl (X := TopCat.of X) A T)).f n
        ≫ (inclChains (TopCat.of X) A).f n) := by
  rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f,
    inclChains_relSubset_comp_inclChains]

/-- The inclusion `S ↪ T` followed by the inclusion `T ↪ X` of the chains is the inclusion
`S ↪ X`. -/
lemma chainMap_pdIncl_comp_inclChains {X : Type} [TopologicalSpace X] {S T : Set X} (h : S ⊆ T) :
    chainMap ℤ (TopCat.of S) (TopCat.of T) (pdIncl (M := TopCat.of X) T S h)
      ≫ inclChains (TopCat.of X) T = inclChains (TopCat.of X) S := by
  have hc : pdIncl (M := TopCat.of X) T S h ≫ subtypeIncl (TopCat.of X) T
      = subtypeIncl (TopCat.of X) S := by
    ext y; rfl
  rw [inclChains, inclChains, chainMap_compPD, hc]

/-- The retraction of the chains of `S` inside `X` splits the inclusion of the chains of `S` into
the chains of `T`. -/
lemma chainMap_pdIncl_comp_chainRetract {X : Type} [TopologicalSpace X] {S T : Set X}
    (h : S ⊆ T) (n : ℕ) :
    ((chainMap ℤ (TopCat.of S) (TopCat.of T) (pdIncl (M := TopCat.of X) T S h)).f n
        ≫ (inclChains (TopCat.of X) T).f n) ≫ chainRetract ℤ (TopCat.of X) S n = 𝟙 _ := by
  rw [← HomologicalComplex.comp_f, chainMap_pdIncl_comp_inclChains, inclChains]
  exact chainRetract_spec ℤ (TopCat.of X) S n

theorem rcResLM_surjective {X : Type} [TopologicalSpace X] (A : Set X) {S T : Set X} (h : S ⊆ T) (n : ℕ) :
    Function.Surjective (rcResLM A h n) := by
  classical
  refine relMapLM_surjective_of_retract (X₁ := TopCat.of S) (X₂ := TopCat.of T)
    (relSubset (X := TopCat.of X) A S) (relSubset (X := TopCat.of X) A T)
    (pdIncl (M := TopCat.of X) T S h) (fun y hy => hy) n
    ((chainRetract ℤ (TopCat.of X) S n).hom.comp ((inclChains (TopCat.of X) T).f n).hom) ?_ ?_
  · have h1 := congrArg ModuleCat.Hom.hom (chainMap_pdIncl_comp_chainRetract (X := X) h n)
    simp only [ModuleCat.hom_comp, ModuleCat.hom_id] at h1
    rw [LinearMap.comp_assoc]
    exact h1
  · intro c hc
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hc
    have hz : ((inclChains (TopCat.of X) T).f n).hom
          (((inclChains (TopCat.of T) (relSubset (X := TopCat.of X) A T)).f n).hom z)
        = ((inclChains (TopCat.of X) A).f n).hom
          (((chainMap ℤ (TopCat.of (relSubset (X := TopCat.of X) A T)) (TopCat.of A)
              (overlapIncl (X := TopCat.of X) A T)).f n).hom z) := by
      have h3 := congrArg ModuleCat.Hom.hom
        (inclChains_relSubset_comp_inclChains_f (X := X) A T n)
      simp only [ModuleCat.hom_comp] at h3
      exact LinearMap.congr_fun h3 z
    have hmem := chainRetract_comp_inclChains_mem_range (X := TopCat.of X) A S n
      (((chainMap ℤ (TopCat.of (relSubset (X := TopCat.of X) A T)) (TopCat.of A)
          (overlapIncl (X := TopCat.of X) A T)).f n).hom z)
    rw [← hz] at hmem
    exact hmem

end

end Work.Cohomology

