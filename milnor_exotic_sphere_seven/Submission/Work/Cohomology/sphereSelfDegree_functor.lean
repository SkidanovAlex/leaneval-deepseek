import Mathlib
import Submission.Work.Cohomology.Degree

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Functoriality of the degree of a self-map of a sphere

`Work.Cohomology.sphereSelfDegree n hn f` is the degree of a self-map `f` of the sphere
`Sⁿ ⊆ ℝⁿ⁺¹`, defined by choosing an isomorphism `H_n(Sⁿ; ℤ) ≅ ℤ` once and for all
(`Work.Cohomology.sphereHomologyTop`) and measuring the induced map on the top homology.

This file proves the three structural facts about that definition:

* the degree of the identity is `1`;
* the degree is multiplicative on composition, `deg (f ≫ g) = deg g · deg f`;
* the degree is a homotopy invariant.

The proof is elementary once the definitions are unwound: with `e : H_n(Sⁿ; ℤ) ≅ ℤ` the chosen
isomorphism, every element of `H_n(Sⁿ; ℤ)` is a `ℤ`-multiple of the chosen generator `e⁻¹ 1`
(`moduleIso_deg_apply`), and the composition and homotopy statements follow from functoriality of
the singular chain complex and homotopy invariance of singular homology.
-/

namespace Work.Cohomology

noncomputable section

open CategoryTheory

/-- **Degrees multiply.**  For an isomorphism `e : M ≅ ℤ` of `ℤ`-modules and an endomorphism `T`
of `M`, the integer `e (T x)` is always the product of `e (T (e⁻¹ 1))` and `e x`: the chosen
generator `e⁻¹ 1` generates `M`, so `T` is determined by its value on it. -/
lemma moduleIso_deg_apply (M : ModuleCat ℤ) (e : M ≅ ModuleCat.of ℤ ℤ) (T : M ⟶ M) (a : M) :
    ModuleCat.Hom.hom e.hom (ModuleCat.Hom.hom T a) =
      ModuleCat.Hom.hom e.hom (ModuleCat.Hom.hom T (ModuleCat.Hom.hom e.inv (1 : ℤ))) *
        ModuleCat.Hom.hom e.hom a := by
  have hmul : ∀ (k : ℤ), ModuleCat.Hom.hom e.inv k = k • ModuleCat.Hom.hom e.inv (1 : ℤ) := by
    intro k
    have hk : k = k • (1 : ℤ) := by rw [smul_eq_mul, mul_one]
    conv_lhs => rw [hk]
    exact map_zsmul _ k (1 : ℤ)
  have ha : a = (ModuleCat.Hom.hom e.hom a) • ModuleCat.Hom.hom e.inv (1 : ℤ) := by
    have h1 : ModuleCat.Hom.hom e.inv (ModuleCat.Hom.hom e.hom a) = a := by
      have h := congrArg ModuleCat.Hom.hom e.hom_inv_id
      rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
      exact LinearMap.congr_fun h a
    nth_rewrite 1 [← h1]
    exact hmul _
  conv_lhs => rw [ha]
  rw [map_zsmul, map_zsmul, zsmul_eq_mul]
  rw [Int.cast_id]
  ring

/-- Evaluation of a composite of morphisms of `ℤ`-modules. -/
lemma moduleCat_hom_comp_apply {M N P : ModuleCat ℤ} (α : M ⟶ N) (β : N ⟶ P) (x : M) :
    ModuleCat.Hom.hom (α ≫ β) x = ModuleCat.Hom.hom β (ModuleCat.Hom.hom α x) := by
  rw [ModuleCat.hom_comp]; rfl

/-- **Functoriality of the sphere degree.**  The degree of a self-map of `Sⁿ` (`n ≥ 1`) is `1` on
the identity, multiplicative on composition, and invariant under homotopy. -/
theorem sphereSelfDegree_functor (n : ℕ) (hn : 1 ≤ n) :
    Work.Cohomology.sphereSelfDegree n hn (CategoryTheory.CategoryStruct.id
        (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))) = 1 ∧
      (∀ f g : TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ⟶
          TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1),
        Work.Cohomology.sphereSelfDegree n hn (CategoryTheory.CategoryStruct.comp f g) =
          Work.Cohomology.sphereSelfDegree n hn g * Work.Cohomology.sphereSelfDegree n hn f) ∧
      (∀ f g : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
          Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1),
        ContinuousMap.Homotopic f g →
          Work.Cohomology.sphereSelfDegree n hn (TopCat.ofHom f) =
            Work.Cohomology.sphereSelfDegree n hn (TopCat.ofHom g)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [sphereSelfDegree, sphereHomologyGen]
    have hcm : chainMap ℤ (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
        (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
        (𝟙 _) = 𝟙 _ := by
      rw [chainMap, CategoryTheory.Functor.map_id]
    rw [hcm, HomologicalComplex.homologyMap_id]
    have h2 : (ModuleCat.Hom.hom ((sphereHomologyTop n hn).some.hom))
        (ModuleCat.Hom.hom ((sphereHomologyTop n hn).some.inv) (1 : ℤ)) = 1 := by
      have h := congrArg ModuleCat.Hom.hom ((sphereHomologyTop n hn).some.inv_hom_id)
      rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
      exact LinearMap.congr_fun h (1 : ℤ)
    exact h2
  · intro f g
    rw [sphereSelfDegree, sphereSelfDegree, sphereSelfDegree, sphereHomologyGen]
    have hcm : chainMap ℤ _ _ (f ≫ g) = chainMap ℤ _ _ f ≫ chainMap ℤ _ _ g := by
      rw [chainMap, CategoryTheory.Functor.map_comp]
    rw [hcm, HomologicalComplex.homologyMap_comp]
    rw [moduleCat_hom_comp_apply]
    exact moduleIso_deg_apply _ _ _ _
  · intro f g hfg
    obtain ⟨H⟩ := hfg
    rw [sphereSelfDegree, sphereSelfDegree, sphereHomologyGen]
    rw [show HomologicalComplex.homologyMap (chainMap ℤ _ _ (TopCat.ofHom f)) n =
        HomologicalComplex.homologyMap (chainMap ℤ _ _ (TopCat.ofHom g)) n from
      TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor H (ModuleCat.of ℤ ℤ) n]

end

end Work.Cohomology
