import Mathlib
import Submission.Work.Cohomology.RelCapHTransfer
import Submission.Work.Cohomology.localHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

noncomputable section

/-- Functoriality of `chainMap` on singular chains (local copy). -/
theorem chainMap_compPD (X Y Z : TopCat) (f : X ⟶ Y) (g : Y ⟶ Z) :
    chainMap ℤ X Y f ≫ chainMap ℤ Y Z g = chainMap ℤ X Z (f ≫ g) := by
  show (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map f)
      ≫ (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map g)
    = (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map (f ≫ g))
  rw [Functor.map_comp]

/-- The inclusion of chains `C_*(A) ⟶ C_*(B)` for `A ⊆ B ⊆ X`. -/
def inclChainsSub (X : TopCat) (A B : Set X) (h : A ⊆ B) :
    singularChains ℤ (TopCat.of A) ⟶ singularChains ℤ (TopCat.of B) :=
  chainMap ℤ (TopCat.of A) (TopCat.of B) (TopCat.ofHom ⟨fun x => ⟨x.1, h x.2⟩,
    Continuous.subtype_mk (f := fun x : A => (x : X)) (continuous_subtype_val) (fun x => h x.2)⟩)

/-- The inclusion factors through the inclusion `A ⊆ B`. -/
theorem inclChainsSub_comp (X : TopCat) (A B : Set X) (h : A ⊆ B) :
    inclChainsSub X A B h ≫ inclChains X B = inclChains X A := by
  rw [inclChainsSub, inclChains, inclChains, chainMap_compPD]
  rw [show (TopCat.ofHom ⟨fun x : A => ⟨(x : X), h x.2⟩,
      Continuous.subtype_mk (f := fun x : A => (x : X)) continuous_subtype_val (fun x => h x.2)⟩ : TopCat.of A ⟶ TopCat.of B)
      ≫ subtypeIncl X B = subtypeIncl X A from by ext x; rfl]

/-- **The natural map of relative chain complexes `C_*(X,A) ⟶ C_*(X,B)` for `A ⊆ B`.** -/
def relChainsSubMap (X : TopCat) (A B : Set X) (h : A ⊆ B) :
    relChains X A ⟶ relChains X B :=
  cokernel.desc (inclChains X A) (cokernel.π (inclChains X B)) (by
    rw [← inclChainsSub_comp X A B h, Category.assoc, cokernel.condition, comp_zero])

/-- The defining property of `relChainsSubMap`. -/
theorem relChainsSubMap_comp (X : TopCat) (A B : Set X) (h : A ⊆ B) :
    cokernel.π (inclChains X A) ≫ relChainsSubMap X A B h = cokernel.π (inclChains X B) := by
  rw [relChainsSubMap, cokernel.π_desc]

/-- The composite of the inclusions `A ⊆ B ⊆ X` of chains. -/
theorem inclChainsSub_comp' {X : TopCat} {A B C : Set X} (h₁ : A ⊆ B) (h₂ : B ⊆ C) :
    inclChainsSub X A B h₁ ≫ inclChainsSub X B C h₂ = inclChainsSub X A C (h₁.trans h₂) := by
  rw [inclChainsSub, inclChainsSub, inclChainsSub, chainMap_compPD]
  rw [show (TopCat.ofHom ⟨fun x : A => ⟨(x : X), h₁ x.2⟩,
      Continuous.subtype_mk (f := fun x : A => (x : X)) continuous_subtype_val (fun x => h₁ x.2)⟩ :
        TopCat.of A ⟶ TopCat.of B)
      ≫ (TopCat.ofHom ⟨fun x : B => ⟨(x : X), h₂ x.2⟩,
      Continuous.subtype_mk (f := fun x : B => (x : X)) continuous_subtype_val (fun x => h₂ x.2)⟩ :
        TopCat.of B ⟶ TopCat.of C)
      = (TopCat.ofHom ⟨fun x : A => ⟨(x : X), h₁.trans h₂ x.2⟩,
      Continuous.subtype_mk (f := fun x : A => (x : X)) continuous_subtype_val (fun x => h₁.trans h₂ x.2)⟩ :
        TopCat.of A ⟶ TopCat.of C) from by ext x; rfl]

/-- **The natural map of relative chain complexes `C_*(X,A) ⟶ C_*(X,B)` for `A ⊆ B`**, written on
the cokernels (the form in which the local classes of a fundamental class are stated). -/
def relCokerMap (X : TopCat) (A B : Set X) (h : A ⊆ B) :
    cokernel (inclChains X A) ⟶ cokernel (inclChains X B) :=
  cokernel.map (inclChains X A) (inclChains X B) (inclChainsSub X A B h) (𝟙 _)
    (by rw [Category.comp_id, inclChainsSub_comp])

/-- The defining property of `relCokerMap`. -/
theorem relCokerMap_comp_π (X : TopCat) (A B : Set X) (h : A ⊆ B) :
    cokernel.π (inclChains X A) ≫ relCokerMap X A B h = cokernel.π (inclChains X B) := by
  rw [relCokerMap, cokernel_π_map, Category.id_comp]

/-- Functoriality of `relCokerMap` in the pair of subsets. -/
theorem relCokerMap_comp {X : TopCat} {A B C : Set X} (h₁ : A ⊆ B) (h₂ : B ⊆ C) :
    relCokerMap X A B h₁ ≫ relCokerMap X B C h₂ = relCokerMap X A C (h₁.trans h₂) := by
  apply (cancel_epi (cokernel.π (inclChains X A))).mp
  rw [← Category.assoc, relCokerMap_comp_π X A B h₁, relCokerMap_comp_π X B C h₂,
    relCokerMap_comp_π X A C (h₁.trans h₂)]

/-- **The local class of `c` at a set `K`**: the image of `c` in `H_N(M, M∖K)`, written on the
cokernel (the form in which the hypothesis `hc` is stated). -/
noncomputable def relLocClass (M : TopCat) (N : ℕ) (c : (singularChains ℤ M).homology N)
    (K : Set M) : (cokernel (inclChains M Kᶜ)).homology N :=
  HomologicalComplex.homologyMap (cokernel.π (inclChains M Kᶜ)) N c

/-- **Functoriality of the local classes**: for `K ⊆ K'` the class at `K'` restricts to the class at
`K` (both are the image of `c`). -/
theorem relLocClass_restrict (M : TopCat) (N : ℕ) (c : (singularChains ℤ M).homology N)
    {K K' : Set M} (h : K ⊆ K') :
    HomologicalComplex.homologyMap (relCokerMap M K'ᶜ Kᶜ (fun x hx hxK => hx (h hxK))) N
        (relLocClass M N c K') = relLocClass M N c K := by
  rw [relLocClass, relLocClass]
  rw [← ModuleCat.comp_apply (HomologicalComplex.homologyMap (cokernel.π (inclChains M K'ᶜ)) N)
        (HomologicalComplex.homologyMap (relCokerMap M K'ᶜ Kᶜ (fun x hx hxK => hx (h hxK))) N) c]
  rw [← HomologicalComplex.homologyMap_comp,
    relCokerMap_comp_π M K'ᶜ Kᶜ (fun x hx hxK => hx (h hxK))]

/-- The local class at a point, in the form in which the hypothesis `hc` is stated. -/
theorem relLocClass_singleton (M : TopCat) (N : ℕ) (c : (singularChains ℤ M).homology N) (x : M) :
    relLocClass M N c {x}
      = HomologicalComplex.homologyMap (cokernel.π (inclChains M {y | y ≠ x})) N c := by
  rw [relLocClass]
  congr 2

/-- The hypothesis `hc` of the target, restated for the local class at a point. -/
theorem relLocClass_point_span (M : TopCat) (N : ℕ) (c : (singularChains ℤ M).homology N)
    (hc : ∀ x : M, Submodule.span ℤ
      {((HomologicalComplex.homologyMap
          (cokernel.π (inclChains M {y | y ≠ x})) N) c)} = ⊤) (x : M) :
    Submodule.span ℤ {relLocClass M N c {x}} = ⊤ := by
  rw [relLocClass_singleton M N c x]
  exact hc x

/-- The relative chain complex is *definitionally* the cokernel of the inclusion of the chains of
`A` (this is the form in which local classes are naturally stated). -/
theorem relChains_eq_cokernel (X : TopCat) (A : Set X) :
    relChains X A = cokernel (inclChains X A) := rfl

/-- The relative homology is the homology of the cokernel (definitionally). -/
theorem relChains_homology_eq_cokernel (X : TopCat) (A : Set X) (i : ℕ) :
    (relChains X A).homology i = (cokernel (inclChains X A)).homology i := rfl

/-- Functoriality of `relCokerMap` on homology. -/
theorem homologyMap_relCokerMap_comp {X : TopCat} {A B C : Set X} (h₁ : A ⊆ B) (h₂ : B ⊆ C) (i : ℕ) :
    HomologicalComplex.homologyMap (relCokerMap X A B h₁) i
        ≫ HomologicalComplex.homologyMap (relCokerMap X B C h₂) i
      = HomologicalComplex.homologyMap (relCokerMap X A C (h₁.trans h₂)) i := by
  rw [← HomologicalComplex.homologyMap_comp, relCokerMap_comp]

/-- A compact subset of a normed space is contained in an open ball around any point.  (Used to
produce the radius in the deformation retraction of the punctured space onto the complement of a
compact convex set.) -/
theorem exists_ball_supset_of_isCompact {E : Type*} [NormedAddCommGroup E] {K : Set E}
    (hK : IsCompact K) (z : E) : ∃ R : ℝ, 0 < R ∧ K ⊆ Metric.ball z R := by
  obtain ⟨R0, hR0⟩ := hK.isBounded.subset_closedBall z
  refine ⟨|R0| + 1, by positivity, fun y hy => ?_⟩
  rw [Metric.mem_ball]
  have h1 : dist y z ≤ R0 := by simpa [dist_comm] using hR0 hy
  have h2 : R0 ≤ |R0| := le_abs_self R0
  linarith

end

end Work.Cohomology
