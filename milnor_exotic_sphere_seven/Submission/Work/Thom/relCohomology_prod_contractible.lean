import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Thom.relCohomology_euclidean_punctured
import Submission.Work.Cohomology.exists_relComplexMap
import Submission.Work.Cohomology.relChainsMapOf_isIso
import Submission.Work.Cohomology.relCohomologyDual
import Submission.Work.Cohomology.PairSequence
import Submission.Work.Cohomology.isIso_homologyMap_tau1
import Submission.Work.Cohomology.relComplexMapCollarIsIso
import Submission.Work.Cohomology.homotopyEquiv
import Submission.Work.Cohomology.homotopyEquiv_prod_fst
import Submission.Work.Thom.relCohomology_prod_contractible_defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Thom

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

/-- **The five lemma for the relative cochain complex of a pair.**  If a map of pairs
`f : (X₁,A₁) → (X₂,A₂)` induces an isomorphism on the absolute cohomology of `X` and of `A`
(in every degree), then it induces an isomorphism on the relative cohomology of the pair in every
degree.  This is `Work.Cohomology.isIso_homologyMap_tau1` applied to the morphism of short exact
sequences `pairShort R X₂ A₂ ⟶ pairShort R X₁ A₁` of `0 ⟶ C^*(–,–) ⟶ C^*(–) ⟶ C^*(A) ⟶ 0`. -/
theorem isIso_homologyMap_relComplexMap {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂)
    (f : X₁ ⟶ X₂) (h : ∀ x ∈ A₁, (ConcreteCategory.hom f) x ∈ A₂) (R : Type) [CommRing R] :
    (∀ m, CategoryTheory.IsIso
        (HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap R X₁ X₂ f) m)) →
      (∀ m, CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap R
        (TopCat.of A₁) (TopCat.of A₂) (Work.Cohomology.relMapSub A₁ A₂ f h)) m)) →
      ∀ n, CategoryTheory.IsIso
        (HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap R A₁ A₂ f h) n) := by
  intro hf hg n
  let S₁ : ShortComplex (CochainComplex (ModuleCat R) ℕ) := Work.Cohomology.pairShort R X₂ A₂
  let S₂ : ShortComplex (CochainComplex (ModuleCat R) ℕ) := Work.Cohomology.pairShort R X₁ A₁
  have hS₁ : S₁.ShortExact := Work.Cohomology.pairShort_shortExact R X₂ A₂
  have hS₂ : S₂.ShortExact := Work.Cohomology.pairShort_shortExact R X₁ A₁
  let φ : S₁ ⟶ S₂ :=
    { τ₁ := Work.Cohomology.relComplexMap R A₁ A₂ f h
      τ₂ := Work.Cohomology.dualChainMap R X₁ X₂ f
      τ₃ := Work.Cohomology.dualChainMap R (TopCat.of A₁) (TopCat.of A₂)
              (Work.Cohomology.relMapSub A₁ A₂ f h)
      comm₁₂ := by
        change Work.Cohomology.relComplexMap R A₁ A₂ f h ≫ Work.Cohomology.relIncl R X₁ A₁
          = Work.Cohomology.relIncl R X₂ A₂ ≫ Work.Cohomology.dualChainMap R X₁ X₂ f
        exact Work.Cohomology.relComplexMap_comp_relIncl_local A₁ A₂ f h
      comm₂₃ := by
        change Work.Cohomology.dualChainMap R X₁ X₂ f ≫ Work.Cohomology.restr R X₁ A₁
          = Work.Cohomology.restr R X₂ A₂ ≫ Work.Cohomology.dualChainMap R (TopCat.of A₁)
              (TopCat.of A₂) (Work.Cohomology.relMapSub A₁ A₂ f h)
        exact Work.Cohomology.dualChainMap_restr_comp R A₁ A₂ f h }
  have hkey := Work.Cohomology.isIso_homologyMap_tau1 R φ hS₁ hS₂ hf hg n
  have hτ : φ.τ₁ = Work.Cohomology.relComplexMap R A₁ A₂ f h := rfl
  rwa [hτ] at hkey

/-- For a contractible space `B` and any `S ⊆ Z`, the projection
`{p : B × Z // p.2 ∈ S} → S` induces an isomorphism on singular cohomology in every degree. -/
theorem isIso_homologyMap_dualChainMap_subtypeProj {B Z : Type} [TopologicalSpace B]
    [TopologicalSpace Z] [ContractibleSpace B] (S : Set Z) (R : Type) [CommRing R] (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap R
      (TopCat.of {p : B × Z // p.2 ∈ S}) (TopCat.of S)
      (TopCat.ofHom (subtypeProj B Z S))) n) := by
  obtain ⟨b₀, hb₀⟩ := id_nullhomotopic B
  let H' : ContinuousMap.Homotopy (ContinuousMap.const B b₀) (ContinuousMap.id B) := hb₀.symm.some
  let inv : C(↥S, {p : B × Z // p.2 ∈ S}) :=
    ⟨fun z => ⟨(b₀, z.1), z.2⟩, Continuous.subtype_mk
      ((continuous_const.prodMk continuous_id).comp continuous_subtype_val) (fun z => z.2)⟩
  have hright : (subtypeProj B Z S).comp inv = ContinuousMap.id ↥S := rfl
  have hrighth : ((subtypeProj B Z S).comp inv).Homotopic (ContinuousMap.id ↥S) :=
    hright.symm ▸ ContinuousMap.Homotopic.refl _
  have hleft : (inv.comp (subtypeProj B Z S)).Homotopic (ContinuousMap.id _) := by
    refine ⟨{ toFun := fun tp => ⟨(H' (tp.1, tp.2.1.1), tp.2.1.2), tp.2.2⟩
              continuous_toFun := ?_
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · exact Continuous.subtype_mk
        ((H'.continuous.comp (continuous_fst.prodMk
          (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)))).prodMk
          (continuous_snd.comp (continuous_subtype_val.comp continuous_snd)))
        (fun tp => tp.2.2)
    · intro p
      show (⟨(H' (0, p.1.1), p.1.2), p.2⟩ : {p : B × Z // p.2 ∈ S})
        = inv ⟨p.1.2, p.2⟩
      apply Subtype.ext
      apply Prod.ext
      · exact H'.map_zero_left p.1.1
      · rfl
    · intro p
      show (⟨(H' (1, p.1.1), p.1.2), p.2⟩ : {p : B × Z // p.2 ∈ S}) = p
      apply Subtype.ext
      apply Prod.ext
      · exact H'.map_one_left p.1.1
      · rfl
  exact Work.Cohomology.homotopyEquiv R (TopCat.of {p : B × Z // p.2 ∈ S}) (TopCat.of ↥S)
    (TopCat.ofHom (subtypeProj B Z S)) (TopCat.ofHom inv) hleft.some hrighth.some n

/-- The restricted projection `relMapSub` of the second projection is the map `subtypeProj`, which
is a homotopy equivalence when `B` is contractible; hence it induces an isomorphism on singular
cohomology.  Stated in the normal form in which the five lemma
(`Work.Thom.isIso_homologyMap_relComplexMap`) consumes it. -/
theorem subtypeProj_relMapSub {B Z : Type} [TopologicalSpace B] [TopologicalSpace Z]
    [ContractibleSpace B] (S : Set Z) (R : Type) [CommRing R] (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap R
      (TopCat.of {p : B × Z // p.2 ∈ S}) (TopCat.of S)
      (Work.Cohomology.relMapSub {p : B × Z | p.2 ∈ S} S (TopCat.ofHom (prodSnd B Z))
        (fun x hx => hx))) n) := by
  have heq : Work.Cohomology.relMapSub {p : B × Z | p.2 ∈ S} S (TopCat.ofHom (prodSnd B Z))
      (fun x hx => hx) = TopCat.ofHom (subtypeProj B Z S) := by
    apply TopCat.ext
    intro a
    rfl
  rw [heq]
  exact isIso_homologyMap_dualChainMap_subtypeProj (B := B) (Z := Z) S R n

/-- The pair map `(B × ℝⁿ, B × (ℝⁿ∖0)) → (ℝⁿ, ℝⁿ∖0)` (the second projection) induces an
isomorphism on relative cohomology when `B` is contractible: both components are homotopy
equivalences (`Work.Thom.isIso_homologyMap_dualChainMap_prodSnd` for the total space and
`Work.Thom.subtypeProj_relMapSub` for the punctured subspace), so the five lemma
`Work.Thom.isIso_homologyMap_relComplexMap` applies.  (Note the contravariance: `relComplexMap` goes
`C^*(ℝⁿ, ℝⁿ∖0) ⟶ C^*(B × ℝⁿ, B × (ℝⁿ∖0))`; the isomorphism below is therefore the `symm` of the
map induced on cohomology.) -/
theorem relComplexMap_prodSnd_isIso (B : Type) [TopologicalSpace B] [ContractibleSpace B]
    (n : ℕ) (k : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap ℤ
      (X₁ := TopCat.of (B × EuclideanSpace ℝ (Fin n)))
      (X₂ := TopCat.of (EuclideanSpace ℝ (Fin n)))
      {p : B × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0}
      {v : EuclideanSpace ℝ (Fin n) | v ≠ 0}
      (TopCat.ofHom (prodSnd B (EuclideanSpace ℝ (Fin n)))) (fun x hx => hx)) k) := by
  have hf : ∀ m, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.dualChainMap ℤ (TopCat.of (B × EuclideanSpace ℝ (Fin n))) (TopCat.of (EuclideanSpace ℝ (Fin n)))
        (TopCat.ofHom (prodSnd B (EuclideanSpace ℝ (Fin n))))) m) :=
    fun m => isIso_homologyMap_dualChainMap_prodSnd (Z := EuclideanSpace ℝ (Fin n)) ℤ m
  have hg : ∀ m, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.dualChainMap ℤ (TopCat.of {p : B × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0})
        (TopCat.of {v : EuclideanSpace ℝ (Fin n) | v ≠ 0})
        (Work.Cohomology.relMapSub (X₁ := TopCat.of (B × EuclideanSpace ℝ (Fin n))) (X₂ := TopCat.of (EuclideanSpace ℝ (Fin n)))
          {p : B × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0} {v : EuclideanSpace ℝ (Fin n) | v ≠ 0}
          (TopCat.ofHom (prodSnd B (EuclideanSpace ℝ (Fin n)))) (fun x hx => hx))) m) :=
    fun m => subtypeProj_relMapSub (B := B) (Z := EuclideanSpace ℝ (Fin n)) {v : EuclideanSpace ℝ (Fin n) | v ≠ 0} ℤ m
  exact isIso_homologyMap_relComplexMap (X₁ := TopCat.of (B × EuclideanSpace ℝ (Fin n))) (X₂ := TopCat.of (EuclideanSpace ℝ (Fin n)))
    {p : B × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0} {v : EuclideanSpace ℝ (Fin n) | v ≠ 0}
    (TopCat.ofHom (prodSnd B (EuclideanSpace ℝ (Fin n)))) (fun x hx => hx) ℤ hf hg k

/-- **A contractible factor does not change relative cohomology.**  For a contractible space `B`
the second projection `(B × ℝⁿ, B × (ℝⁿ∖0)) → (ℝⁿ, ℝⁿ∖0)` is a homotopy equivalence of pairs, so it
induces an isomorphism of relative cohomology: `RelCoh ℤ k (B × ℝⁿ) (B × (ℝⁿ∖0)) ≅
RelCoh ℤ k ℝⁿ (ℝⁿ∖0)`.  This is the *induction step* of the Thom isomorphism for the trivial bundle
over a contractible base (a cell): it reduces the pair cohomology of the trivial bundle over `B` to
the pair cohomology of `(ℝⁿ, ℝⁿ∖0)`, which is computed in
`Work.Thom.relCohomology_euclidean_punctured`.
-/
theorem relCohomology_prod_contractible (B : Type) [TopologicalSpace B] [ContractibleSpace B]
    (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    Nonempty (Work.Thom.RelCoh ℤ k (B × EuclideanSpace ℝ (Fin n))
      {p : B × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0} ≅
      Work.Thom.RelCoh ℤ k (EuclideanSpace ℝ (Fin n))
        {v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) := by
  haveI : CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap ℤ
      (X₁ := TopCat.of (B × EuclideanSpace ℝ (Fin n)))
      (X₂ := TopCat.of (EuclideanSpace ℝ (Fin n)))
      {p : B × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0}
      {v : EuclideanSpace ℝ (Fin n) | v ≠ 0}
      (TopCat.ofHom (prodSnd B (EuclideanSpace ℝ (Fin n)))) (fun x hx => hx)) k) :=
    relComplexMap_prodSnd_isIso B n k
  exact ⟨(CategoryTheory.asIso (HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap ℤ
    (X₁ := TopCat.of (B × EuclideanSpace ℝ (Fin n)))
    (X₂ := TopCat.of (EuclideanSpace ℝ (Fin n)))
    {p : B × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0}
    {v : EuclideanSpace ℝ (Fin n) | v ≠ 0}
    (TopCat.ofHom (prodSnd B (EuclideanSpace ℝ (Fin n)))) (fun x hx => hx)) k)).symm⟩

end

end Work.Thom
