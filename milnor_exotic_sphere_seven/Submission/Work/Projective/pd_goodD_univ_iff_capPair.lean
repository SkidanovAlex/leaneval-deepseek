import Mathlib
import Submission.Work.Cohomology.pd_middleDegree_of_good
import Submission.Work.Cohomology.pd_goodD_natural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.Projective

open Work.Cohomology

/-- Bijectivity of a map `L` is equivalent to bijectivity of a map `R` when the two are related
through a commuting square `Ψ ∘ L = R ∘ Φ` whose vertical maps `Φ`, `Ψ` are bijections. -/
private theorem bijective_iff_of_comm {X₁ Y₁ X₂ Y₂ : Type*}
    (L : X₁ → Y₁) (R : X₂ → Y₂) (Φ : X₁ → X₂) (Ψ : Y₁ → Y₂)
    (Φ' : X₂ → X₁) (Ψ' : Y₂ → Y₁)
    (hΦ : Function.LeftInverse Φ' Φ) (hΦ' : Function.RightInverse Φ' Φ)
    (hΨ : Function.LeftInverse Ψ' Ψ) (hΨ' : Function.RightInverse Ψ' Ψ)
    (h : ∀ x, Ψ (L x) = R (Φ x)) :
    Function.Bijective L ↔ Function.Bijective R := by
  have hΦb : Function.Bijective Φ := ⟨hΦ.injective, hΦ'.surjective⟩
  have hΦ'b : Function.Bijective Φ' := ⟨hΦ'.injective, hΦ.surjective⟩
  have hΨb : Function.Bijective Ψ := ⟨hΨ.injective, hΨ'.surjective⟩
  have hΨ'b : Function.Bijective Ψ' := ⟨hΨ'.injective, hΨ.surjective⟩
  constructor
  · intro hL
    have hR : R = fun y => Ψ (L (Φ' y)) := by
      funext y
      exact (congrArg R (hΦ' y).symm).trans (h (Φ' y)).symm
    rw [hR]
    exact hΨb.comp (hL.comp hΦ'b)
  · intro hR
    have hL : L = fun x => Ψ' (R (Φ x)) := by
      funext x
      exact (hΨ (L x)).symm.trans (congrArg Ψ' (h x))
    rw [hL]
    exact hΨ'b.comp (hR.comp hΦb)

/-- **The duality map of the `Good` framework at the whole space, in terms of the cap product.**

For `k + m = N` and `c ∈ H_N(M;ℤ)` the duality map `x ↦ x ⌢ μ_{M}` of the pair
`(M, M∖M) = (M,∅)` is bijective if and only if the absolute cap product `y ↦ y ⌢ c` is.  The two
are related by the isomorphism of pairs `(M,∅) ≅ (M,M)` given by the canonical homeomorphism
`M ≅ {x // x ∈ Set.univ}` and by the identification `C^*(M,∅) ≅ C^*(M)`. -/
theorem pd_goodD_univ_iff_capPair_gen {M : TopCat} [CompactSpace M] [T2Space M]
    (k m N : ℕ) (hkm : k + m = N) (c : (Work.Cohomology.singularChains ℤ M).homology N) :
    Function.Bijective (fun x : (Work.Cohomology.relComplex ℤ (TopCat.of (Set.univ : Set M))
        (Work.Cohomology.pdRelSub (Set.univ : Set M) Set.univ)).homology k =>
      Work.Cohomology.goodD N c Set.univ isOpen_univ Set.univ (Set.subset_univ Set.univ)
        isCompact_univ k m hkm x)
    ↔ Function.Bijective (fun y : (Work.Cohomology.singularCochainComplex ℤ M).homology k =>
        (Work.Cohomology.capPair ℤ (TopCat.toSSet.obj M) k m) y (hkm ▸ c)) := by
  subst hkm
  let U : Set M := Set.univ
  let A : Set M := (Set.univ : Set M)ᶜ
  let S : Set (TopCat.of U) := pdRelSub U U
  let f : TopCat.of U ⟶ M := subtypeIncl M U
  have hfA : ∀ x ∈ S, f x ∈ A := fun x hx => hx
  let fst : (relComplex ℤ M A).homology k → (relComplex ℤ (TopCat.of U) S).homology k :=
    fun a => (HomologicalComplex.homologyMap (relComplexMap ℤ S A f hfA) k).hom a
  let inc : (relComplex ℤ M A).homology k → (singularCochainComplex ℤ M).homology k :=
    fun a => (HomologicalComplex.homologyMap (relIncl ℤ M A) k).hom a
  let Ψ : (singularChains ℤ (TopCat.of U)).homology m → (singularChains ℤ M).homology m :=
    fun z => (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of U) M f) m).hom z
  haveI hfstIso : IsIso (HomologicalComplex.homologyMap (relComplexMap ℤ S A f hfA) k) :=
    pdmd_relComplexMap_iso_of_isIso_pairs S A f hfA (pdmd_univIncl M) (fun y hy => hy)
      (pdmd_subtypeIncl_univ_univIncl M) (pdmd_univIncl_subtypeIncl_univ M) k
  haveI hincIso : IsIso (HomologicalComplex.homologyMap (relIncl ℤ M A) k) := by
    haveI : IsEmpty (↥A) := ⟨fun x => x.2 trivial⟩
    haveI : IsIso (relIncl ℤ M A) := isIso_relIncl_of_isEmpty M A
    exact Functor.map_isIso
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) k) (relIncl ℤ M A)
  let fst' : (relComplex ℤ (TopCat.of U) S).homology k → (relComplex ℤ M A).homology k :=
    fun x => (inv (HomologicalComplex.homologyMap (relComplexMap ℤ S A f hfA) k)).hom x
  let inc' : (singularCochainComplex ℤ M).homology k → (relComplex ℤ M A).homology k :=
    fun y => (inv (HomologicalComplex.homologyMap (relIncl ℤ M A) k)).hom y
  let L : (relComplex ℤ (TopCat.of U) S).homology k → (singularChains ℤ (TopCat.of U)).homology m :=
    fun x => goodD (k + m) c U isOpen_univ U (Set.subset_univ U) isCompact_univ k m rfl x
  let R : (singularCochainComplex ℤ M).homology k → (singularChains ℤ M).homology m :=
    fun y => (capPair ℤ (TopCat.toSSet.obj M) k m) y c
  let Φ : (relComplex ℤ (TopCat.of U) S).homology k → (singularCochainComplex ℤ M).homology k :=
    fun x => inc (fst' x)
  let Φ' : (singularCochainComplex ℤ M).homology k → (relComplex ℤ (TopCat.of U) S).homology k :=
    fun y => fst (inc' y)
  let Ψ' : (singularChains ℤ M).homology m → (singularChains ℤ (TopCat.of U)).homology m :=
    fun z => (HomologicalComplex.homologyMap (chainMap ℤ M (TopCat.of U) (pdmd_univIncl M)) m).hom z
  have hΦ_left : Function.LeftInverse Φ' Φ := fun x => by
    change (HomologicalComplex.homologyMap (relComplexMap ℤ S A f hfA) k).hom
      ((inv (HomologicalComplex.homologyMap (relIncl ℤ M A) k)).hom
        ((HomologicalComplex.homologyMap (relIncl ℤ M A) k).hom
          ((inv (HomologicalComplex.homologyMap (relComplexMap ℤ S A f hfA) k)).hom x))) = x
    rw [IsIso.hom_inv_id_apply (HomologicalComplex.homologyMap (relIncl ℤ M A) k)
      ((inv (HomologicalComplex.homologyMap (relComplexMap ℤ S A f hfA) k)).hom x)]
    exact IsIso.inv_hom_id_apply (HomologicalComplex.homologyMap (relComplexMap ℤ S A f hfA) k) x
  have hΦ_right : Function.RightInverse Φ' Φ := fun y => by
    change (HomologicalComplex.homologyMap (relIncl ℤ M A) k).hom
      ((inv (HomologicalComplex.homologyMap (relComplexMap ℤ S A f hfA) k)).hom
        ((HomologicalComplex.homologyMap (relComplexMap ℤ S A f hfA) k).hom
          ((inv (HomologicalComplex.homologyMap (relIncl ℤ M A) k)).hom y))) = y
    rw [IsIso.hom_inv_id_apply (HomologicalComplex.homologyMap (relComplexMap ℤ S A f hfA) k)
      ((inv (HomologicalComplex.homologyMap (relIncl ℤ M A) k)).hom y)]
    exact IsIso.inv_hom_id_apply (HomologicalComplex.homologyMap (relIncl ℤ M A) k) y
  have hid1 : (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of U) M f) m)
      ≫ (HomologicalComplex.homologyMap (chainMap ℤ M (TopCat.of U) (pdmd_univIncl M)) m)
      = 𝟙 ((singularChains ℤ (TopCat.of U)).homology m) := by
    rw [← HomologicalComplex.homologyMap_comp,
      ← chainMap_comp' (TopCat.of U) M (TopCat.of U) f (pdmd_univIncl M),
      pdmd_subtypeIncl_univ_univIncl M, chainMap_id', HomologicalComplex.homologyMap_id]
  have hid2 : (HomologicalComplex.homologyMap (chainMap ℤ M (TopCat.of U) (pdmd_univIncl M)) m)
      ≫ (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of U) M f) m)
      = 𝟙 ((singularChains ℤ M).homology m) := by
    rw [← HomologicalComplex.homologyMap_comp,
      ← chainMap_comp' M (TopCat.of U) M (pdmd_univIncl M) f,
      pdmd_univIncl_subtypeIncl_univ M, chainMap_id', HomologicalComplex.homologyMap_id]
  have hΨ_left : Function.LeftInverse Ψ' Ψ := fun z => by
    have hz := ConcreteCategory.congr_hom hid1 z
    simpa [Ψ, Ψ'] using hz
  have hΨ_right : Function.RightInverse Ψ' Ψ := fun z => by
    have hz := ConcreteCategory.congr_hom hid2 z
    simpa [Ψ, Ψ'] using hz
  let μ : (relChains (TopCat.of U) S).homology (k + m) :=
    localFundClass (k + m) c U isOpen_univ U (Set.subset_univ U) isCompact_univ
  have hpush : (HomologicalComplex.homologyMap (relChainsMapOf (TopCat.of U) M S A f
      (relMapSub S A f hfA) (relMapSub_spec S A f hfA)) (k + m)).hom μ
      = relLocClass M (k + m) c U := by
    rw [pdmd_relChainsMapOf_relMapSub_eq_relChainsMap M U A hfA]
    exact localFundClass_spec (k + m) c U isOpen_univ U (Set.subset_univ U) isCompact_univ
  have hrelLoc : relLocClass M (k + m) c U
      = (HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (inclChains M A)) (k + m)).hom c := by
    rw [relLocClass]
  have hcomm : ∀ x : (relComplex ℤ (TopCat.of U) S).homology k, Ψ (L x) = R (Φ x) := by
    intro x
    have hx : (HomologicalComplex.homologyMap (relComplexMap ℤ S A f hfA) k).hom (fst' x) = x :=
      IsIso.inv_hom_id_apply _ x
    have hnat := Crux.relCapPair_natural S A f hfA k m (fst' x) μ
    rw [hpush, hrelLoc, relCapPair_abs_eq_capPair M A k m (fst' x) c] at hnat
    rw [hx] at hnat
    show (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of U) M f) m).hom
        (relCapPair (TopCat.of U) S k m x μ)
      = (capPair ℤ (TopCat.toSSet.obj M) k m)
          ((HomologicalComplex.homologyMap (relIncl ℤ M A) k).hom (fst' x)) c
    exact hnat
  exact bijective_iff_of_comm L R Φ Ψ Φ' Ψ' hΦ_left hΦ_right hΨ_left hΨ_right hcomm

-- WARNING: do NOT use `Good`, `cp2_good_univ_direct`, `cp2_good_univ`, `cp2SelfIntersection_pm_one_uncond`,
-- `cp2SelfIntersection_eq_pm_one`, `pd_good_univ` or `pd_good_union` (they are sorry/conditional).
-- The proof must be pure structural homological algebra, and `#print axioms` must show no `sorryAx`.
theorem pd_goodD_univ_iff_capPair {M : TopCat} [CompactSpace M] [T2Space M]
    (k m : ℕ) (hkm : k + m = 4) (c : (Work.Cohomology.singularChains ℤ M).homology 4) :
    Function.Bijective (fun x : (Work.Cohomology.relComplex ℤ (TopCat.of (Set.univ : Set M))
        (Work.Cohomology.pdRelSub (Set.univ : Set M) Set.univ)).homology k =>
      Work.Cohomology.goodD 4 c Set.univ isOpen_univ Set.univ (Set.subset_univ Set.univ)
        isCompact_univ k m hkm x)
    ↔ Function.Bijective (fun y : (Work.Cohomology.singularCochainComplex ℤ M).homology k =>
        (Work.Cohomology.capPair ℤ (TopCat.toSSet.obj M) k m) y (hkm ▸ c)) :=
  pd_goodD_univ_iff_capPair_gen k m 4 hkm c

end Work.Projective
