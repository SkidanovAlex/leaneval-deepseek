import Mathlib
import Submission.Work.Tubular.tubeHalfOrientation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Excision for the tubular neighbourhood, in the natural form

This file proves `Work.Tubular.tubeExcisionNat`: for a tubular chart `C : TubeChart E ε` of the
normal bundle of an embedding `E : V ↪ ℝ^{8+k}`,

* **topological part.**  For `K ⊆ D_ε(ν)` of norm `< ε` and compact, the inclusion of pairs
  `(U_ε, U_ε ∖ K') → (ℝ^N, ℝ^N ∖ K')`, with `K' = tubeImage K`, is an isomorphism on homology in
  degree `N = 8 + k`.  Here `U_ε = openTubeSet E ε` is the open tube and `K'` is closed (it is the
  continuous image of the compact `K`), so this is the excision statement
  `Work.Cohomology.excision_relChainsMap_isIso` for the cover `U_ε ∪ (K')ᶜ = ℝ^N`.

* **naturality.**  The excision maps are compatible with the restriction maps
  `relCokerMap` induced on the relative sets by an inclusion `K ⊆ K'` of the compact pieces.  This
  is a purely formal consequence of the definitions of `relChainsMap` and `relCokerMap` as
  `cokernel.map`s, so it is proved from `cokernel_π_map` and `relCokerMap_comp_π` by cancelling the
  epimorphism `cokernel.π`.

The naturality half is stated for arbitrary topological spaces as
`Work.Tubular.relChainsMapOf_relCokerMap`, since it has nothing to do with tubular neighbourhoods.
-/

set_option maxHeartbeats 2000000

namespace Work.Tubular

open scoped Topology
open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ} [NeZero k] {ε : ℝ}

/-! ## The comparison of `relChainsMap` with `relCokerMap` -/

/-- The compatibility of `relChainsMapOf` with the projection onto the relative chain complex. -/
theorem cokernel_π_relChainsMapOf (X Y : TopCat) (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (g : TopCat.of A ⟶ TopCat.of B)
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B) :
    cokernel.π (Work.Cohomology.inclChains X A)
        ≫ Work.Cohomology.relChainsMapOf X Y A B f g w
      = Work.Cohomology.chainMap ℤ X Y f ≫ cokernel.π (Work.Cohomology.inclChains Y B) := by
  rw [Work.Cohomology.relChainsMapOf]
  exact Work.Cohomology.cokernel_π_map _ _ _ _ _

/-- **Naturality of a map of relative chain complexes in the relative set.**

A map of pairs `(f, g) : (X, A) → (Y, B)` and an inclusion `A ⊆ A'` of relative sets (with any
convenient `g'` on the larger set) give a commutative square comparing the induced maps
`relChains X A → relChains Y B` and `relChains X A' → relChains Y B'` through the restriction maps
`relCokerMap`.

Both sides are maps out of `relChains X A = cokernel (inclChains X A)`, so it suffices to compare
the composites with the epimorphism `cokernel.π (inclChains X A)`; this is
`cokernel_π_relChainsMapOf` on both squares and `relCokerMap_comp_π` on the vertical maps. -/
theorem relChainsMapOf_relCokerMap (X Y : TopCat) (A A' : Set X) (B B' : Set Y)
    (hA : A ⊆ A') (hB : B ⊆ B') (f : X ⟶ Y) (g : TopCat.of A ⟶ TopCat.of B)
    (g' : TopCat.of A' ⟶ TopCat.of B')
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B)
    (w' : Work.Cohomology.subtypeIncl X A' ≫ f = g' ≫ Work.Cohomology.subtypeIncl Y B') :
    Work.Cohomology.relChainsMapOf X Y A B f g w ≫ Work.Cohomology.relCokerMap Y B B' hB
      = Work.Cohomology.relCokerMap X A A' hA
        ≫ Work.Cohomology.relChainsMapOf X Y A' B' f g' w' := by
  apply (cancel_epi (cokernel.π (Work.Cohomology.inclChains X A))).mp
  have h₁ : cokernel.π (Work.Cohomology.inclChains X A)
        ≫ Work.Cohomology.relChainsMapOf X Y A B f g w
      = Work.Cohomology.chainMap ℤ X Y f ≫ cokernel.π (Work.Cohomology.inclChains Y B) :=
    cokernel_π_relChainsMapOf X Y A B f g w
  have h₂ : cokernel.π (Work.Cohomology.inclChains X A)
        ≫ Work.Cohomology.relCokerMap X A A' hA
      = cokernel.π (Work.Cohomology.inclChains X A') :=
    Work.Cohomology.relCokerMap_comp_π X A A' hA
  have h₃ : cokernel.π (Work.Cohomology.inclChains Y B)
        ≫ Work.Cohomology.relCokerMap Y B B' hB
      = cokernel.π (Work.Cohomology.inclChains Y B') :=
    Work.Cohomology.relCokerMap_comp_π Y B B' hB
  have h₄ : cokernel.π (Work.Cohomology.inclChains X A')
        ≫ Work.Cohomology.relChainsMapOf X Y A' B' f g' w'
      = Work.Cohomology.chainMap ℤ X Y f ≫ cokernel.π (Work.Cohomology.inclChains Y B') :=
    cokernel_π_relChainsMapOf X Y A' B' f g' w'
  have key : cokernel.π (Work.Cohomology.inclChains X A)
        ≫ (Work.Cohomology.relChainsMapOf X Y A B f g w
            ≫ Work.Cohomology.relCokerMap Y B B' hB)
      = Work.Cohomology.chainMap ℤ X Y f
        ≫ cokernel.π (Work.Cohomology.inclChains Y B') :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ Work.Cohomology.relCokerMap Y B B' hB) h₁).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun t => Work.Cohomology.chainMap ℤ X Y f ≫ t) h₃)))
  have key₂ : cokernel.π (Work.Cohomology.inclChains X A)
        ≫ (Work.Cohomology.relCokerMap X A A' hA
            ≫ Work.Cohomology.relChainsMapOf X Y A' B' f g' w')
      = Work.Cohomology.chainMap ℤ X Y f
        ≫ cokernel.π (Work.Cohomology.inclChains Y B') :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ Work.Cohomology.relChainsMapOf X Y A' B' f g' w') h₂).trans h₄)
  exact key.trans key₂.symm

/-! ## The tubular form -/

/-- `excisionMap K` is, definitionally, the inclusion of pairs
`(U_ε, U_ε ∖ K') → (ℝ^N, ℝ^N ∖ K')`, with `K' = tubeImage K`. -/
theorem excisionMap_eq_relChainsMap {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (K : Set (NormalDiscSub E ε)) :
    excisionMap (E := E) K
      = Work.Cohomology.relChainsMap (TopCat.of (Euc (8 + k))) (openTubeSet E ε)
          ((tubeImage (E := E) K)ᶜ) := rfl

/-- **Excision for a compact piece of the disc bundle.**  If every point of `K` has normal norm
`< ε` and `K` is compact, then the inclusion of pairs `(U_ε, U_ε∖K') → (ℝ^N, ℝ^N∖K')` is an
isomorphism on homology in degree `N = 8 + k`.

The piece `K' = tubeImage K` is compact, hence closed, and it is contained in the open tube `U_ε`;
so `U_ε` and `(K')ᶜ` are open sets covering `ℝ^N`, and the claim is
`Work.Cohomology.excision_relChainsMap_isIso`. -/
theorem isIso_excisionMap_homologyMap
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (C : TubeChart E ε) {K : Set (NormalDiscSub E ε)}
    (hK : ∀ q ∈ K, normalNorm E (q : NormalTotal E) < ε) (hKc : IsCompact K) :
    IsIso (HomologicalComplex.homologyMap (excisionMap (E := E) K) (8 + k)) := by
  have hU : IsOpen (openTubeSet E ε) := C.isOpen_openTube
  have hcont : Continuous (fun q : NormalDiscSub E ε => tubeMap E (q : NormalTotal E)) :=
    (continuous_tubeMap E).comp continuous_subtype_val
  have hclosed : IsClosed (tubeImage (E := E) K) := (hKc.image hcont).isClosed
  have hcov : openTubeSet E ε ∪ (tubeImage (E := E) K)ᶜ = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro y
    by_cases hy : y ∈ tubeImage (E := E) K
    · exact Or.inl (tubeImage_subset_openTube C hK hy)
    · exact Or.inr hy
  exact Work.Cohomology.excision_relChainsMap_isIso _ _ _ hU hclosed.isOpen_compl hcov _

/-- **Naturality of the excision map in the compact piece.**  For `K ⊆ K'` inside the open disc
bundle, the two ways of going from `(U_ε, U_ε∖K'')` to `(ℝ^N, ℝ^N∖K')` — first restrict the
relative set on the ambient side, or first restrict on the tube side and then excise — agree. -/
theorem excisionMap_relCokerMap
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    {K K' : Set (NormalDiscSub E ε)} (h : K ⊆ K') :
    excisionMap (E := E) K' ≫ Work.Cohomology.relCokerMap (TopCat.of (Euc (8 + k)))
          (tubeImage (E := E) K')ᶜ (tubeImage (E := E) K)ᶜ
          (fun y hy hc => hy (by
            rcases hc with ⟨q, hq, hqe⟩
            exact ⟨q, h hq, hqe⟩))
      = Work.Cohomology.relCokerMap (TopCat.of ↥(openTubeSet E ε))
            (tubeRelSub (E := E) K') (tubeRelSub (E := E) K)
            (fun y hy hyy => hy (by
              rcases hyy with ⟨q, hq, hqe⟩
              exact ⟨q, h hq, hqe⟩))
          ≫ excisionMap (E := E) K := by
  apply (cancel_epi (cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(openTubeSet E ε))
    (tubeRelSub (E := E) K')))).mp
  have h₁ : cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(openTubeSet E ε))
        (tubeRelSub (E := E) K')) ≫ excisionMap (E := E) K'
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(openTubeSet E ε)) (TopCat.of (Euc (8 + k)))
          (Work.Cohomology.subtypeIncl (TopCat.of (Euc (8 + k))) (openTubeSet E ε))
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (Euc (8 + k)))
            ((tubeImage (E := E) K')ᶜ)) := by
    rw [show excisionMap (E := E) K'
        = Work.Cohomology.relChainsMap (TopCat.of (Euc (8 + k))) (openTubeSet E ε)
            ((tubeImage (E := E) K')ᶜ) from rfl]
    exact Work.Cohomology.cokernel_π_relChainsMap (TopCat.of (Euc (8 + k))) (openTubeSet E ε)
      ((tubeImage (E := E) K')ᶜ)
  have h₂ : cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(openTubeSet E ε))
        (tubeRelSub (E := E) K'))
      ≫ Work.Cohomology.relCokerMap (TopCat.of ↥(openTubeSet E ε))
          (tubeRelSub (E := E) K') (tubeRelSub (E := E) K)
          (fun y hy hyy => hy (by
            rcases hyy with ⟨q, hq, hqe⟩
            exact ⟨q, h hq, hqe⟩))
      = cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(openTubeSet E ε))
          (tubeRelSub (E := E) K)) :=
    Work.Cohomology.relCokerMap_comp_π _ _ _ _
  have h₃ : cokernel.π (Work.Cohomology.inclChains (TopCat.of (Euc (8 + k)))
        ((tubeImage (E := E) K')ᶜ))
      ≫ Work.Cohomology.relCokerMap (TopCat.of (Euc (8 + k)))
          (tubeImage (E := E) K')ᶜ (tubeImage (E := E) K)ᶜ
          (fun y hy hc => hy (by
            rcases hc with ⟨q, hq, hqe⟩
            exact ⟨q, h hq, hqe⟩))
      = cokernel.π (Work.Cohomology.inclChains (TopCat.of (Euc (8 + k)))
          ((tubeImage (E := E) K)ᶜ)) :=
    Work.Cohomology.relCokerMap_comp_π _ _ _ _
  have h₄ : cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(openTubeSet E ε))
        (tubeRelSub (E := E) K)) ≫ excisionMap (E := E) K
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(openTubeSet E ε)) (TopCat.of (Euc (8 + k)))
          (Work.Cohomology.subtypeIncl (TopCat.of (Euc (8 + k))) (openTubeSet E ε))
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (Euc (8 + k)))
            ((tubeImage (E := E) K)ᶜ)) := by
    rw [show excisionMap (E := E) K
        = Work.Cohomology.relChainsMap (TopCat.of (Euc (8 + k))) (openTubeSet E ε)
            ((tubeImage (E := E) K)ᶜ) from rfl]
    exact Work.Cohomology.cokernel_π_relChainsMap (TopCat.of (Euc (8 + k))) (openTubeSet E ε)
      ((tubeImage (E := E) K)ᶜ)
  have key : cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(openTubeSet E ε))
          (tubeRelSub (E := E) K'))
        ≫ (excisionMap (E := E) K' ≫ Work.Cohomology.relCokerMap (TopCat.of (Euc (8 + k)))
            (tubeImage (E := E) K')ᶜ (tubeImage (E := E) K)ᶜ
            (fun y hy hc => hy (by
              rcases hc with ⟨q, hq, hqe⟩
              exact ⟨q, h hq, hqe⟩)))
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(openTubeSet E ε)) (TopCat.of (Euc (8 + k)))
          (Work.Cohomology.subtypeIncl (TopCat.of (Euc (8 + k))) (openTubeSet E ε))
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (Euc (8 + k)))
            ((tubeImage (E := E) K)ᶜ)) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ Work.Cohomology.relCokerMap (TopCat.of (Euc (8 + k)))
            (tubeImage (E := E) K')ᶜ (tubeImage (E := E) K)ᶜ
            (fun y hy hc => hy (by
              rcases hc with ⟨q, hq, hqe⟩
              exact ⟨q, h hq, hqe⟩))) h₁).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun t => Work.Cohomology.chainMap ℤ (TopCat.of ↥(openTubeSet E ε))
              (TopCat.of (Euc (8 + k)))
              (Work.Cohomology.subtypeIncl (TopCat.of (Euc (8 + k))) (openTubeSet E ε)) ≫ t)
            h₃)))
  have key₂ : cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(openTubeSet E ε))
          (tubeRelSub (E := E) K'))
        ≫ (Work.Cohomology.relCokerMap (TopCat.of ↥(openTubeSet E ε))
              (tubeRelSub (E := E) K') (tubeRelSub (E := E) K)
              (fun y hy hyy => hy (by
                rcases hyy with ⟨q, hq, hqe⟩
                exact ⟨q, h hq, hqe⟩))
            ≫ excisionMap (E := E) K)
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(openTubeSet E ε)) (TopCat.of (Euc (8 + k)))
          (Work.Cohomology.subtypeIncl (TopCat.of (Euc (8 + k))) (openTubeSet E ε))
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (Euc (8 + k)))
            ((tubeImage (E := E) K)ᶜ)) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ excisionMap (E := E) K) h₂).trans h₄)
  exact key.trans key₂.symm

/-- **Excision for the tubular neighbourhood, with its naturality.** -/
theorem tubeExcisionNat {V : Work.ThomBordism.Man8} {k : ℕ} [NeZero k] {ε : ℝ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (C : Work.Tubular.TubeChart E ε) :
    (∀ K : Set (Work.Tubular.NormalDiscSub E ε),
        (∀ q ∈ K, Work.Tubular.normalNorm E (q : Work.Tubular.NormalTotal E) < ε) →
        IsCompact K →
        CategoryTheory.IsIso (HomologicalComplex.homologyMap
          (Work.Tubular.excisionMap (E := E) K) (8 + k))) ∧
    (∀ (K K' : Set (Work.Tubular.NormalDiscSub E ε)) (h : K ⊆ K'),
        CategoryTheory.CategoryStruct.comp (Work.Tubular.excisionMap (E := E) K')
          (Work.Cohomology.relCokerMap
            (TopCat.of (Work.Tubular.Euc (8 + k)))
            (Work.Tubular.tubeImage (E := E) K')ᶜ (Work.Tubular.tubeImage (E := E) K)ᶜ
            (fun y hy hc => hy (by
              rcases hc with ⟨q, hq, hqe⟩
              exact ⟨q, h hq, hqe⟩))
          ) = CategoryTheory.CategoryStruct.comp (Work.Cohomology.relCokerMap
              (TopCat.of ↥(Work.Tubular.openTubeSet E ε))
              (Work.Tubular.tubeRelSub (E := E) K') (Work.Tubular.tubeRelSub (E := E) K)
              (fun y hy hyy => hy (by
                rcases hyy with ⟨q, hq, hqe⟩
                exact ⟨q, h hq, hqe⟩))
            ) (Work.Tubular.excisionMap (E := E) K)) :=
  ⟨fun K hK hKc => isIso_excisionMap_homologyMap C hK hKc,
   fun K K' h => excisionMap_relCokerMap (E := E) h⟩

end

end Work.Tubular
