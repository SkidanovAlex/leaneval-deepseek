import Mathlib
import Submission.Work.Cohomology.sphere3DiscPairDefs
import Submission.Work.Cohomology.RelCapHTransfer
import Submission.Work.Cohomology.Crux.vkOvlDefs
import Submission.Work.Cohomology.Crux.vkInternalTransgression
-- Re-routed (Islands subproject, 2026): `Crux/vkCruxRestr.lean` and
-- `Crux/ovlRestrictionSurjective.lean` declare the same names (likewise `vkCruxCompat` and
-- `ovlRestrSurjCompat`), so they cannot be imported together.  The rest of the workspace uses
-- the `ovl` copies; this file used the `vk` ones.  The declarations it uses from
-- `vkCruxCompat` (`ovlRestrSurjCompat` and friends) have the identical statements in
-- `ovlRestrSurjCompat`, which is what we import now.
import Submission.Work.Cohomology.Crux.ovlRestrSurjCompat
import Submission.Work.Cohomology.Crux.ovlPairModelDefs
import Submission.Work.Cohomology.Crux.relComplexMapHomologyIsoCompat
import Submission.Work.Cohomology.Crux.relCapPair_natural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology

namespace Work.Cohomology.Crux

noncomputable section

/-- The restriction of relative cohomology to the overlap of the two charts of `Vk (-2)`, as the
linear map `H⁴(Vk(-2), Mk(-2)) →ₗ H⁴(U ∩ V, (U ∩ V) ∩ Mk(-2))` of the transgression identity. -/
abbrev ovlRestr := ModuleCat.Hom.hom (HomologicalComplex.homologyMap
    (relComplexMap ℤ vkOvlA vkPairA
      (subtypeIncl vkPairX (vkU ∩ vkV)) (fun _ hx => hx)) 4)

/-- The comparison map `(U ∩ V, (U ∩ V) ∩ Mk(-2)) ⟶ (S³ × D⁴, S³ × S³)` is an isomorphism on the
relative cohomology in degree `4`.  This is the compatible replacement of
`overlapModelTransfer_relCochainIso` (which goes through the `ℤ`-dual of the relative chains). -/
theorem overlapModelTransferCompat_relCochainIso :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (relComplexMap ℤ vkOvlA PairAT ovlPairMap ovlPairMap_mem) 4) := by
  let A : Set ↥vkOvl := vkOvlA
  let B : Set ↥PairXT := PairAT
  let h : ∀ x ∈ A, ovlPairMap x ∈ B := ovlPairMap_mem
  have hf' : ∀ k, CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (chainMap ℤ vkOvl PairXT ovlPairMap) k) :=
    ovlPairMap_chainMap_isIso
  have hg' : ∀ k, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (chainMap ℤ (TopCat.of A) (TopCat.of B) (relMapSub A B ovlPairMap h)) k) :=
    ovlPairMapA_chainMap_isIso
  exact relComplexMapHomologyIsoCompat A B ovlPairMap h 4 hf' hg'

/-- The comparison map is a quasi-isomorphism of relative chain complexes in degree `7`. -/
theorem overlapModelTransferCompat_relChainIso :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (relChainsMapOf vkOvl PairXT vkOvlA PairAT ovlPairMap
        (relMapSub vkOvlA PairAT ovlPairMap ovlPairMap_mem)
        (relMapSub_spec vkOvlA PairAT ovlPairMap ovlPairMap_mem)) 7) := by
  let A : Set ↥vkOvl := vkOvlA
  let B : Set ↥PairXT := PairAT
  let g : TopCat.of A ⟶ TopCat.of B := relMapSub vkOvlA PairAT ovlPairMap ovlPairMap_mem
  let w : subtypeIncl vkOvl A ≫ ovlPairMap = g ≫ subtypeIncl PairXT B :=
    relMapSub_spec vkOvlA PairAT ovlPairMap ovlPairMap_mem
  have hf' : ∀ k, CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (chainMap ℤ vkOvl PairXT ovlPairMap) k) :=
    ovlPairMap_chainMap_isIso
  have hg' : ∀ k, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (chainMap ℤ (TopCat.of A) (TopCat.of B) g) k) :=
    ovlPairMapA_chainMap_isIso
  exact relChainsMapOf_isIso A B ovlPairMap g w 7 hf' hg'

/-- **The overlap of the two charts of `Vk (-2)` is modelled by `(S³ × D⁴, S³ × S³)`.**

The homotopy equivalence of pairs `(U ∩ V, (U ∩ V) ∩ Mk(-2)) ≃ (S³ × D⁴, S³ × S³)` built in
`Work.Cohomology.Crux.ovlPairModelDefs` identifies the relative cap products up to sign: `Ψ₁` is the
inverse of the pullback on relative cohomology, `Ψ₂` the pushforward on relative homology and `Ψ₃`
the pushforward on absolute homology, and the naturality of the relative cap product under a map of
pairs (`Work.Cohomology.Crux.relCapPair_natural`) gives the identity. -/
theorem overlapModelTransferCompat :
    ∃ (Ψ₁ : relCohomology ℤ vkOvl vkOvlA 4 ≃ₗ[ℤ] relCohomology ℤ PairXT PairAT 4)
      (Ψ₂ : (relChains vkOvl vkOvlA).homology 7 ≃ₗ[ℤ] (relChains PairXT PairAT).homology 7)
      (Ψ₃ : (singularChains ℤ vkOvl).homology 3 ≃ₗ[ℤ] (singularChains ℤ PairXT).homology 3),
      ∀ (a : relCohomology ℤ vkOvl vkOvlA 4) (c : (relChains vkOvl vkOvlA).homology 7),
        Ψ₃ (relCapPair vkOvl vkOvlA 4 3 a c)
            = relCapPair PairXT PairAT 4 3 (Ψ₁ a) (Ψ₂ c) ∨
        Ψ₃ (relCapPair vkOvl vkOvlA 4 3 a c)
            = - relCapPair PairXT PairAT 4 3 (Ψ₁ a) (Ψ₂ c) := by
  haveI h₁ : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (relComplexMap ℤ vkOvlA PairAT ovlPairMap ovlPairMap_mem) 4) :=
    overlapModelTransferCompat_relCochainIso
  haveI h₂ : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (relChainsMapOf vkOvl PairXT vkOvlA PairAT ovlPairMap
        (relMapSub vkOvlA PairAT ovlPairMap ovlPairMap_mem)
        (relMapSub_spec vkOvlA PairAT ovlPairMap ovlPairMap_mem)) 7) :=
    overlapModelTransferCompat_relChainIso
  haveI h₃ : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (chainMap ℤ vkOvl PairXT ovlPairMap) 3) := ovlPairMap_chainMap_isIso 3
  let Φ₁ := CategoryTheory.asIso (HomologicalComplex.homologyMap
    (relComplexMap ℤ vkOvlA PairAT ovlPairMap ovlPairMap_mem) 4)
  let Φ₂ := CategoryTheory.asIso (HomologicalComplex.homologyMap
    (relChainsMapOf vkOvl PairXT vkOvlA PairAT ovlPairMap
      (relMapSub vkOvlA PairAT ovlPairMap ovlPairMap_mem)
      (relMapSub_spec vkOvlA PairAT ovlPairMap ovlPairMap_mem)) 7)
  let Φ₃ := CategoryTheory.asIso (HomologicalComplex.homologyMap
    (chainMap ℤ vkOvl PairXT ovlPairMap) 3)
  refine ⟨Φ₁.toLinearEquiv.symm, Φ₂.toLinearEquiv, Φ₃.toLinearEquiv, ?_⟩
  intro a c
  have hnat := relCapPair_natural vkOvlA PairAT ovlPairMap ovlPairMap_mem 4 3
    (Φ₁.toLinearEquiv.symm a) c
  have hA : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (relComplexMap ℤ vkOvlA PairAT ovlPairMap ovlPairMap_mem) 4))
        (Φ₁.toLinearEquiv.symm a) = a := by
    show Φ₁.toLinearEquiv (Φ₁.toLinearEquiv.symm a) = a
    exact LinearEquiv.apply_symm_apply _ _
  rw [hA] at hnat
  have hB : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (relChainsMapOf vkOvl PairXT vkOvlA PairAT ovlPairMap
        (relMapSub vkOvlA PairAT ovlPairMap ovlPairMap_mem)
        (relMapSub_spec vkOvlA PairAT ovlPairMap ovlPairMap_mem)) 7)) c
      = Φ₂.toLinearEquiv c := by
    rw [Iso.toLinearEquiv_apply]
    rfl
  rw [hB] at hnat
  have hC : Φ₃.toLinearEquiv (relCapPair vkOvl vkOvlA 4 3 a c)
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (chainMap ℤ vkOvl PairXT ovlPairMap) 3))
        (relCapPair vkOvl vkOvlA 4 3 a c) := by
    rw [Iso.toLinearEquiv_apply]
    rfl
  left
  rw [hC]
  exact hnat

/-- **The Mayer--Vietoris transgression identity for the two-chart cover of `Vk (-2)`** (weak form).

`vkPairX = Vk(-2)` is the total space of Milnor's rank-`4` disc bundle over `S⁴`, `vkPairA =
Mk(-2)` its unit sphere bundle, and `vkOvl = U ∩ V`, `vkOvlA = (U ∩ V) ∩ Mk(-2)` their overlap,
modelled by `PairXT = S³ × D⁴` with `PairAT = S³ × S³`.  The maps `r`, `T` are the (surjective)
restriction and relative Mayer--Vietoris connecting map, and `U` the (injective) absolute
connecting map; the relative cap product is natural for them up to the harmless global sign. -/
theorem vk_transgression_cap_weak :
    ∃ (r : (Work.Cohomology.relCohomology ℤ Work.Cohomology.vkPairX Work.Cohomology.vkPairA 4)
            →ₗ[ℤ] (Work.Cohomology.relCohomology ℤ Work.Cohomology.PairXT Work.Cohomology.PairAT 4))
      (T : (Work.Cohomology.relChains Work.Cohomology.vkPairX Work.Cohomology.vkPairA).homology 8
            →ₗ[ℤ] (Work.Cohomology.relChains Work.Cohomology.PairXT Work.Cohomology.PairAT).homology 7)
      (U : (Work.Cohomology.singularChains ℤ Work.Cohomology.vkPairX).homology 4
            →ₗ[ℤ] (Work.Cohomology.singularChains ℤ Work.Cohomology.PairXT).homology 3),
      Function.Surjective r ∧ Function.Surjective T ∧ Function.Injective U ∧
      ∀ (a : Work.Cohomology.relCohomology ℤ Work.Cohomology.vkPairX Work.Cohomology.vkPairA 4)
        (c : (Work.Cohomology.relChains Work.Cohomology.vkPairX Work.Cohomology.vkPairA).homology 8),
        U (Work.Cohomology.relCapPair Work.Cohomology.vkPairX Work.Cohomology.vkPairA 4 4 a c)
            = Work.Cohomology.relCapPair Work.Cohomology.PairXT Work.Cohomology.PairAT 4 3 (r a) (T c) ∨
        U (Work.Cohomology.relCapPair Work.Cohomology.vkPairX Work.Cohomology.vkPairA 4 4 a c)
            = - Work.Cohomology.relCapPair Work.Cohomology.PairXT Work.Cohomology.PairAT 4 3 (r a) (T c) := by
  obtain ⟨T₀, U₀, hT, hU, hId⟩ := vkInternalTransgression
  obtain ⟨Ψ₁, Ψ₂, Ψ₃, hBid⟩ := overlapModelTransferCompat
  refine ⟨(Ψ₁ : _ →ₗ[ℤ] _).comp ovlRestr, (Ψ₂ : _ →ₗ[ℤ] _).comp T₀,
          (Ψ₃ : _ →ₗ[ℤ] _).comp U₀, ?_, ?_, ?_, ?_⟩
  · exact Ψ₁.surjective.comp ovlRestrSurjCompat
  · exact Ψ₂.surjective.comp hT
  · exact Ψ₃.injective.comp hU
  · intro a c
    -- the overlap restriction, as the two-turn map `Ψ₃ ∘ U₀`
    have hB := hBid (ovlRestr a) (T₀ c)
    rcases hId a c with h | h
    · rcases hB with h2 | h2
      · refine Or.inl ?_
        exact (congrArg (fun z => (Ψ₃ : (singularChains ℤ vkOvl).homology 3 →ₗ[ℤ]
          (singularChains ℤ PairXT).homology 3) z) h).trans h2
      · refine Or.inr ?_
        exact (congrArg (fun z => (Ψ₃ : (singularChains ℤ vkOvl).homology 3 →ₗ[ℤ]
          (singularChains ℤ PairXT).homology 3) z) h).trans h2
    · rcases hB with h2 | h2
      · refine Or.inr ?_
        refine ((congrArg (fun z => (Ψ₃ : (singularChains ℤ vkOvl).homology 3 →ₗ[ℤ]
          (singularChains ℤ PairXT).homology 3) z) h).trans ?_)
        rw [map_neg]
        exact congrArg Neg.neg h2
      · refine Or.inl ?_
        refine ((congrArg (fun z => (Ψ₃ : (singularChains ℤ vkOvl).homology 3 →ₗ[ℤ]
          (singularChains ℤ PairXT).homology 3) z) h).trans ?_)
        rw [map_neg]
        exact (congrArg Neg.neg h2).trans (neg_neg _)

end

end Work.Cohomology.Crux
