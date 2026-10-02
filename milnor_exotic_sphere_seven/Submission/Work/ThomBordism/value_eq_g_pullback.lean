import Mathlib
import Submission.Work.ThomBordism.ambientBase
import Submission.Work.ThomBordism.collapseM4Defs
import Submission.Work.ThomBordism.tubeGenLoop_hurewiczChain_natural
import Submission.Work.ThomBordism.localisationHurewicz
import Submission.Work.ThomBordism.valuePmOneV2Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism

/-!
# `Work.ThomBordism.value_eq_g_pullback`

**M2/M3 of the ambient collapse localisation** (see `NOTE_AMBIENTV2_PLAN6.md`): the pairing of the
ambient standard class with the tube avatar of the collapse class is the pairing, in the Thom space
`(ν⁺, ν⁺∖{x₀})`, of the pulled-back chart avatar `g^*(βf)` with the *localisation at `some (E.e x)`
of the fixed Hurewicz class* `stdRelK k` — the datum-independent class of the standard
stereographic cube collapse.

The proof composes the three naturalities of the workspace for the map of pairs
`g : (S, S∖{some (E.e x)}) → (ν⁺, ν⁺∖{x₀})`:

* `Work.ThomBordism.tubeGenLoop_hurewiczChain_natural` — the Hurewicz class of the tube loop is the
  push-forward along `g` of the fixed class:
  `hurewiczChain (8+k) ∞ (tubeGenLoopOnePoint C g hg hR hbox) = g_*(stdRelK k)`;
* `Work.Tubular.TubeClass.cokernel_pi_chainMap_homology` — the cokernel projection (the
  localisation) is natural for the induced map of relative chain complexes;
* `Work.Tubular.relKronH_natural` — the relative Kronecker pairing is natural for the map of pairs.

The only bookkeeping is the degree: the fixed classes live at degree `8 + k` while the target pairs
at `k + 8`, and the degree cast is moved across `homologyMap` with
`Work.Tubular.homologyMap_cast_nat` on the *fixed* classes only (never on a variable), which keeps
the elaboration cheap.

The hypotheses `hδ`, `hβ`, `hβf` enter through `Work.ThomBordism.value_eq_piStar_fine`, which
identifies the target's value with the `(ν⁺, ν⁺∖{x₀})`-pairing of `βf` with the cokernel image of
the collapse's Hurewicz class; the map of pairs `g` then moves `βf` to the sphere side.
-/

theorem value_eq_g_pullback {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R) (x : V.pt)
    (δ : (Work.Cohomology.relChains (TopCat.of ↥C.U)
      (Work.ThomBordism.tubeInvPunct E C)).homology (k + 8))
    (hδ : Work.ThomBordism.tubeInvHomology E C δ
      = Work.Tubular.collapseRelK8 C g hg hR hbox)
    (β : Work.Thom.RelCoh ℤ (k + 8) (OnePoint (Work.Tubular.NormalTotal E))
      (Work.Tubular.onePointNonzero E))
    (hβ : Work.Tubular.compPull E (k + 8) β
      = (Nat.add_comm 8 k) ▸ Work.ThomBordism.chartModelClass E C x
          (Work.ThomBordism.continuous_chartAffine_cap E C x))
    (βf : Work.Thom.RelCoh ℤ (k + 8) (OnePoint (Work.Tubular.NormalTotal E))
      ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E))))
    (hβf : (Work.Thom.relCohMap (ContinuousMap.id (OnePoint (Work.Tubular.NormalTotal E)))
        (Work.Tubular.onePointNonzero E)
        ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))
        (fun y hy => fun hcon => Work.ThomBordism.zeroSectionPunctPt_notMem E x (hcon ▸ hy))
        ℤ (k + 8)).hom βf
      = β) :
    Work.Tubular.relKronH (TopCat.of ↥C.U) (Work.ThomBordism.tubeInvPunct E C) (k + 8)
        ((Nat.add_comm 8 k) ▸ Work.ThomBordism.ambientStandardClass E C x) δ
      = Work.Tubular.relKronH (TopCat.of (OnePoint (Work.Tubular.Euc (8 + k))))
          ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k)))) (k + 8)
          ((Work.Thom.relCohMap g
            ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k))))
            ({Work.Tubular.zeroSectionPunctPt E x}ᶜ :
              Set (OnePoint (Work.Tubular.NormalTotal E)))
            (Work.ThomBordism.collapse_g_mem_fine E C x g hg hg2 hR hbox) ℤ (k + 8)).hom βf)
          ((Nat.add_comm 8 k) ▸ Work.Orient.locClass
            (TopCat.of (OnePoint (Work.Tubular.Euc (8 + k)))) (8 + k) (Work.ThomBordism.stdRelK k)
            (OnePoint.some (E.e x))) := by
  classical
  have h8k : 8 + k = k + 8 := Nat.add_comm 8 k
  -- ### the map of pairs `(S, S∖{p₀}) → (ν⁺, ν⁺∖{x₀})` induced by `g`
  let G : TopCat.of (↥({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k))))) ⟶
      TopCat.of (↥({Work.Tubular.zeroSectionPunctPt E x}ᶜ :
        Set (OnePoint (Work.Tubular.NormalTotal E)))) :=
    TopCat.ofHom
      ⟨fun y => ⟨g y.1,
          Work.ThomBordism.collapse_g_mem_fine E C x g hg hg2 hR hbox y.1 y.2⟩,
        Continuous.subtype_mk (g.continuous.comp continuous_subtype_val)
          (fun y => Work.ThomBordism.collapse_g_mem_fine E C x g hg hg2 hR hbox y.1 y.2)⟩
  let W : CategoryTheory.CategoryStruct.comp
        (Work.Cohomology.subtypeIncl (TopCat.of (OnePoint (Work.Tubular.Euc (8 + k))))
          ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k)))))
        (TopCat.ofHom g)
      = CategoryTheory.CategoryStruct.comp G
        (Work.Cohomology.subtypeIncl (TopCat.of (OnePoint (Work.Tubular.NormalTotal E)))
          ({Work.Tubular.zeroSectionPunctPt E x}ᶜ :
            Set (OnePoint (Work.Tubular.NormalTotal E)))) := by
    apply TopCat.ext
    intro a
    rfl
  -- ### the Hurewicz class of the tube loop is the push-forward of the fixed class
  have hhc8 : Work.Stems.hurewiczChain (8 + k) (by omega) OnePoint.infty
        (Work.Tubular.tubeGenLoopOnePoint C g hg hR hbox)
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
          (TopCat.of (OnePoint (Work.Tubular.Euc (8 + k))))
          (TopCat.of (OnePoint (Work.Tubular.NormalTotal E)))
          (TopCat.ofHom g)) (8 + k))) (Work.ThomBordism.stdRelK k) := by
    rw [Work.ThomBordism.tubeGenLoop_hurewiczChain_natural C g hg hR hbox]
    rfl
  -- ### naturality of the cokernel projection along the map of pairs
  have hnatCM := Work.Tubular.TubeClass.cokernel_pi_chainMap_homology
    (X := TopCat.of (OnePoint (Work.Tubular.Euc (8 + k))))
    (Y := TopCat.of (OnePoint (Work.Tubular.NormalTotal E)))
    (A := ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k)))))
    (B := ({Work.Tubular.zeroSectionPunctPt E x}ᶜ :
      Set (OnePoint (Work.Tubular.NormalTotal E))))
    (f := TopCat.ofHom g) (g := G) (w := W) (n := 8 + k)
    (x := Work.ThomBordism.stdRelK k)
  -- ### the fixed class in the cokernel is its local class
  have hloc : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains
          (TopCat.of (OnePoint (Work.Tubular.Euc (8 + k))))
          ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k))))))
        (8 + k))) (Work.ThomBordism.stdRelK k)
      = Work.Orient.locClass (TopCat.of (OnePoint (Work.Tubular.Euc (8 + k)))) (8 + k)
          (Work.ThomBordism.stdRelK k) (OnePoint.some (E.e x)) := rfl
  -- ### naturality of the relative Kronecker pairing along the map of pairs, at the target's degree
  have hnatRK := Work.Tubular.relKronH_natural
    (X := TopCat.of (OnePoint (Work.Tubular.Euc (8 + k))))
    (Y := TopCat.of (OnePoint (Work.Tubular.NormalTotal E)))
    (A := ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k)))))
    (B := ({Work.Tubular.zeroSectionPunctPt E x}ᶜ :
      Set (OnePoint (Work.Tubular.NormalTotal E))))
    (f := TopCat.ofHom g) (g := G)
    (hf := Work.ThomBordism.collapse_g_mem_fine E C x g hg hg2 hR hbox)
    (w := W) (n := k + 8) (β := βf)
    (c := (h8k ▸ Work.Orient.locClass (TopCat.of (OnePoint (Work.Tubular.Euc (8 + k))))
        (8 + k) (Work.ThomBordism.stdRelK k) (OnePoint.some (E.e x)) :
      (Work.Cohomology.relChains (TopCat.of (OnePoint (Work.Tubular.Euc (8 + k))))
        ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k))))).homology (k + 8)))
  -- ### the assembly
  rw [Work.ThomBordism.value_eq_piStar_fine E C g hg hR hbox x δ hδ β hβ βf hβf]
  rw [hhc8]
  rw [Work.Tubular.homologyMap_cast_nat
    (φ := CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains
      (TopCat.of (OnePoint (Work.Tubular.NormalTotal E)))
      ({Work.Tubular.zeroSectionPunctPt E x}ᶜ :
        Set (OnePoint (Work.Tubular.NormalTotal E))))) (h := h8k)]
  rw [hnatCM]
  rw [hloc]
  refine Eq.trans ?_ hnatRK.symm
  exact congrArg (fun w => ((Work.Tubular.relKronH
      (TopCat.of (OnePoint (Work.Tubular.NormalTotal E)))
      ({Work.Tubular.zeroSectionPunctPt E x}ᶜ :
        Set (OnePoint (Work.Tubular.NormalTotal E)))) (k + 8) βf) w)
    (Work.Tubular.homologyMap_cast_nat
      (Work.Cohomology.relChainsMapOf
        (TopCat.of (OnePoint (Work.Tubular.Euc (8 + k))))
        (TopCat.of (OnePoint (Work.Tubular.NormalTotal E)))
        ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k))))
        ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))
        (TopCat.ofHom g) G W) h8k
      (Work.Orient.locClass (TopCat.of (OnePoint (Work.Tubular.Euc (8 + k)))) (8 + k)
        (Work.ThomBordism.stdRelK k) (OnePoint.some (E.e x)))).symm



end Work.ThomBordism
