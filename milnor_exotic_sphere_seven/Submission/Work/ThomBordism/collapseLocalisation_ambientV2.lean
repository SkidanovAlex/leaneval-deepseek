import Mathlib
import Submission.Work.ThomBordism.ambientBase
import Submission.Work.ThomBordism.value_eq_g_pullback
import Submission.Work.ThomBordism.collapseM4Assembly
import Submission.Work.ThomBordism.compPullSurjCopy
import Submission.Work.ThomBordism.fineLift_surjective
import Submission.Work.ThomBordism.eucSliceClass_existsV2
import Submission.Work.ThomBordism.tubeCast

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace Work.ThomBordism

noncomputable section

/-- **The per-datum identity**: for every collapse datum and every class `σ` of
`H^{8+k}(S^{8+k}, S^{8+k}∖0)` restricting to `stdModelGen`, the value of the datum is the *fixed*
integer `⟨σ, locClass (stdRelK k) (some 0)⟩`.

The proof assembles the proved pieces: `value_eq_g_pullback` (the localisation in the `ν⁺`-world),
`collapse_pullback_eq_translated_8k` (the dictionary `g^*(βf) = (T_{-(E.e x)})^*σ`),
`relKronH_cast` (the degree bookkeeping) and `constancy_translated_local_pairing` (the independence
of the point). -/
theorem value_eq_stdPairing {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ} (hk : 1 ≤ k)
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
    (σ : Work.Thom.RelCoh ℤ (8 + k) (OnePoint (Work.Tubular.Euc (8 + k)))
      ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ :
        Set (OnePoint (Work.Tubular.Euc (8 + k)))))
    (hσ : (Work.Thom.relCohMap (Work.ThomBordism.eucInclV2 (8 + k))
        ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
        ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ)
        (Work.ThomBordism.eucInclV2_mem (8 + k)) ℤ (8 + k)).hom σ
      = Work.ThomBordism.stdModelGen (8 + k)) :
    Work.Tubular.relKronH (TopCat.of ↥C.U) (Work.ThomBordism.tubeInvPunct E C) (k + 8)
        ((Nat.add_comm 8 k) ▸ Work.ThomBordism.ambientStandardClass E C x) δ
      = Work.Tubular.relKronH (TopCat.of (OnePoint (Work.Tubular.Euc (8 + k))))
          ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ :
            Set (OnePoint (Work.Tubular.Euc (8 + k)))) (8 + k) σ
          (Work.Orient.locClass (TopCat.of (OnePoint (Work.Tubular.Euc (8 + k)))) (8 + k)
            (Work.ThomBordism.stdRelK k) (OnePoint.some (0 : Work.Tubular.Euc (8 + k)))) := by
  classical
  -- the `ν⁺`-avatars `β` and `βf` of the chart model class, at degree `8 + k`
  obtain ⟨β₈, hβ₈⟩ := Work.ThomBordism.compPull_surjective_v2 E (8 + k)
    (Work.ThomBordism.chartModelClass E C x (Work.ThomBordism.continuous_chartAffine_cap E C x))
  obtain ⟨βf₈, hβf₈⟩ := Work.ThomBordism.fineLift_surjective hk E x β₈
  -- the same data cast to the degree `k + 8` of the target
  have hβ : Work.Tubular.compPull E (k + 8) ((Nat.add_comm 8 k) ▸ β₈)
      = (Nat.add_comm 8 k) ▸ Work.ThomBordism.chartModelClass E C x
          (Work.ThomBordism.continuous_chartAffine_cap E C x) := by
    rw [Work.ThomBordism.compPull_cast (E := E) (Nat.add_comm 8 k) β₈, hβ₈]
  have hβf : (Work.Thom.relCohMap (ContinuousMap.id (OnePoint (Work.Tubular.NormalTotal E)))
      (Work.Tubular.onePointNonzero E)
      ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))
      (fun y hy => fun hcon => Work.ThomBordism.zeroSectionPunctPt_notMem E x (hcon ▸ hy))
      ℤ (k + 8)).hom ((Nat.add_comm 8 k) ▸ βf₈) = (Nat.add_comm 8 k) ▸ β₈ := by
    rw [Work.Thom.relCohMap_cast (ContinuousMap.id (OnePoint (Work.Tubular.NormalTotal E)))
      (Work.Tubular.onePointNonzero E)
      ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))
      (fun y hy => fun hcon => Work.ThomBordism.zeroSectionPunctPt_notMem E x (hcon ▸ hy))
      (Nat.add_comm 8 k) βf₈, hβf₈]
  -- the localisation step (M2/M3)
  rw [Work.ThomBordism.value_eq_g_pullback E C g hg hg2 hR hbox x δ hδ
      ((Nat.add_comm 8 k) ▸ β₈) hβ ((Nat.add_comm 8 k) ▸ βf₈) hβf]
  -- the dictionary (M4)
  rw [Work.Thom.relCohMap_cast g
      ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k))))
      ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))
      (Work.ThomBordism.collapse_g_mem_fine E C x g hg hg2 hR hbox) (Nat.add_comm 8 k) βf₈]
  rw [Work.ThomBordism.collapse_pullback_eq_translated_8k E C g hg hg2 hR hbox x β₈ hβ₈ βf₈ hβf₈
      σ hσ]
  -- the degree bookkeeping
  rw [Work.Tubular.relKronH_cast (Nat.add_comm 8 k)
      ((Work.Thom.relCohMap (Work.ThomBordism.transT (-(E.e x)))
        ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k))))
        ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ)
        (Work.ThomBordism.transT_pair (E.e x)) ℤ (8 + k)).hom σ)
      (Work.Orient.locClass (TopCat.of (OnePoint (Work.Tubular.Euc (8 + k)))) (8 + k)
        (Work.ThomBordism.stdRelK k) (OnePoint.some (E.e x)))]
  -- the independence of the point
  rw [Work.ThomBordism.constancy_translated_local_pairing (8 + k) σ (Work.ThomBordism.stdRelK k)
      (E.e x) 0]
  -- the translation by `0` is the identity
  have htransT0 : Work.ThomBordism.transT (-(0 : Work.Tubular.Euc (8 + k)))
      = ContinuousMap.id (OnePoint (Work.Tubular.Euc (8 + k))) := by
    apply ContinuousMap.ext
    intro z
    rw [neg_zero]
    induction z using OnePoint.rec with
    | infty =>
        rw [Work.ThomBordism.transT_infty]
        rfl
    | coe y =>
        rw [Work.ThomBordism.transT_some]
        exact congrArg OnePoint.some (add_zero y)
  have htriv : (Work.Thom.relCohMap (Work.ThomBordism.transT (-(0 : Work.Tubular.Euc (8 + k))))
      ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ :
        Set (OnePoint (Work.Tubular.Euc (8 + k))))
      ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ :
        Set (OnePoint (Work.Tubular.Euc (8 + k))))
      (Work.ThomBordism.transT_pair 0) ℤ (8 + k)).hom σ = σ := by
    rw [show (Work.Thom.relCohMap (Work.ThomBordism.transT (-(0 : Work.Tubular.Euc (8 + k))))
        ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ :
          Set (OnePoint (Work.Tubular.Euc (8 + k))))
        ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ :
          Set (OnePoint (Work.Tubular.Euc (8 + k))))
        (Work.ThomBordism.transT_pair 0) ℤ (8 + k))
        = Work.Thom.relCohMap (ContinuousMap.id (OnePoint (Work.Tubular.Euc (8 + k))))
          ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ :
            Set (OnePoint (Work.Tubular.Euc (8 + k))))
          ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ :
            Set (OnePoint (Work.Tubular.Euc (8 + k))))
          (fun _ h => h) ℤ (8 + k) from
      Work.Thom.relCohMap_congrA _ _ htransT0 _ _ ℤ (8 + k),
      Work.Thom.relCohMap_idA ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ) ℤ (8 + k)]
    rfl
  rw [htriv]

/-- **THE TARGET, and exactly what is left.**

The reduction below (`collapseLocalisation_ambientV2_of_uniformLocalClass`) is proved, but it is
**no longer the route in use**: see `NOTE_AMBIENTV2_PLAN6.md` (this directory) for the sharpened
one, which avoids `UniformLocalClass` altogether.  In one line:

    value = ⟨g^*(βf), locClass S (8+k) stdRelK (some p₀)⟩          [naturality + `hc = g_*(stdRelK)`]
          = ⟨(T_{-p})^*σ, locClass S (8+k) stdRelK (some p₀)⟩      [the dictionary (M4)]
          = ⟨σ, locClass S (8+k) stdRelK (some 0)⟩                 [`constancy_translated_local_pairing`]
          = a FIXED integer.

with `stdRelK` (below) the **datum-independent** Hurewicz class of the fixed stereographic cube
collapse, and where `hc = g_*(stdRelK)` is the PROVED
`Work.ThomBordism.tubeGenLoop_hurewiczChain_natural`.  The banked pieces (`stdRelK`, `collapse_infty`,
`normalBlowUp_eq_zeroSection`, `collapse_g_mem_fine`, `someNu_fine_mem`,
`someNu_pullback_eq_compPull`) are all proved; the two remaining proofs are the statements recorded
in `Submission/Work/ThomBordism/_v3/asm3.lean`. -/
theorem collapseLocalisation_ambientV2 (k : ℕ) (hk : 1 ≤ k) :
    ∃ κ : ℤ, (κ = 1 ∨ κ = -1) ∧
    ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
      (C : Work.Tubular.TubeChart E ε)
      (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
      (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
      (hg2 : ∀ y, y ∈ C.openTube →
        g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
      {R : ℝ} (hR : 0 ≤ R)
      (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R) (x : V.pt)
      (δ : (Work.Cohomology.relChains (TopCat.of ↥C.U)
        (Work.ThomBordism.tubeInvPunct E C)).homology (k + 8)),
      Work.ThomBordism.tubeInvHomology E C δ
        = Work.Tubular.collapseRelK8 C g hg hR hbox →
      Work.Tubular.relKronH (TopCat.of ↥C.U) (Work.ThomBordism.tubeInvPunct E C) (k + 8)
        ((Nat.add_comm 8 k) ▸ Work.ThomBordism.ambientStandardClass E C x) δ = κ := by
  classical
  obtain ⟨σ, hσ⟩ := Work.ThomBordism.eucSliceClass_existsV2 (k := k)
  by_cases hex : ∃ (V : Work.ThomBordism.Man8) (hV : ConnectedSpace V.pt)
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (ε : ℝ)
      (C : Work.Tubular.TubeChart E ε)
      (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
      (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
      (hg2 : ∀ y, y ∈ C.openTube →
        g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
      (R : ℝ) (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R) (x : V.pt)
      (δ : (Work.Cohomology.relChains (TopCat.of ↥C.U)
        (Work.ThomBordism.tubeInvPunct E C)).homology (k + 8))
      (hδ : Work.ThomBordism.tubeInvHomology E C δ
        = Work.Tubular.collapseRelK8 C g hg hR hbox), True
  · obtain ⟨V, hV, E, ε, C, g, hg, hg2, R, hR, hbox, x, δ, hδ, -⟩ := hex
    letI : ConnectedSpace V.pt := hV
    refine ⟨Work.Tubular.relKronH (TopCat.of (OnePoint (Work.Tubular.Euc (8 + k))))
        ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ :
          Set (OnePoint (Work.Tubular.Euc (8 + k)))) (8 + k) σ
        (Work.Orient.locClass (TopCat.of (OnePoint (Work.Tubular.Euc (8 + k)))) (8 + k)
          (Work.ThomBordism.stdRelK k) (OnePoint.some (0 : Work.Tubular.Euc (8 + k)))), ?_, ?_⟩
    · rw [← value_eq_stdPairing (k := k) hk E C g hg hg2 hR hbox x δ hδ σ hσ]
      exact Work.ThomBordism.valuePmOneV2 k hk E C g hg hg2 hR hbox x δ hδ
    · rintro V' hV' E' ε' C' g' hg' hg2' R' hR' hbox' x' δ' hδ'
      letI : ConnectedSpace V'.pt := hV'
      exact value_eq_stdPairing (k := k) hk E' C' g' hg' hg2' hR' hbox' x' δ' hδ' σ hσ
  · refine ⟨1, Or.inl rfl, ?_⟩
    rintro V hV E ε C g hg hg2 R hR hbox x δ hδ
    exact absurd ⟨V, hV, E, ε, C, g, hg, hg2, R, hR, hbox, x, δ, hδ, trivial⟩ hex

