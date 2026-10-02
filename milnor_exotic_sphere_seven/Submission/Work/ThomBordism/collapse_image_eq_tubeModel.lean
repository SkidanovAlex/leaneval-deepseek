import Mathlib
import Submission.Work.ThomBordism.collapseM4Defs
import Submission.Work.ThomBordism.blowPsiStage_mem_fine
import Submission.Work.ThomBordism.ambientBase
import Submission.Work.ThomBordism.somePullbackCompPullV2
import Submission.Work.ThomBordism.relCohMap_id_normalPunct_injective

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

namespace Work.ThomBordism

open CategoryTheory

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-! ## Auxiliary lemmas -/

/-- `normalBlowUp` is continuous on the open `ε`-disc. -/
theorem continuousOn_normalBlowUp_openDisc
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (ε : ℝ) :
    ContinuousOn (fun p : Work.Tubular.NormalTotal E => Work.Tubular.normalBlowUp E ε p)
      {p | Work.Tubular.normalNorm E p < ε} := by
  have h := Work.ThomBordism.continuousOn_radialRescale_blowPsi E ε
  have hcomp := h.comp ((continuous_const.prodMk continuous_id :
    Continuous fun p : Work.Tubular.NormalTotal E => ((1 : ℝ), p)).continuousOn)
    (fun p hp => hp)
  refine hcomp.congr (fun p _ => ?_)
  exact (Work.ThomBordism.radialRescale_blowPsi_one E ε p).symm

/-- The distiguished zero-section point is the `some` of the zero-section point. -/
theorem zeroSectionPunctPt_eq_some_v2
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt) :
    Work.Tubular.zeroSectionPunctPt E x
      = (OnePoint.some (Work.Tubular.zeroSectionNormal E x) :
          OnePoint (Work.Tubular.NormalTotal E)) := by
  rw [Work.Tubular.zeroSectionPunctPt, Work.Tubular.zeroSectionOnePoint_apply]
  rfl

/-- `some` of a point is the distinguished zero-section point only for that point. -/
theorem some_ne_zeroSectionPunctPt_iff
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt)
    (p : Work.Tubular.NormalTotal E) :
    (OnePoint.some p : OnePoint (Work.Tubular.NormalTotal E)) ≠
        Work.Tubular.zeroSectionPunctPt E x ↔ p ≠ Work.Tubular.zeroSectionNormal E x := by
  rw [zeroSectionPunctPt_eq_some_v2]
  exact OnePoint.coe_injective.ne_iff

/-- **The capped chart map only vanishes at the base zero-section point.** -/
theorem chartAffine_cap_ne_zero_of_ne
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt)
    {p : Work.Tubular.NormalTotal E} (hp : p ≠ Work.Tubular.zeroSectionNormal E x) :
    Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p) ≠ 0 := by
  intro h0
  have htube : Work.Tubular.tubeMap E (Work.ThomBordism.cap E ε p) = E.e x := by
    have h := congrArg (fun z : Work.Tubular.Euc (8 + k) => z + E.e x) h0
    rw [Work.ThomBordism.chartAffine_apply] at h
    rw [sub_add_cancel] at h
    simpa [Work.Tubular.tubeMap] using h
  have hle : Work.Tubular.normalNorm E (Work.ThomBordism.cap E ε p) ≤ ε :=
    Work.ThomBordism.cap_mem_disc E C.eps_pos.le p
  have hnorm0 : Work.Tubular.normalNorm E (Work.Tubular.zeroSectionNormal E x) = 0 := by
    rw [Work.Tubular.zeroSectionNormal]; simp
  have heq : Work.ThomBordism.cap E ε p = Work.Tubular.zeroSectionNormal E x := by
    have h1 := congrArg C.inv
      (htube.trans (Work.ThomBordism.tubeMap_zeroSectionNormal E x).symm)
    rw [C.inv_tubeMap _ hle, C.inv_tubeMap _ (by rw [hnorm0]; exact C.eps_pos.le)] at h1
    exact h1
  have hcapnorm := Work.ThomBordism.normalNorm_cap (E := E) (ε := ε) C.eps_pos.le p
  have hmin : min (Work.Tubular.normalNorm E p) ε = 0 :=
    hcapnorm.symm.trans (by rw [heq, hnorm0])
  have hnormp : Work.Tubular.normalNorm E p = 0 := by
    by_cases h : Work.Tubular.normalNorm E p ≤ ε
    · rw [min_eq_left h] at hmin; exact hmin
    · rw [min_eq_right (not_le.mp h).le] at hmin
      exact absurd hmin (ne_of_gt C.eps_pos)
  -- the projection of `p` is `x`, and its normal vector vanishes
  apply hp
  apply Subtype.ext
  apply Prod.ext
  · have h1 := congrArg (fun z : V.pt × Work.Tubular.Euc (8 + k) => z.1)
      (congrArg Subtype.val heq)
    rw [Work.ThomBordism.cap, Work.ThomBordism.radialRescale_coe,
      Work.Tubular.zeroSectionNormal_apply] at h1
    simpa using h1
  · have h2 : ‖((p : V.pt × Work.Tubular.Euc (8 + k)).2)‖ = 0 := by
      have h := Work.Tubular.normalNorm_mk (E := E)
        ((p : V.pt × Work.Tubular.Euc (8 + k)).1)
        ((p : V.pt × Work.Tubular.Euc (8 + k)).2) p.2
      rw [← h]
      exact hnormp
    simpa using norm_eq_zero.mp h2

/-- The blow-up of the tube inverse misses the distinguished zero-section point. -/
theorem normalBlowUp_inv_ne_zeroSectionPunct
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    ∀ y ∈ Work.ThomBordism.openTubePtset E C x,
      Work.Tubular.normalBlowUp E ε (C.inv (y.1 : Work.Tubular.Euc (8 + k)))
        ≠ Work.Tubular.zeroSectionNormal E x := by
  intro y hy hcon
  have h1 : C.inv (y.1 : Work.Tubular.Euc (8 + k)) = Work.Tubular.zeroSectionNormal E x :=
    Work.ThomBordism.normalBlowUp_eq_zeroSection E C.eps_pos (C.normalNorm_inv_lt y.2) x hcon
  have h2 : (y.1 : Work.Tubular.Euc (8 + k)) = E.e x := by
    rw [← C.tubeMap_inv (y.1 : Work.Tubular.Euc (8 + k)) (C.openTube_subset_U y.2), h1,
      Work.ThomBordism.tubeMap_zeroSectionNormal]
  exact hy h2

/-- The reciprocal membership: the fibre of the norm-zero condition is the zero section. -/
theorem normalNorm_eq_zero_iff_zeroSection
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (p : Work.Tubular.NormalTotal E) :
    Work.Tubular.normalNorm E p = 0 ↔ p = Work.Tubular.zeroSectionNormal E (p.1.1) := by
  constructor
  · intro hp
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have h2 : ‖((p : V.pt × Work.Tubular.Euc (8 + k)).2)‖ = 0 := by
        have h := Work.Tubular.normalNorm_mk (E := E)
          ((p : V.pt × Work.Tubular.Euc (8 + k)).1)
          ((p : V.pt × Work.Tubular.Euc (8 + k)).2) p.2
        rw [← h]; exact hp
      simpa [Work.Tubular.zeroSectionNormal_apply] using norm_eq_zero.mp h2
  · intro hp
    rw [hp, Work.Tubular.zeroSectionNormal_apply, Work.Tubular.normalNorm_mk, norm_zero]


/-! ## The main theorem -/

theorem collapse_image_eq_tubeModel {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R) (x : V.pt)
    (β : Work.Thom.RelCoh ℤ (8 + k) (OnePoint (Work.Tubular.NormalTotal E))
      (Work.Tubular.onePointNonzero E))
    (hβ : Work.Tubular.compPull E (8 + k) β
      = Work.ThomBordism.chartModelClass E C x (Work.ThomBordism.continuous_chartAffine_cap E C x))
    (βf : Work.Thom.RelCoh ℤ (8 + k) (OnePoint (Work.Tubular.NormalTotal E))
      ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E))))
    (hβf : (Work.Thom.relCohMap (ContinuousMap.id (OnePoint (Work.Tubular.NormalTotal E)))
        (Work.Tubular.onePointNonzero E)
        ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))
        (fun y hy => fun hcon => Work.ThomBordism.zeroSectionPunctPt_notMem E x (hcon ▸ hy))
        ℤ (8 + k)).hom βf
      = β) :
    (Work.Thom.relCohMap (Work.ThomBordism.someOpen E C)
        (Work.ThomBordism.openTubePtset E C x)
        ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k))))
        (Work.ThomBordism.someOpen_mem E C x) ℤ (8 + k)).hom
      ((Work.Thom.relCohMap g
          ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k))))
          ({Work.Tubular.zeroSectionPunctPt E x}ᶜ :
            Set (OnePoint (Work.Tubular.NormalTotal E)))
          (Work.ThomBordism.collapse_g_mem_fine E C x g hg hg2 hR hbox) ℤ (8 + k)).hom βf)
      = (Work.Thom.relCohMap (Work.ThomBordism.blowPsiStage E C 1)
          (Work.ThomBordism.openTubePtset E C x)
          (Work.ThomBordism.tubePtSet E C x)
          (Work.ThomBordism.blowPsiStage_mem_fine E C x 1) ℤ (8 + k)).hom
          (Work.ThomBordism.tubeTransModel E C x) := by
  classical
  -- ## the auxiliary continuous maps and sets
  have hBIcont : Continuous fun y : ↥C.openTube =>
      Work.Tubular.normalBlowUp E ε (C.inv (y.1 : Work.Tubular.Euc (8 + k))) :=
    (continuousOn_normalBlowUp_openDisc E ε).comp_continuous
      ((C.continuousOn_inv.mono C.openTube_subset_U).comp_continuous continuous_subtype_val
        (fun y => y.2))
      (fun y => C.normalNorm_inv_lt y.2)
  let BI : C(↥C.openTube, Work.Tubular.NormalTotal E) :=
    ⟨fun y => Work.Tubular.normalBlowUp E ε (C.inv (y.1 : Work.Tubular.Euc (8 + k))), hBIcont⟩
  let SP : C(Work.Tubular.NormalTotal E, OnePoint (Work.Tubular.NormalTotal E)) :=
    ⟨OnePoint.some, OnePoint.continuous_coe⟩
  let BS : C(↥C.openTube, OnePoint (Work.Tubular.NormalTotal E)) := SP.comp BI
  let CM : C(Work.Tubular.NormalTotal E, Work.Tubular.Euc (8 + k)) :=
    ⟨fun p => Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p),
      Work.ThomBordism.continuous_chartAffine_cap E C x⟩
  let L : Set (Work.Tubular.NormalTotal E) :=
    {p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}
  -- ## the set memberships
  have hBI_L : ∀ y ∈ Work.ThomBordism.openTubePtset E C x, BI y ∈ L :=
    fun y hy => normalBlowUp_inv_ne_zeroSectionPunct E C x y hy
  have hSP_L : ∀ p ∈ L, SP p ∈ ({Work.Tubular.zeroSectionPunctPt E x}ᶜ :
      Set (OnePoint (Work.Tubular.NormalTotal E))) :=
    fun p hp => (some_ne_zeroSectionPunctPt_iff E x p).mpr hp
  have hCM_L : ∀ p ∈ L, CM p ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) :=
    fun p hp => chartAffine_cap_ne_zero_of_ne E C x hp
  have hBS_p : ∀ y ∈ Work.ThomBordism.openTubePtset E C x,
      BS y ∈ ({Work.Tubular.zeroSectionPunctPt E x}ᶜ :
        Set (OnePoint (Work.Tubular.NormalTotal E))) :=
    fun y hy => hSP_L (BI y) (hBI_L y hy)
  have hSPsn : ∀ p ∈ Work.Tubular.normalNonzero E,
      SP p ∈ ({Work.Tubular.zeroSectionPunctPt E x}ᶜ :
        Set (OnePoint (Work.Tubular.NormalTotal E))) :=
    Work.ThomBordism.someNu_fine_mem E x
  have hCM_M : ∀ p ∈ Work.Tubular.normalNonzero E,
      CM p ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) :=
    fun p hp => Work.ThomBordism.chartAffine_cap_ne_zero E C x hp
  -- ## `g ∘ someOpen = BS`
  have hgBS : g.comp (Work.ThomBordism.someOpen E C) = BS := by
    apply ContinuousMap.ext
    intro y
    show g (OnePoint.some (y.1 : Work.Tubular.Euc (8 + k)))
      = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv (y.1 : Work.Tubular.Euc (8 + k))))
    exact hg2 (y.1 : Work.Tubular.Euc (8 + k)) y.2
  -- the pair condition of the composite
  have hgpair : ∀ y ∈ Work.ThomBordism.openTubePtset E C x,
      (g.comp (Work.ThomBordism.someOpen E C)) y
        ∈ ({Work.Tubular.zeroSectionPunctPt E x}ᶜ :
            Set (OnePoint (Work.Tubular.NormalTotal E))) :=
    fun y hy => Work.ThomBordism.collapse_g_mem_fine E C x g hg hg2 hR hbox
      (Work.ThomBordism.someOpen E C y) (Work.ThomBordism.someOpen_mem E C x y hy)
  -- ## the two elements `w` and `z`
  let w : Work.Thom.RelCoh ℤ (8 + k) (Work.Tubular.NormalTotal E) L :=
    (Work.Thom.relCohMap SP L ({Work.Tubular.zeroSectionPunctPt E x}ᶜ :
      Set (OnePoint (Work.Tubular.NormalTotal E))) hSP_L ℤ (8 + k)).hom βf
  let z : Work.Thom.RelCoh ℤ (8 + k) (Work.Tubular.NormalTotal E) L :=
    (Work.Thom.relCohMap CM L ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hCM_L ℤ (8 + k)).hom
      (Work.ThomBordism.stdModelGen (8 + k))
  -- ## the left-hand side is `(BI)^* w`
  have hLHS : (Work.Thom.relCohMap (Work.ThomBordism.someOpen E C)
        (Work.ThomBordism.openTubePtset E C x)
        ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k))))
        (Work.ThomBordism.someOpen_mem E C x) ℤ (8 + k)).hom
      ((Work.Thom.relCohMap g
          ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k))))
          ({Work.Tubular.zeroSectionPunctPt E x}ᶜ :
            Set (OnePoint (Work.Tubular.NormalTotal E)))
          (Work.ThomBordism.collapse_g_mem_fine E C x g hg hg2 hR hbox) ℤ (8 + k)).hom βf)
      = (Work.Thom.relCohMap BI (Work.ThomBordism.openTubePtset E C x) L hBI_L ℤ
          (8 + k)).hom w := by
    -- combine the two pullbacks
    have h1 : Work.Thom.relCohMap g
          ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k))))
          ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))
          (Work.ThomBordism.collapse_g_mem_fine E C x g hg hg2 hR hbox) ℤ (8 + k)
        ≫ Work.Thom.relCohMap (Work.ThomBordism.someOpen E C)
          (Work.ThomBordism.openTubePtset E C x)
          ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k))))
          (Work.ThomBordism.someOpen_mem E C x) ℤ (8 + k)
        = Work.Thom.relCohMap (g.comp (Work.ThomBordism.someOpen E C))
          (Work.ThomBordism.openTubePtset E C x)
          ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))
          hgpair ℤ (8 + k) :=
      Work.Thom.relCohMap_compA (Work.ThomBordism.openTubePtset E C x)
        ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k))))
        ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))
        (Work.ThomBordism.someOpen E C) g (Work.ThomBordism.someOpen_mem E C x)
        (Work.ThomBordism.collapse_g_mem_fine E C x g hg hg2 hR hbox) hgpair ℤ (8 + k)
    have hcong1 : Work.Thom.relCohMap (g.comp (Work.ThomBordism.someOpen E C))
          (Work.ThomBordism.openTubePtset E C x)
          ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))
          hgpair ℤ (8 + k)
        = Work.Thom.relCohMap BS (Work.ThomBordism.openTubePtset E C x)
          ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))
          hBS_p ℤ (8 + k) :=
      Work.Thom.relCohMap_congrA (Work.ThomBordism.openTubePtset E C x)
        ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))
        hgBS hgpair hBS_p ℤ (8 + k)
    have h2 : Work.Thom.relCohMap SP L
          ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))
          hSP_L ℤ (8 + k)
        ≫ Work.Thom.relCohMap BI (Work.ThomBordism.openTubePtset E C x) L hBI_L ℤ (8 + k)
        = Work.Thom.relCohMap BS (Work.ThomBordism.openTubePtset E C x)
          ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))
          hBS_p ℤ (8 + k) :=
      Work.Thom.relCohMap_compA (Work.ThomBordism.openTubePtset E C x) L
        ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))
        BI SP hBI_L hSP_L hBS_p ℤ (8 + k)
    rw [← ModuleCat.comp_apply, h1, hcong1, ← h2, ModuleCat.comp_apply]
  -- ## the right-hand side is `(BI)^* z`
  have hRHS : (Work.Thom.relCohMap (Work.ThomBordism.blowPsiStage E C 1)
        (Work.ThomBordism.openTubePtset E C x)
        (Work.ThomBordism.tubePtSet E C x)
        (Work.ThomBordism.blowPsiStage_mem_fine E C x 1) ℤ (8 + k)).hom
      (Work.ThomBordism.tubeTransModel E C x)
      = (Work.Thom.relCohMap BI (Work.ThomBordism.openTubePtset E C x) L hBI_L ℤ
          (8 + k)).hom z := by
    -- unfold the tube model class
    have h3 : Work.ThomBordism.tubeTransModel E C x
        = (Work.Thom.relCohMap (Work.ThomBordism.tubeTransMap E C x)
            (Work.ThomBordism.tubePtSet E C x) ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
            (Work.ThomBordism.tubeTransMap_mem E C x) ℤ (8 + k)).hom
            (Work.ThomBordism.stdModelGen (8 + k)) := rfl
    rw [h3]
    -- combine the two pullbacks
    have h4 : Work.Thom.relCohMap (Work.ThomBordism.tubeTransMap E C x)
          (Work.ThomBordism.tubePtSet E C x) ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
          (Work.ThomBordism.tubeTransMap_mem E C x) ℤ (8 + k)
        ≫ Work.Thom.relCohMap (Work.ThomBordism.blowPsiStage E C 1)
          (Work.ThomBordism.openTubePtset E C x) (Work.ThomBordism.tubePtSet E C x)
          (Work.ThomBordism.blowPsiStage_mem_fine E C x 1) ℤ (8 + k)
        = Work.Thom.relCohMap ((Work.ThomBordism.tubeTransMap E C x).comp
            (Work.ThomBordism.blowPsiStage E C 1))
          (Work.ThomBordism.openTubePtset E C x)
          ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
          (fun y hy => Work.ThomBordism.tubeTransMap_mem E C x _
            (Work.ThomBordism.blowPsiStage_mem_fine E C x 1 y hy)) ℤ (8 + k) :=
      Work.Thom.relCohMap_compA (Work.ThomBordism.openTubePtset E C x)
        (Work.ThomBordism.tubePtSet E C x) ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
        (Work.ThomBordism.blowPsiStage E C 1) (Work.ThomBordism.tubeTransMap E C x)
        (Work.ThomBordism.blowPsiStage_mem_fine E C x 1)
        (Work.ThomBordism.tubeTransMap_mem E C x)
        (fun y hy => Work.ThomBordism.tubeTransMap_mem E C x _
          (Work.ThomBordism.blowPsiStage_mem_fine E C x 1 y hy)) ℤ (8 + k)
    rw [← ModuleCat.comp_apply, h4]
    -- `TT ∘ blowPsiStage 1 = CM ∘ BI`
    have h5 : (Work.ThomBordism.tubeTransMap E C x).comp (Work.ThomBordism.blowPsiStage E C 1)
        = CM.comp BI := by
      apply ContinuousMap.ext
      intro y
      show ((Work.ThomBordism.blowPsiStage E C 1) y : Work.Tubular.Euc (8 + k)) - E.e x
        = Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε
            (Work.Tubular.normalBlowUp E ε (C.inv (y.1 : Work.Tubular.Euc (8 + k)))))
      have hinv := Work.ThomBordism.blowPsiStage_inv_eq E C 1 y
      rw [show ((1 : unitInterval) : ℝ) = 1 from rfl,
        Work.ThomBordism.radialRescale_blowPsi_one] at hinv
      rw [← hinv]
      exact (Work.ThomBordism.chartAffine_inv E C x
        ((Work.ThomBordism.blowPsiStage E C 1) y).2).symm
    have hcong2 : Work.Thom.relCohMap ((Work.ThomBordism.tubeTransMap E C x).comp
            (Work.ThomBordism.blowPsiStage E C 1))
          (Work.ThomBordism.openTubePtset E C x)
          ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
          (fun y hy => Work.ThomBordism.tubeTransMap_mem E C x _
            (Work.ThomBordism.blowPsiStage_mem_fine E C x 1 y hy)) ℤ (8 + k)
        = Work.Thom.relCohMap (CM.comp BI) (Work.ThomBordism.openTubePtset E C x)
          ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
          (fun y hy => hCM_L (BI y) (hBI_L y hy)) ℤ (8 + k) :=
      Work.Thom.relCohMap_congrA (Work.ThomBordism.openTubePtset E C x)
        ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) h5 _ _ ℤ (8 + k)
    rw [hcong2]
    -- decompose through `L`
    have h6 : Work.Thom.relCohMap CM L ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hCM_L ℤ (8 + k)
        ≫ Work.Thom.relCohMap BI (Work.ThomBordism.openTubePtset E C x) L hBI_L ℤ (8 + k)
        = Work.Thom.relCohMap (CM.comp BI) (Work.ThomBordism.openTubePtset E C x)
          ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
          (fun y hy => hCM_L (BI y) (hBI_L y hy)) ℤ (8 + k) :=
      Work.Thom.relCohMap_compA (Work.ThomBordism.openTubePtset E C x) L
        ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) BI CM hBI_L hCM_L
        (fun y hy => hCM_L (BI y) (hBI_L y hy)) ℤ (8 + k)
    rw [← h6, ModuleCat.comp_apply]
  -- ## the crux: `w = z`
  have hsub : ∀ p ∈ Work.Tubular.normalNonzero E, p ∈ L :=
    fun p hp => by
      intro h
      refine (Work.Tubular.mem_normalNonzero (E := E)).mp hp ?_
      have h2 : p = Work.Tubular.zeroSectionNormal E x := by simpa using h
      rw [h2]; simp
  have hwz : w = z := by
    have hjw : (Work.Thom.relCohMap (ContinuousMap.id (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) L hsub ℤ (8 + k)).hom w
        = Work.ThomBordism.chartModelClass E C x
            (Work.ThomBordism.continuous_chartAffine_cap E C x) := by
      have h1 : Work.Thom.relCohMap SP L
            ({Work.Tubular.zeroSectionPunctPt E x}ᶜ :
              Set (OnePoint (Work.Tubular.NormalTotal E))) hSP_L ℤ (8 + k)
          ≫ Work.Thom.relCohMap (ContinuousMap.id (Work.Tubular.NormalTotal E))
            (Work.Tubular.normalNonzero E) L hsub ℤ (8 + k)
          = Work.Thom.relCohMap SP (Work.Tubular.normalNonzero E)
            ({Work.Tubular.zeroSectionPunctPt E x}ᶜ :
              Set (OnePoint (Work.Tubular.NormalTotal E))) hSPsn ℤ (8 + k) :=
        Work.Thom.relCohMap_compA (Work.Tubular.normalNonzero E) L
          ({Work.Tubular.zeroSectionPunctPt E x}ᶜ :
            Set (OnePoint (Work.Tubular.NormalTotal E)))
          (ContinuousMap.id (Work.Tubular.NormalTotal E)) SP hsub hSP_L hSPsn ℤ (8 + k)
      rw [show w = (Work.Thom.relCohMap SP L
            ({Work.Tubular.zeroSectionPunctPt E x}ᶜ :
              Set (OnePoint (Work.Tubular.NormalTotal E))) hSP_L ℤ (8 + k)).hom βf from rfl]
      rw [← ModuleCat.comp_apply, h1]
      exact (Work.ThomBordism.someNu_pullback_eq_compPull E x β βf hβf).trans hβ
    have hjz : (Work.Thom.relCohMap (ContinuousMap.id (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) L hsub ℤ (8 + k)).hom z
        = Work.ThomBordism.chartModelClass E C x
            (Work.ThomBordism.continuous_chartAffine_cap E C x) := by
      have h2 : Work.Thom.relCohMap CM L ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hCM_L
            ℤ (8 + k)
          ≫ Work.Thom.relCohMap (ContinuousMap.id (Work.Tubular.NormalTotal E))
            (Work.Tubular.normalNonzero E) L hsub ℤ (8 + k)
          = Work.Thom.relCohMap CM (Work.Tubular.normalNonzero E)
            ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hCM_M ℤ (8 + k) :=
        Work.Thom.relCohMap_compA (Work.Tubular.normalNonzero E) L
          ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
          (ContinuousMap.id (Work.Tubular.NormalTotal E)) CM hsub hCM_L hCM_M ℤ (8 + k)
      rw [show z = (Work.Thom.relCohMap CM L ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
            hCM_L ℤ (8 + k)).hom (Work.ThomBordism.stdModelGen (8 + k)) from rfl]
      rw [← ModuleCat.comp_apply, h2]
      rfl
    exact Work.ThomBordism.relCohMap_id_normalPunct_injective E x (hjw.trans hjz.symm)
  -- ## assembly
  exact hLHS.trans ((congrArg (fun u => (Work.Thom.relCohMap BI
      (Work.ThomBordism.openTubePtset E C x) L hBI_L ℤ (8 + k)).hom u) hwz).trans hRHS.symm)
end

end Work.ThomBordism
