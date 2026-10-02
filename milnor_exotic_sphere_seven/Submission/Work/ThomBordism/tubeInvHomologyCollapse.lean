import Mathlib
import Submission.Work.ThomBordism.ambientClassDefs
import Submission.Work.ThomBordism.tubeRelChains_tubeInvPunct_nonzero
import Submission.Work.ThomBordism.ambientLocalDefs2
import Submission.Work.ThomBordism.tubeInvHomology_injective
import Submission.Work.ThomBordism.valuePmOneV2Defs
import Submission.Work.ThomBordism.radialRescale_homologyMap_id

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.ThomBordism

open CategoryTheory

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ} {ε : ℝ}

/-- The coefficient of the "clamping" fibrewise radial rescaling `p ↦ (ε / max ‖p‖ ε) • p` of the
normal bundle: it is positive everywhere on `[0,∞)` and equals `1` on the closed disc bundle of
radius `ε`, so that the clamping fixes the image of the tube inverse. -/
def clampCoeff (ε : ℝ) : ℝ → ℝ := fun r => ε / max r ε

theorem continuous_clampCoeff {ε : ℝ} (hε : 0 < ε) : Continuous (clampCoeff ε) := by
  unfold clampCoeff
  exact continuous_const.div (continuous_id.max continuous_const)
    (fun r => ne_of_gt (lt_of_lt_of_le hε (le_max_right r ε)))

theorem clampCoeff_pos {ε : ℝ} (hε : 0 < ε) : ∀ r : ℝ, 0 ≤ r → 0 < clampCoeff ε r := by
  intro r _
  unfold clampCoeff
  exact div_pos hε (lt_of_lt_of_le hε (le_max_right r ε))

/-- The clamping rescaling is the fibrewise multiplication by `clampScale`. -/
theorem radialRescale_clampCoeff_eq_nsmul
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (p : Work.Tubular.NormalTotal E) :
    Work.ThomBordism.radialRescale E (clampCoeff ε) p
      = Work.ThomBordism.nsmul (Work.ThomBordism.clampScale (ε := ε) p) p := rfl

theorem continuous_radialRescale_clampCoeff
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (hε : 0 < ε) :
    Continuous (Work.ThomBordism.radialRescale E (clampCoeff ε)) :=
  Work.ThomBordism.ttm_continuous_radialRescale E (clampCoeff ε) (continuous_clampCoeff hε)

/-- The clamping, as a self-map of the normal total space. -/
noncomputable def clampMap (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (hε : 0 < ε) :
    TopCat.of (Work.Tubular.NormalTotal E) ⟶ TopCat.of (Work.Tubular.NormalTotal E) :=
  TopCat.ofHom ⟨Work.ThomBordism.radialRescale E (clampCoeff ε),
    continuous_radialRescale_clampCoeff (E := E) (ε := ε) hε⟩

/-- The clamping, as a self-map of the punctured normal total space. -/
noncomputable def clampSubMap (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (hε : 0 < ε) :
    TopCat.of ↥(Work.Tubular.normalNonzero E) ⟶ TopCat.of ↥(Work.Tubular.normalNonzero E) :=
  TopCat.ofHom
    ⟨fun p => ⟨Work.ThomBordism.radialRescale E (clampCoeff ε) p.1,
        Work.ThomBordism.radialRescale_mem_normalNonzero E (clampCoeff ε)
          (clampCoeff_pos hε) p.2⟩,
      Continuous.subtype_mk
        ((continuous_radialRescale_clampCoeff (E := E) (ε := ε) hε).comp
          continuous_subtype_val)
        (fun p => Work.ThomBordism.radialRescale_mem_normalNonzero E (clampCoeff ε)
          (clampCoeff_pos hε) p.2)⟩

/-- **The clamping is homotopic to the identity**, through rescalings which preserve `ν ∖ 0` at
every time. -/
noncomputable def clampHomTop (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (hε : 0 < ε) :
    TopCat.Homotopy (clampMap (E := E) (ε := ε) hε)
      (𝟙 (TopCat.of (Work.Tubular.NormalTotal E))) :=
  { toContinuousMap :=
      Work.ThomBordism.radialRescaleHomotopy E (clampCoeff ε) (continuous_clampCoeff hε)
    map_zero_left := fun p => by
      show Work.ThomBordism.radialRescaleHomotopy E (clampCoeff ε)
          (continuous_clampCoeff hε) ((0 : unitInterval), p)
        = (clampMap (E := E) (ε := ε) hε) p
      rw [Work.ThomBordism.radialRescaleHomotopy_apply,
        Work.ThomBordism.radialRescaleHomotopyFun_zero]
      rfl
    map_one_left := fun p => by
      show Work.ThomBordism.radialRescaleHomotopy E (clampCoeff ε)
          (continuous_clampCoeff hε) ((1 : unitInterval), p)
        = (𝟙 (TopCat.of (Work.Tubular.NormalTotal E))) p
      rw [Work.ThomBordism.radialRescaleHomotopy_apply,
        Work.ThomBordism.radialRescaleHomotopyFun_one]
      rfl }

theorem clampHomTop_mem (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ t x, x ∈ Work.Tubular.normalNonzero E →
      clampHomTop (E := E) (ε := ε) hε (t, x) ∈ Work.Tubular.normalNonzero E :=
  fun _ _ hx => Work.ThomBordism.radialRescaleHomotopyFun_mem_normalNonzero E (clampCoeff ε)
    (clampCoeff_pos hε) hx

/-- **The clamping retraction followed by the tube inverse is the radial clamping.**
The composite `ν → C.U → ν` of the clamping retraction `psiMap` with the tube inverse `C.inv` sends
`p` to `C.inv (tubeMap (clamp p)) = clamp p`, i.e. to the fibrewise rescaling of `p` by
`ε / max ‖p‖ ε`. -/
theorem psiMap_comp_tubeInvMap_apply
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (hε : 0 < ε)
    (C : Work.Tubular.TubeChart E ε) (p : Work.Tubular.NormalTotal E) :
    (Work.ThomBordism.psiMap (E := E) (ε := ε) hε C
      ≫ TopCat.ofHom (Work.ThomBordism.tubeInvMap E C)) p
      = Work.ThomBordism.radialRescale E (clampCoeff ε) p := by
  have hle : Work.Tubular.normalNorm E
      (Work.ThomBordism.nsmul (Work.ThomBordism.clampScale (ε := ε) p) p) ≤ ε := by
    rw [Work.ThomBordism.nsmul_norm, Real.norm_eq_abs,
      abs_of_nonneg (Work.ThomBordism.clampScale_nonneg hε p)]
    exact Work.ThomBordism.clampScale_mul_norm_le hε p
  have h1 : ((Work.ThomBordism.psiFun (E := E) (ε := ε) hε C p : ↥C.U) :
        Work.Tubular.Euc (8 + k))
      = Work.Tubular.tubeMap E
          (Work.ThomBordism.nsmul (Work.ThomBordism.clampScale (ε := ε) p) p) := rfl
  show C.inv ((Work.ThomBordism.psiFun (E := E) (ε := ε) hε C p : ↥C.U) :
    Work.Tubular.Euc (8 + k)) = _
  rw [h1, C.inv_tubeMap _ hle]
  exact (radialRescale_clampCoeff_eq_nsmul (E := E) (ε := ε) p).symm

/-- The composite of the clamping with the tube inverse is the clamping. -/
theorem psiMap_comp_tubeInvMap
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (hε : 0 < ε)
    (C : Work.Tubular.TubeChart E ε) :
    Work.ThomBordism.psiMap (E := E) (ε := ε) hε C
      ≫ TopCat.ofHom (Work.ThomBordism.tubeInvMap E C)
      = clampMap (E := E) (ε := ε) hε := by
  apply TopCat.ext
  intro p
  show (Work.ThomBordism.psiMap (E := E) (ε := ε) hε C
      ≫ TopCat.ofHom (Work.ThomBordism.tubeInvMap E C)) p = (clampMap (E := E) (ε := ε) hε) p
  rw [psiMap_comp_tubeInvMap_apply (E := E) (ε := ε) hε C p]
  rfl

/-- The composite of the clamping with the tube inverse, on the punctured parts, is the clamping. -/
theorem psiSubMap_comp_tubeInvSub
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (hε : 0 < ε)
    (C : Work.Tubular.TubeChart E ε) :
    Work.ThomBordism.psiSubMap (E := E) (ε := ε) hε C ≫ Work.ThomBordism.tubeInvSub E C
      = clampSubMap (E := E) (ε := ε) hε := by
  apply TopCat.ext
  intro p
  apply Subtype.ext
  exact psiMap_comp_tubeInvMap_apply (E := E) (ε := ε) hε C
    (p : Work.Tubular.NormalTotal E)

/-- The chain map of the pair `(C.U, tubeInvPunct) → (ν, ν∖0)` induced by the tube inverse `C.inv`
(the chain-level avatar of `Work.ThomBordism.tubeInvHomology`). -/
noncomputable def tubeInvChain
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) :
    Work.Cohomology.relChains (TopCat.of ↥C.U) (Work.ThomBordism.tubeInvPunct E C) ⟶
      Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) :=
  Work.Cohomology.relChainsMapOf (TopCat.of ↥C.U) (TopCat.of (Work.Tubular.NormalTotal E))
    (Work.ThomBordism.tubeInvPunct E C) (Work.Tubular.normalNonzero E)
    (TopCat.ofHom (Work.ThomBordism.tubeInvMap E C)) (Work.ThomBordism.tubeInvSub E C)
    (Work.ThomBordism.tubeInv_compat E C)

/-- The chain map of the pair `(ν, ν∖0) → (C.U, tubeInvPunct)` induced by the clamping retraction
`psiMap` (a *strict* left inverse of the tube inverse). -/
noncomputable def psiChain
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ} (hε : 0 < ε)
    (C : Work.Tubular.TubeChart E ε) :
    Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) ⟶
      Work.Cohomology.relChains (TopCat.of ↥C.U) (Work.ThomBordism.tubeInvPunct E C) :=
  Work.Cohomology.relChainsMapOf (TopCat.of (Work.Tubular.NormalTotal E)) (TopCat.of ↥C.U)
    (Work.Tubular.normalNonzero E) (Work.ThomBordism.tubeInvPunct E C)
    (Work.ThomBordism.psiMap (E := E) (ε := ε) hε C)
    (Work.ThomBordism.psiSubMap (E := E) (ε := ε) hε C)
    (Work.ThomBordism.psi_spec (E := E) (ε := ε) hε C)

theorem tubeInvHomology_eq_chain
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) :
    Work.ThomBordism.tubeInvHomology E C
      = (HomologicalComplex.homologyMap (tubeInvChain E C) (k + 8)).hom := rfl

/-- **The tube inverse induces a surjection on relative homology.**

The clamping retraction `psiMap : ν → C.U` is a strict left inverse of `C.inv`, and the composite
`psiMap ≫ C.inv : ν → ν` is the positive fibrewise radial rescaling
`p ↦ (ε / max ‖p‖ ε) • p`, which is homotopic to the identity through maps of the pair
`(ν, ν∖0)` (`clampHomTop`).  Hence on relative homology the two induced maps compose to the
identity, and `tubeInvHomology` is surjective. -/
theorem tubeInvHomology_surjective
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) :
    Function.Surjective (Work.ThomBordism.tubeInvHomology E C) := by
  classical
  have hε : 0 < ε := C.eps_pos
  -- the pair conditions of the two composites at the level of pairs
  have wid : Work.Cohomology.subtypeIncl (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) ≫ 𝟙 (TopCat.of (Work.Tubular.NormalTotal E))
      = 𝟙 (TopCat.of ↥(Work.Tubular.normalNonzero E))
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (Work.Tubular.NormalTotal E))
            (Work.Tubular.normalNonzero E) := by
    rw [Category.id_comp, Category.comp_id]
  have wc : Work.Cohomology.subtypeIncl (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) ≫ clampMap (E := E) (ε := ε) hε
      = clampSubMap (E := E) (ε := ε) hε
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (Work.Tubular.NormalTotal E))
            (Work.Tubular.normalNonzero E) := by
    apply TopCat.ext
    intro a
    rfl
  have w'' : Work.Cohomology.subtypeIncl (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)
        ≫ (Work.ThomBordism.psiMap (E := E) (ε := ε) hε C
            ≫ TopCat.ofHom (Work.ThomBordism.tubeInvMap E C))
      = (Work.ThomBordism.psiSubMap (E := E) (ε := ε) hε C ≫ Work.ThomBordism.tubeInvSub E C)
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (Work.Tubular.NormalTotal E))
            (Work.Tubular.normalNonzero E) := by
    rw [← Category.assoc, Work.ThomBordism.psi_spec (E := E) (ε := ε) hε C, Category.assoc,
      Work.ThomBordism.tubeInv_compat E C, ← Category.assoc]
  -- the composite chain map is the one induced by the clamping
  have hcomp : psiChain (E := E) (ε := ε) hε C ≫ tubeInvChain E C
      = Work.Cohomology.relChainsMapOf (TopCat.of (Work.Tubular.NormalTotal E))
          (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E)
          (Work.Tubular.normalNonzero E) (clampMap (E := E) (ε := ε) hε)
          (clampSubMap (E := E) (ε := ε) hε) wc := by
    unfold psiChain tubeInvChain
    rw [Work.Cohomology.relChainsMapOf_comp
      (X := TopCat.of (Work.Tubular.NormalTotal E)) (Y := TopCat.of ↥C.U)
      (Z := TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E) (Work.ThomBordism.tubeInvPunct E C)
      (Work.Tubular.normalNonzero E)
      (Work.ThomBordism.psiMap (E := E) (ε := ε) hε C)
      (Work.ThomBordism.psiSubMap (E := E) (ε := ε) hε C)
      (Work.ThomBordism.psi_spec (E := E) (ε := ε) hε C)
      (TopCat.ofHom (Work.ThomBordism.tubeInvMap E C)) (Work.ThomBordism.tubeInvSub E C)
      (Work.ThomBordism.tubeInv_compat E C) w'']
    exact Work.ThomBordism.doubleFC.relChainsMapOf_congr
      (psiMap_comp_tubeInvMap (E := E) (ε := ε) hε C)
      (psiSubMap_comp_tubeInvSub (E := E) (ε := ε) hε C) w'' wc
  -- the clamping induces the identity on relative homology
  have hmain := Work.PTGeometric.HOF.relChainsMapOf_homologyMap_eq_of_homotopic
    (A := Work.Tubular.normalNonzero E) (B := Work.Tubular.normalNonzero E)
    (clampSubMap (E := E) (ε := ε) hε)
    (𝟙 (TopCat.of ↥(Work.Tubular.normalNonzero E))) wc wid
    (clampHomTop (E := E) (ε := ε) hε) (clampHomTop_mem (E := E) (ε := ε) hε) (k + 8)
  have hid : HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf (TopCat.of (Work.Tubular.NormalTotal E))
          (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E)
          (Work.Tubular.normalNonzero E) (𝟙 (TopCat.of (Work.Tubular.NormalTotal E)))
          (𝟙 (TopCat.of ↥(Work.Tubular.normalNonzero E))) wid) (k + 8)
      = 𝟙 ((Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E)).homology (k + 8)) := by
    rw [relChainsMapOf_eq_id (Work.Tubular.normalNonzero E)
      (𝟙 (TopCat.of (Work.Tubular.NormalTotal E)))
      (𝟙 (TopCat.of ↥(Work.Tubular.normalNonzero E))) wid rfl rfl,
      HomologicalComplex.homologyMap_id]
  have hhom : HomologicalComplex.homologyMap (psiChain (E := E) (ε := ε) hε C) (k + 8)
        ≫ HomologicalComplex.homologyMap (tubeInvChain E C) (k + 8)
      = 𝟙 ((Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E)).homology (k + 8)) := by
    rw [← HomologicalComplex.homologyMap_comp, hcomp, hmain, hid]
  intro z
  have key : (HomologicalComplex.homologyMap (tubeInvChain E C) (k + 8)).hom
      ((HomologicalComplex.homologyMap (psiChain (E := E) (ε := ε) hε C) (k + 8)).hom z)
      = z := by
    have h1 : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (psiChain (E := E) (ε := ε) hε C) (k + 8)
        ≫ HomologicalComplex.homologyMap (tubeInvChain E C) (k + 8))) z = z := by
      rw [hhom, ModuleCat.hom_id]
      rfl
    rwa [ModuleCat.hom_comp] at h1
  refine ⟨(HomologicalComplex.homologyMap (psiChain (E := E) (ε := ε) hε C) (k + 8)).hom z,
    ?_⟩
  rw [tubeInvHomology_eq_chain (E := E) (k := k) C]
  exact key

theorem tubeInvHomologyCollapse {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R) :
    ∃ δ : (Work.Cohomology.relChains (TopCat.of ↥C.U)
        (Work.ThomBordism.tubeInvPunct E C)).homology (k + 8),
      Work.ThomBordism.tubeInvHomology E C δ
        = Work.Tubular.collapseRelK8 C g hg hR hbox := by
  obtain ⟨δ, hδ⟩ := tubeInvHomology_surjective (k := k) E C
    (Work.Tubular.collapseRelK8 C g hg hR hbox)
  exact ⟨δ, hδ⟩

end

end Work.ThomBordism
