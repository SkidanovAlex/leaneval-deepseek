import Mathlib
import Submission.Work.ThomBordism.valuePmOneV2Defs
import Submission.Work.ThomBordism.localGenDefs
import Submission.Work.ThomBordism.exists_ne_zero_relH_normalTotal
import Submission.Work.ThomBordism.radialRescale_homologyMap_id
import Submission.Work.ThomBordism.tubeTrans_modelSpan
import Submission.Work.Cohomology.relChainsMapOf_comp
import Submission.Work.ThomBordism.doubleFC.relFactor

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.ThomBordism

open CategoryTheory

/-!
# The relative homology of the tube modulo the punctured core is non-trivial

The target says that `H_{8+k}(C.U, tubeInvPunct E C; ℤ) ≠ 0` for a tubular chart `C` of the normal
bundle of an embedding `E : V ↪ ℝ^{8+k}` of a connected closed oriented smooth `8`-manifold.

The pair `(C.U, tubeInvPunct E C)` is the closed `ε`-disc bundle of the normal bundle relative to
the complement of the zero section; it is a "thickened zero section", and its top relative homology
is the Thom group `H_{8+k}(ν, ν∖0) ≅ H_8(V) ≅ ℤ`
(`Work.ThomBordism.exists_ne_zero_relH_normalTotal`).

## Route

The tube inverse `t := tubeInvMap E C : (C.U, tubeInvPunct) → (ν, ν∖0)` is a map of pairs whose
image is the closed `ε`-disc bundle.  The *radially rescaled* tubular map in the reverse direction,

  `s p = tubeMap E (φ(‖p‖) • p)`,  `φ r = ε / (1 + |r|)`,

maps `(ν, ν∖0)` into `(C.U, tubeInvPunct)` — the rescaling `φ` is chosen so that every rescaled
point has norm `< ε`, hence lands in the closed disc bundle.  The composite
`t ∘ s : (ν, ν∖0) → (ν, ν∖0)` is the positive fibrewise radial rescaling `radialRescale E φ`, which
is *homotopic to the identity through maps of pairs* (`radialRescaleHomotopyTop`).  By homotopy
invariance of the induced map on relative homology
(`Work.PTGeometric.HOF.relChainsMapOf_homologyMap_eq_of_homotopic`) the composite `t_* ∘ s_*` is the
identity on `H_{8+k}(ν, ν∖0)`; in particular `t_*` is surjective, so the image of a non-zero class
is non-zero.

Everything is functoriality of `relChainsMapOf` (`Work.Cohomology.relChainsMapOf_comp`), the
well-definedness of `relChainsMapOf` in its proof argument
(`Work.ThomBordism.doubleFC.relChainsMapOf_congr`), and the elementwise computation
`t_*(y) = (t_* ∘ s_*)(s_* y) = 0` for a hypothetical `s_* y = 0`.
-/

theorem tubeRelChains_tubeInvPunct_nonzero {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (hk : 1 ≤ k) (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    ∃ z : (Work.Cohomology.relChains (TopCat.of ↥C.U)
      (Work.ThomBordism.tubeInvPunct E C)).homology (8 + k), z ≠ 0 := by
  classical
  obtain ⟨y, hy⟩ := Work.ThomBordism.exists_ne_zero_relH_normalTotal (V := V) (k := k) hk E
  -- the rescaling coefficient: everywhere positive and decaying, so that `φ(‖p‖)·‖p‖ < ε`
  let φ : ℝ → ℝ := fun r => ε / (1 + |r|)
  have hφc : Continuous φ := by
    change Continuous (fun r : ℝ => ε / (1 + |r|))
    exact continuous_const.div (continuous_const.add continuous_abs) (by intro r; positivity)
  have hφpos : ∀ r : ℝ, 0 ≤ r → 0 < φ r := by
    intro r hr
    change 0 < ε / (1 + |r|)
    exact div_pos C.eps_pos (by positivity)
  have hcont : Continuous (Work.ThomBordism.radialRescale E φ) :=
    Work.ThomBordism.ttm_continuous_radialRescale E φ hφc
  have hnorm_le : ∀ p : Work.Tubular.NormalTotal E,
      Work.Tubular.normalNorm E (Work.ThomBordism.radialRescale E φ p) ≤ ε := by
    intro p
    have hr0 : 0 ≤ Work.Tubular.normalNorm E p := Work.Tubular.normalNorm_nonneg E p
    rw [Work.ThomBordism.normalNorm_radialRescale]
    have hφr : φ (Work.Tubular.normalNorm E p)
        = ε / (1 + Work.Tubular.normalNorm E p) := by
      change ε / (1 + |Work.Tubular.normalNorm E p|) = ε / (1 + Work.Tubular.normalNorm E p)
      rw [abs_of_nonneg hr0]
    rw [hφr, abs_of_pos (div_pos C.eps_pos (by linarith))]
    rw [div_mul_eq_mul_div,
      div_le_iff₀ (by linarith : (0:ℝ) < 1 + Work.Tubular.normalNorm E p)]
    nlinarith [C.eps_pos.le, hr0]
  -- the radially rescaled tubular map `ν → C.U`
  let sMap : C(Work.Tubular.NormalTotal E, ↥C.U) :=
    ⟨fun p => ⟨Work.Tubular.tubeMap E (Work.ThomBordism.radialRescale E φ p),
        C.mem_U _ (hnorm_le p)⟩,
      Continuous.subtype_mk ((Work.Tubular.continuous_tubeMap E).comp hcont)
        (fun p => C.mem_U _ (hnorm_le p))⟩
  let s : TopCat.of (Work.Tubular.NormalTotal E) ⟶ TopCat.of ↥C.U := TopCat.ofHom sMap
  have hmem_gs : ∀ p : ↥(Work.Tubular.normalNonzero E),
      sMap p.1 ∈ Work.ThomBordism.tubeInvPunct E C := by
    intro p
    show C.inv ((sMap p.1 : ↥C.U) : Work.Tubular.Euc (8 + k)) ∈ Work.Tubular.normalNonzero E
    rw [show ((sMap p.1 : ↥C.U) : Work.Tubular.Euc (8 + k))
          = Work.Tubular.tubeMap E (Work.ThomBordism.radialRescale E φ p.1) from rfl,
        C.inv_tubeMap _ (hnorm_le p.1)]
    exact Work.ThomBordism.radialRescale_mem_normalNonzero E φ hφpos p.2
  let gsMap : C(↥(Work.Tubular.normalNonzero E), ↥(Work.ThomBordism.tubeInvPunct E C)) :=
    ⟨fun p => ⟨sMap p.1, hmem_gs p⟩,
      Continuous.subtype_mk (sMap.continuous.comp continuous_subtype_val) hmem_gs⟩
  let gs : TopCat.of ↥(Work.Tubular.normalNonzero E) ⟶
      TopCat.of ↥(Work.ThomBordism.tubeInvPunct E C) := TopCat.ofHom gsMap
  -- the same rescaling, as a self-map of `ν` and of `ν∖0`
  let ρa : C(Work.Tubular.NormalTotal E, Work.Tubular.NormalTotal E) :=
    ⟨Work.ThomBordism.radialRescale E φ, hcont⟩
  let ρg : C(↥(Work.Tubular.normalNonzero E), ↥(Work.Tubular.normalNonzero E)) :=
    ⟨fun p => ⟨Work.ThomBordism.radialRescale E φ p.1,
        Work.ThomBordism.radialRescale_mem_normalNonzero E φ hφpos p.2⟩,
      Continuous.subtype_mk (hcont.comp continuous_subtype_val)
        (fun p => Work.ThomBordism.radialRescale_mem_normalNonzero E φ hφpos p.2)⟩
  -- the tube inverse undoes the rescaled tubular map
  have hf : (s ≫ TopCat.ofHom (Work.ThomBordism.tubeInvMap E C)) = TopCat.ofHom ρa := by
    apply TopCat.ext
    intro p
    exact C.inv_tubeMap (Work.ThomBordism.radialRescale E φ p) (hnorm_le p)
  have hg : (gs ≫ Work.ThomBordism.tubeInvSub E C) = TopCat.ofHom ρg := by
    apply TopCat.ext
    intro p
    apply Subtype.ext
    exact C.inv_tubeMap (Work.ThomBordism.radialRescale E φ p.1) (hnorm_le p.1)
  -- the three pair compatibilities
  have ws : Work.Cohomology.subtypeIncl (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) ≫ s
      = gs ≫ Work.Cohomology.subtypeIncl (TopCat.of ↥C.U)
          (Work.ThomBordism.tubeInvPunct E C) := by
    apply TopCat.ext; intro p; rfl
  have wrad : Work.Cohomology.subtypeIncl (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) ≫ TopCat.ofHom ρa
      = TopCat.ofHom ρg ≫ Work.Cohomology.subtypeIncl (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E) := by
    apply TopCat.ext; intro p; rfl
  have w'' : Work.Cohomology.subtypeIncl (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)
        ≫ (s ≫ TopCat.ofHom (Work.ThomBordism.tubeInvMap E C))
      = (gs ≫ Work.ThomBordism.tubeInvSub E C)
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (Work.Tubular.NormalTotal E))
            (Work.Tubular.normalNonzero E) := by
    apply TopCat.ext; intro p; rfl
  have wid : Work.Cohomology.subtypeIncl (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) ≫ 𝟙 (TopCat.of (Work.Tubular.NormalTotal E))
      = 𝟙 (TopCat.of ↥(Work.Tubular.normalNonzero E))
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (Work.Tubular.NormalTotal E))
            (Work.Tubular.normalNonzero E) := by
    rw [Category.id_comp, Category.comp_id]
  let RS : Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) ⟶
      Work.Cohomology.relChains (TopCat.of ↥C.U) (Work.ThomBordism.tubeInvPunct E C) :=
    Work.Cohomology.relChainsMapOf (TopCat.of (Work.Tubular.NormalTotal E))
      (TopCat.of ↥C.U) (Work.Tubular.normalNonzero E) (Work.ThomBordism.tubeInvPunct E C)
      s gs ws
  let RT : Work.Cohomology.relChains (TopCat.of ↥C.U)
        (Work.ThomBordism.tubeInvPunct E C) ⟶
      Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) :=
    Work.Cohomology.relChainsMapOf (TopCat.of ↥C.U)
      (TopCat.of (Work.Tubular.NormalTotal E)) (Work.ThomBordism.tubeInvPunct E C)
      (Work.Tubular.normalNonzero E) (TopCat.ofHom (Work.ThomBordism.tubeInvMap E C))
      (Work.ThomBordism.tubeInvSub E C) (Work.ThomBordism.tubeInv_compat E C)
  let Rrad := Work.Cohomology.relChainsMapOf (TopCat.of (Work.Tubular.NormalTotal E))
      (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E)
      (Work.Tubular.normalNonzero E) (TopCat.ofHom ρa) (TopCat.ofHom ρg) wrad
  let Rid := Work.Cohomology.relChainsMapOf (TopCat.of (Work.Tubular.NormalTotal E))
      (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E)
      (Work.Tubular.normalNonzero E) (𝟙 (TopCat.of (Work.Tubular.NormalTotal E)))
      (𝟙 (TopCat.of ↥(Work.Tubular.normalNonzero E))) wid
  -- `RS ≫ RT` is the chain map of the composite map of pairs, which is the radial rescaling
  have hcomp : RS ≫ RT = Rrad := by
    have hX := Work.Cohomology.relChainsMapOf_comp
      (X := TopCat.of (Work.Tubular.NormalTotal E)) (Y := TopCat.of ↥C.U)
      (Z := TopCat.of (Work.Tubular.NormalTotal E))
      (A := Work.Tubular.normalNonzero E) (B := Work.ThomBordism.tubeInvPunct E C)
      (C := Work.Tubular.normalNonzero E)
      s gs ws
      (TopCat.ofHom (Work.ThomBordism.tubeInvMap E C)) (Work.ThomBordism.tubeInvSub E C)
      (Work.ThomBordism.tubeInv_compat E C) w''
    exact hX.trans (Work.ThomBordism.doubleFC.relChainsMapOf_congr hf hg w'' wrad)
  -- the radial rescaling is homotopic to the identity through maps of pairs
  have hhom : HomologicalComplex.homologyMap Rrad (8 + k)
      = HomologicalComplex.homologyMap Rid (8 + k) :=
    Work.PTGeometric.HOF.relChainsMapOf_homologyMap_eq_of_homotopic
      (Work.Tubular.normalNonzero E) (Work.Tubular.normalNonzero E)
      (TopCat.ofHom ρg) (𝟙 (TopCat.of ↥(Work.Tubular.normalNonzero E))) wrad wid
      (Work.ThomBordism.radialRescaleHomotopyTop E φ hφc hcont)
      (fun t p hp => Work.ThomBordism.radialRescaleHomotopyFun_mem_normalNonzero E φ hφpos hp)
      (8 + k)
  have hRid : Rid = 𝟙 (Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E)) := by
    show Work.Cohomology.relChainsMapOf (TopCat.of (Work.Tubular.NormalTotal E))
      (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E)
      (Work.Tubular.normalNonzero E) (𝟙 (TopCat.of (Work.Tubular.NormalTotal E)))
      (𝟙 (TopCat.of ↥(Work.Tubular.normalNonzero E))) wid
      = 𝟙 (Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E))
    unfold Work.Cohomology.relChainsMapOf
    simp only [Work.Cohomology.chainMap, CategoryTheory.Functor.map_id]
    exact CategoryTheory.Limits.cokernel.map_id _ _ _
  have hid : HomologicalComplex.homologyMap Rid (8 + k)
      = 𝟙 ((Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E)).homology (8 + k)) := by
    rw [hRid, HomologicalComplex.homologyMap_id]
  -- hence `hom RT ∘ hom RS = id`, so `hom RT` is surjective and its composite with `hom RS` kills
  -- exactly what `hom RS` kills
  have hfin : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap RT (8 + k))).comp
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap RS (8 + k))) = LinearMap.id := by
    have h2 : ModuleCat.Hom.hom (HomologicalComplex.homologyMap (RS ≫ RT) (8 + k))
        = LinearMap.id := by
      rw [hcomp, hhom, hid]
      exact ModuleCat.hom_id
    rw [← h2, HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp]
  refine ⟨(ModuleCat.Hom.hom (HomologicalComplex.homologyMap RS (8 + k))) y, ?_⟩
  intro hz
  have h1 : ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap RT (8 + k))).comp
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap RS (8 + k)))) y = 0 := by
    show (ModuleCat.Hom.hom (HomologicalComplex.homologyMap RT (8 + k)))
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap RS (8 + k))) y) = 0
    rw [hz, map_zero]
  rw [hfin] at h1
  exact hy (by simpa using h1)

end Work.ThomBordism
