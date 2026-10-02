import Mathlib
import Submission.Work.ThomBordism.ambientClassDefs
import Submission.Work.Tubular.tubeTransferChain

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.ThomBordism

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ} {ε : ℝ}

/-!
# Injectivity of the tube-inverse map on relative homology

`Work.ThomBordism.tubeInvHomology E C` is the map induced on the relative homology
`H_{k+8}(C.U, C.U ∖ zero section)` by the tube inverse `C.inv`.  The present file proves that it is
injective.

No homotopy theory is needed: the tube inverse admits an explicit **strict** left inverse at the
level of maps of pairs.  The normal bundle is retracted onto its closed `ε`-disc bundle by the
fibrewise rescaling `p ↦ (ε / max ‖p‖ ε) • p`; composing with the tubular map `(x,w) ↦ e x + w`
gives a map of pairs
`Ψ : (ν, ν∖0) → (C.U, C.U ∖ zero section)`
which is a left inverse of the tube inverse `Φ` *on the nose*: on `C.U` one has
`Ψ (Φ y) = tubeMap (clamp (C.inv y)) = tubeMap (C.inv y) = y`, because the clamp fixes all points
of norm `≤ ε`.  Hence `(Φ_*) ≫ (Ψ_*) = 𝟙` on relative homology, and `Φ_*` is injective.
-/

/-! ## Fibrewise rescaling of the normal bundle -/

/-- Fibrewise scalar multiplication on the normal total space. -/
def nsmul {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} (c : ℝ)
    (p : Work.Tubular.NormalTotal E) : Work.Tubular.NormalTotal E :=
  ⟨(p.1.1, c • p.1.2), Submodule.smul_mem _ c p.2⟩

theorem nsmul_norm {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} (c : ℝ)
    (p : Work.Tubular.NormalTotal E) :
    Work.Tubular.normalNorm E (nsmul c p) = ‖c‖ * Work.Tubular.normalNorm E p := by
  simp [Work.Tubular.normalNorm, nsmul, norm_smul]

theorem nsmul_one {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (p : Work.Tubular.NormalTotal E) : nsmul (1 : ℝ) p = p := by
  apply Subtype.ext
  simp [nsmul]

/-- The clamping factor `ε / max ‖p‖ ε`, a positive continuous function. -/
def clampScale {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (p : Work.Tubular.NormalTotal E) : ℝ :=
  ε / max (Work.Tubular.normalNorm E p) ε

theorem clampScale_pos {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} (hε : 0 < ε)
    (p : Work.Tubular.NormalTotal E) : 0 < clampScale (ε := ε) p :=
  div_pos hε (lt_of_lt_of_le hε (le_max_right _ _))

theorem clampScale_nonneg {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} (hε : 0 < ε)
    (p : Work.Tubular.NormalTotal E) : 0 ≤ clampScale (ε := ε) p := (clampScale_pos hε p).le

theorem clampScale_mul_norm_le {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (hε : 0 < ε) (p : Work.Tubular.NormalTotal E) :
    clampScale (ε := ε) p * Work.Tubular.normalNorm E p ≤ ε := by
  rw [clampScale]
  by_cases h : Work.Tubular.normalNorm E p ≤ ε
  · rw [max_eq_right h, div_self (ne_of_gt hε), one_mul]; exact h
  · rw [max_eq_left (le_of_lt (not_le.mp h)),
      div_mul_cancel₀ _ (ne_of_gt (lt_trans hε (not_le.mp h)))]

theorem clampScale_eq_one_of_le {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (hε : 0 < ε) {p : Work.Tubular.NormalTotal E} (h : Work.Tubular.normalNorm E p ≤ ε) :
    clampScale (ε := ε) p = 1 := by
  rw [clampScale, max_eq_right h, div_self (ne_of_gt hε)]

/-- The clamped point stays inside the closed `ε`-disc bundle. -/
def clamp {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (hε : 0 < ε) (p : Work.Tubular.NormalTotal E) : Work.Tubular.NormalDiscSub E ε :=
  ⟨nsmul (clampScale (ε := ε) p) p,
    Work.Tubular.mem_normalClosedDiscSet.mpr (by
      rw [nsmul_norm, Real.norm_eq_abs, abs_of_nonneg (clampScale_nonneg hε p)]
      exact clampScale_mul_norm_le hε p)⟩

theorem clamp_coe {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} (hε : 0 < ε)
    (p : Work.Tubular.NormalTotal E) :
    ((clamp (E := E) (ε := ε) hε p : Work.Tubular.NormalDiscSub E ε) :
        Work.Tubular.NormalTotal E) = nsmul (clampScale (ε := ε) p) p := rfl

theorem clamp_norm {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} (hε : 0 < ε)
    (p : Work.Tubular.NormalTotal E) :
    Work.Tubular.normalNorm E ((clamp (E := E) (ε := ε) hε p :
      Work.Tubular.NormalDiscSub E ε) : Work.Tubular.NormalTotal E)
      = clampScale (ε := ε) p * Work.Tubular.normalNorm E p := by
  rw [clamp_coe, nsmul_norm, Real.norm_eq_abs, abs_of_nonneg (clampScale_nonneg hε p)]

/-- The clamp fixes every point of the closed `ε`-disc bundle. -/
theorem clamp_eq_self {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} (hε : 0 < ε)
    {p : Work.Tubular.NormalTotal E} (h : Work.Tubular.normalNorm E p ≤ ε) :
    ((clamp (E := E) (ε := ε) hε p : Work.Tubular.NormalDiscSub E ε) :
        Work.Tubular.NormalTotal E) = p := by
  rw [clamp_coe, clampScale_eq_one_of_le hε h, nsmul_one]

/-- The clamp preserves the punctured (non-zero) part. -/
theorem clamp_mem_normalNonzero_iff {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (hε : 0 < ε) (p : Work.Tubular.NormalTotal E) :
    ((clamp (E := E) (ε := ε) hε p : Work.Tubular.NormalDiscSub E ε) :
        Work.Tubular.NormalTotal E) ∈ Work.Tubular.normalNonzero E
      ↔ p ∈ Work.Tubular.normalNonzero E := by
  rw [Work.Tubular.mem_normalNonzero, Work.Tubular.mem_normalNonzero, clamp_norm]
  constructor
  · intro h hc; exact h (by rw [hc, mul_zero])
  · intro h hc
    rcases mul_eq_zero.mp hc with h1 | h1
    · exact absurd h1 (ne_of_gt (clampScale_pos hε p))
    · exact h h1

/-! ## Continuity -/

theorem continuous_clampScale {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (hε : 0 < ε) : Continuous (clampScale (ε := ε) : Work.Tubular.NormalTotal E → ℝ) := by
  unfold clampScale
  refine Continuous.div continuous_const
    ((Work.Tubular.continuous_normalNorm E).max continuous_const) ?_
  intro p
  exact ne_of_gt (lt_of_lt_of_le hε (le_max_right _ _))

theorem continuous_clamp {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (hε : 0 < ε) : Continuous (clamp (E := E) (ε := ε) hε) := by
  refine Continuous.subtype_mk (f := fun p : Work.Tubular.NormalTotal E =>
      nsmul (clampScale (ε := ε) p) p) ?_ (fun p => (clamp (E := E) (ε := ε) hε p).2)
  refine Continuous.subtype_mk (f := fun p : Work.Tubular.NormalTotal E =>
      (p.1.1, clampScale (ε := ε) p • p.1.2)) ?_ (fun p => Submodule.smul_mem _ _ p.2)
  exact Continuous.prodMk continuous_subtype_val.fst
    ((continuous_clampScale (E := E) (ε := ε) hε).smul continuous_subtype_val.snd)

/-! ## The left inverse, as a map of pairs -/

/-- Clamp into the disc bundle and map back into the ambient space by the tubular map: a map
`ν → C.U`. -/
def psiFun {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} (hε : 0 < ε)
    (C : Work.Tubular.TubeChart E ε) (p : Work.Tubular.NormalTotal E) : ↥C.U :=
  ⟨Work.Tubular.tubeMap E
      ((clamp (E := E) (ε := ε) hε p : Work.Tubular.NormalDiscSub E ε) :
        Work.Tubular.NormalTotal E),
    C.mem_U ((clamp (E := E) (ε := ε) hε p : Work.Tubular.NormalDiscSub E ε) :
        Work.Tubular.NormalTotal E)
      (Work.Tubular.mem_normalClosedDiscSet.mp (clamp (E := E) (ε := ε) hε p).2)⟩

theorem continuous_psiFun {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (hε : 0 < ε) (C : Work.Tubular.TubeChart E ε) :
    Continuous (psiFun (E := E) (ε := ε) hε C) := by
  refine Continuous.subtype_mk (p := C.U) (f := fun p : Work.Tubular.NormalTotal E =>
      Work.Tubular.tubeMap E
        ((clamp (E := E) (ε := ε) hε p : Work.Tubular.NormalDiscSub E ε) :
          Work.Tubular.NormalTotal E)) ?_
    (fun p => C.mem_U ((clamp (E := E) (ε := ε) hε p : Work.Tubular.NormalDiscSub E ε) :
        Work.Tubular.NormalTotal E)
      (Work.Tubular.mem_normalClosedDiscSet.mp (clamp (E := E) (ε := ε) hε p).2))
  exact (Work.Tubular.continuous_tubeMap E).comp
    (continuous_subtype_val.comp (continuous_clamp (E := E) (ε := ε) hε))

/-- The restriction of `psiFun` to the punctured parts. -/
def psiSubFun {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} (hε : 0 < ε)
    (C : Work.Tubular.TubeChart E ε) (p : ↥(Work.Tubular.normalNonzero E)) :
    ↥(tubeInvPunct E C) :=
  ⟨psiFun (E := E) (ε := ε) hε C (p : Work.Tubular.NormalTotal E), by
    show C.inv (Work.Tubular.tubeMap E ((clamp (E := E) (ε := ε) hε
      (p : Work.Tubular.NormalTotal E) : Work.Tubular.NormalDiscSub E ε) :
        Work.Tubular.NormalTotal E)) ∈ Work.Tubular.normalNonzero E
    rw [C.inv_tubeMap _ (Work.Tubular.mem_normalClosedDiscSet.mp
      (clamp (E := E) (ε := ε) hε (p : Work.Tubular.NormalTotal E)).2)]
    exact (clamp_mem_normalNonzero_iff hε (p : Work.Tubular.NormalTotal E)).2 p.2⟩

theorem continuous_psiSubFun {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (hε : 0 < ε) (C : Work.Tubular.TubeChart E ε) :
    Continuous (psiSubFun (E := E) (ε := ε) hε C) :=
  Continuous.subtype_mk (p := tubeInvPunct E C)
    (f := fun p : ↥(Work.Tubular.normalNonzero E) =>
      psiFun (E := E) (ε := ε) hε C (p : Work.Tubular.NormalTotal E))
    ((continuous_psiFun (E := E) (ε := ε) hε C).comp continuous_subtype_val)
    (fun p => by
      show C.inv (Work.Tubular.tubeMap E ((clamp (E := E) (ε := ε) hε
        (p : Work.Tubular.NormalTotal E) : Work.Tubular.NormalDiscSub E ε) :
          Work.Tubular.NormalTotal E)) ∈ Work.Tubular.normalNonzero E
      rw [C.inv_tubeMap _ (Work.Tubular.mem_normalClosedDiscSet.mp
        (clamp (E := E) (ε := ε) hε (p : Work.Tubular.NormalTotal E)).2)]
      exact (clamp_mem_normalNonzero_iff hε (p : Work.Tubular.NormalTotal E)).2 p.2)

/-- The clamping retraction, as a map of pairs `(ν, ν∖0) → (C.U, C.U ∖ zero section)`. -/
def psiMap {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} (hε : 0 < ε)
    (C : Work.Tubular.TubeChart E ε) :
    TopCat.of (Work.Tubular.NormalTotal E) ⟶ TopCat.of ↥C.U :=
  TopCat.ofHom ⟨psiFun (E := E) (ε := ε) hε C, continuous_psiFun (E := E) (ε := ε) hε C⟩

/-- The restriction of `psiMap` to the punctured parts. -/
def psiSubMap {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} (hε : 0 < ε)
    (C : Work.Tubular.TubeChart E ε) :
    TopCat.of ↥(Work.Tubular.normalNonzero E) ⟶ TopCat.of ↥(tubeInvPunct E C) :=
  TopCat.ofHom ⟨psiSubFun (E := E) (ε := ε) hε C, continuous_psiSubFun (E := E) (ε := ε) hε C⟩

/-- The punctured-part map underlying `tubeInvHomology`, copied verbatim from its definition. -/
def tubeInvSubMap {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) :
    TopCat.of ↥(tubeInvPunct E C) ⟶ TopCat.of ↥(Work.Tubular.normalNonzero E) :=
  TopCat.ofHom
    ⟨fun y : ↥(tubeInvPunct E C) =>
        ⟨C.inv y.1.1, y.2⟩,
      Continuous.subtype_mk ((tubeInvMap E C).continuous.comp continuous_subtype_val)
        (fun y => (show C.inv (↑(y : ↥C.U) : Work.Tubular.Euc (8 + k)) ∈
          Work.Tubular.normalNonzero E from y.2))⟩

theorem psi_spec {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} (hε : 0 < ε)
    (C : Work.Tubular.TubeChart E ε) :
    Work.Cohomology.subtypeIncl (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) ≫ psiMap (E := E) (ε := ε) hε C
      = psiSubMap (E := E) (ε := ε) hε C
        ≫ Work.Cohomology.subtypeIncl (TopCat.of ↥C.U) (tubeInvPunct E C) := by
  apply TopCat.ext
  intro a
  rfl

/-- The clamping retraction is a strict left inverse of the tube inverse. -/
theorem tubeInvMap_comp_psiMap {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (hε : 0 < ε) (C : Work.Tubular.TubeChart E ε) :
    TopCat.ofHom (tubeInvMap E C) ≫ psiMap (E := E) (ε := ε) hε C
      = 𝟙 (TopCat.of ↥C.U) := by
  apply TopCat.ext
  intro y
  refine Subtype.ext ?_
  show Work.Tubular.tubeMap E
      ((clamp (E := E) (ε := ε) hε (C.inv y.1) : Work.Tubular.NormalDiscSub E ε) :
        Work.Tubular.NormalTotal E) = y.1
  rw [clamp_eq_self hε (C.inv_mem y.1 y.2), C.tubeMap_inv y.1 y.2]

theorem tubeInvSubMap_comp_psiSubMap {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (hε : 0 < ε) (C : Work.Tubular.TubeChart E ε) :
    tubeInvSubMap (E := E) C ≫ psiSubMap (E := E) (ε := ε) hε C
      = 𝟙 (TopCat.of ↥(tubeInvPunct E C)) := by
  apply TopCat.ext
  intro y
  refine Subtype.ext (Subtype.ext ?_)
  show Work.Tubular.tubeMap E
      ((clamp (E := E) (ε := ε) hε (C.inv y.1.1) : Work.Tubular.NormalDiscSub E ε) :
        Work.Tubular.NormalTotal E) = y.1.1
  rw [clamp_eq_self hε (C.inv_mem y.1.1 y.1.2), C.tubeMap_inv y.1.1 y.1.2]

/-! ## Two general lemmas on `relChainsMapOf` -/

/-- `relChainsMapOf` of the identity maps is the identity.  (The auxiliary statement is phrased with
the codomain written as an explicit cokernel -- which is what `relChains` unfolds to -- so that the
intermediate goals of the proof are well typed without unfolding.) -/
theorem relChainsMapOf_id {X : TopCat} (A : Set X)
    (w : Work.Cohomology.subtypeIncl X A ≫ 𝟙 X
      = 𝟙 (TopCat.of A) ≫ Work.Cohomology.subtypeIncl X A) :
    Work.Cohomology.relChainsMapOf X X A A (𝟙 X) (𝟙 (TopCat.of A)) w
      = 𝟙 (Work.Cohomology.relChains X A) := by
  have h : Work.Cohomology.relChainsMapOf X X A A (𝟙 X) (𝟙 (TopCat.of A)) w
      = 𝟙 (cokernel (Work.Cohomology.inclChains X A)) := by
    rw [Work.Cohomology.relChainsMapOf]
    apply (cancel_epi (cokernel.π (Work.Cohomology.inclChains X A))).1
    rw [Work.Cohomology.cokernel_π_map]
    rw [show Work.Cohomology.chainMap ℤ X X (𝟙 X)
        = 𝟙 (Work.Cohomology.singularChains ℤ X) from by
      simp only [Work.Cohomology.chainMap, CategoryTheory.Functor.map_id]]
    rw [Category.id_comp, Category.comp_id]
  exact h

/-- `relChainsMapOf` of a map of pairs each of whose components is *equal* to an identity is the
identity. -/
theorem relChainsMapOf_eq_id {X : TopCat} (A : Set X) (f : X ⟶ X)
    (g : TopCat.of A ⟶ TopCat.of A)
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl X A)
    (hf : f = 𝟙 X) (hg : g = 𝟙 (TopCat.of A)) :
    Work.Cohomology.relChainsMapOf X X A A f g w = 𝟙 (Work.Cohomology.relChains X A) := by
  subst hf
  subst hg
  exact relChainsMapOf_id A w

/-- **A map of pairs with a strict left inverse induces an injective map on relative homology.**

This is the abstract form of the argument: if `f : (X,A) → (Y,B)` has a left inverse `f'` on the
nose, then on relative homology `(f_*) ≫ (f'_*) = 𝟙`, so `f_*` is injective. -/
theorem homologyMap_relChainsMapOf_injective_of_retract {X Y : TopCat} {A : Set X} {B : Set Y}
    (f : X ⟶ Y) (g : TopCat.of A ⟶ TopCat.of B)
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B)
    (f' : Y ⟶ X) (g' : TopCat.of B ⟶ TopCat.of A)
    (w' : Work.Cohomology.subtypeIncl Y B ≫ f' = g' ≫ Work.Cohomology.subtypeIncl X A)
    (hf : f ≫ f' = 𝟙 X) (hg : g ≫ g' = 𝟙 (TopCat.of A)) (n : ℕ) :
    Function.Injective
      ((HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf X Y A B f g w) n).hom) := by
  have w'' : Work.Cohomology.subtypeIncl X A ≫ (f ≫ f')
      = (g ≫ g') ≫ Work.Cohomology.subtypeIncl X A := by
    rw [← Category.assoc, w, Category.assoc, w', Category.assoc]
  have hcomp : Work.Cohomology.relChainsMapOf X Y A B f g w
      ≫ Work.Cohomology.relChainsMapOf Y X B A f' g' w' = 𝟙 (Work.Cohomology.relChains X A) := by
    rw [Work.Cohomology.relChainsMapOf_comp A B A f g w f' g' w' w'']
    exact relChainsMapOf_eq_id A (f ≫ f') (g ≫ g') w'' hf hg
  have hhom : HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf X Y A B f g w) n
      ≫ HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf Y X B A f' g' w') n
      = 𝟙 ((Work.Cohomology.relChains X A).homology n) := by
    rw [← HomologicalComplex.homologyMap_comp, hcomp, HomologicalComplex.homologyMap_id]
  haveI : IsSplitMono (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMapOf X Y A B f g w) n) :=
    IsSplitMono.mk' ⟨HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMapOf Y X B A f' g' w') n, hhom⟩
  exact (ModuleCat.mono_iff_injective _).1 (IsSplitMono.mono _)

/-! ## The target -/

theorem tubeInvHomology_injective {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) :
    Function.Injective (Work.ThomBordism.tubeInvHomology E C) := by
  have hε : 0 < ε := C.eps_pos
  have hinj := homologyMap_relChainsMapOf_injective_of_retract
    (X := TopCat.of ↥C.U) (Y := TopCat.of (Work.Tubular.NormalTotal E))
    (A := tubeInvPunct E C) (B := Work.Tubular.normalNonzero E)
    (TopCat.ofHom (tubeInvMap E C)) (tubeInvSubMap (E := E) C)
    (by apply TopCat.ext; intro a; rfl)
    (psiMap (E := E) (ε := ε) hε C) (psiSubMap (E := E) (ε := ε) hε C) (psi_spec hε C)
    (tubeInvMap_comp_psiMap hε C) (tubeInvSubMap_comp_psiSubMap hε C) (k + 8)
  exact hinj

end

end Work.ThomBordism
