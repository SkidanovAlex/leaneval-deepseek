import Mathlib
import Submission.Work.Serre.Csr.Defs
import Submission.Work.Serre.Csr.Tools
import Submission.Work.Serre.Csr.Five
import Submission.Work.Serre.Csr.csrCompressBase
import Submission.Work.Serre.E2dEngine

/-!
# The chain of the per-cell computation

For the pullback `π` of `q` along the characteristic map of the `i`-th cell, the relative homology of
the preimage pair over `(dOpen n (1/2), dPunct n (1/2))` is isomorphic, in every degree, to that of
the preimage pair over `(dClosed n 1, dSph n 1)`.  This is obtained by the chain of concentric model
pairs
`(dOpen n (1/2), dPunct n (1/2)) → (dOpen n (1/2), dPunctClosed n s) →
 (dClosed n 1, dPunctClosed n s) → (dClosed n 1, dSph n s) → (dClosed n 1, dAnn n s 1) →
 (dClosed n 1, dSph n 1)`,
each step being the five lemma for a map of pairs
(`Work.Serre.Csr.nonempty_homologyIso_relChains_incl`) whose two absolute quasi-isomorphisms come
from the compression engine (`Work.Serre.isZero_relChains_preimage_of_base_compress` together with
`Work.Serre.isIso_subtypeIncl_of_isZero_relChains`) applied to the six compressible base pairs of
`Work.Serre.Csr.csrCompressBase`.
-/

set_option maxHeartbeats 1000000

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open Work.RatHurewicz (cellSphere cellDisk attachCells cellMap)
open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] {ι : Type} {E : Type} [TopologicalSpace E]

/-- **The compression engine for the preimage pairs.**  If the base pair `(W, V)` (subsets of the
model cell) is compressible in every dimension, then the preimage pair `(π⁻¹W, π⁻¹V)` is acyclic
over `ℤ`. -/
theorem csrEngineZero (f : ι → C(cellSphere n, Y)) (q : C(E, attachCells n Y ι f))
    (hq : Work.StemsB.IsSerreFibration q) (i : ι) {W V : Set (cellDisk n)} (hVW : V ⊆ W)
    (hb : ∀ d, Work.RatHurewicz.CompressRel ↥W {x : ↥W | (x : cellDisk n) ∈ V} d) (m : ℕ) :
    IsZero ((Work.Cohomology.relChains (TopCat.of ↥(pPre f q i W))
      {x : ↥(pPre f q i W) | (x : csrPull f q i) ∈ pPre f q i V}).homology m) :=
  isZero_relChains_preimage_of_base_compress (Work.StemsB.pullbackSnd q (cellMap n Y ι f i))
    (csrPull_serre f q hq i) V W hVW hb m

/-- **The absolute quasi-isomorphism of the inclusion of preimages.** -/
theorem csrInclIso (f : ι → C(cellSphere n, Y)) (q : C(E, attachCells n Y ι f))
    (hq : Work.StemsB.IsSerreFibration q) (i : ι) {W V : Set (cellDisk n)} (hVW : V ⊆ W)
    (hb : ∀ d, Work.RatHurewicz.CompressRel ↥W {x : ↥W | (x : cellDisk n) ∈ V} d) :
    ∀ k, IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥(pPre f q i V)) (TopCat.of ↥(pPre f q i W))
      (TopCat.ofHom (subtypeInclCM (Set.preimage_mono hVW)))) k) :=
  isIso_subtypeIncl_of_isZero_relChains (Set.preimage_mono hVW)
    (fun k => csrEngineZero f q hq i hVW hb k)

/-- The inclusion of equal sets is a quasi-isomorphism. -/
theorem csrInclIsoSelf (f : ι → C(cellSphere n, Y)) (q : C(E, attachCells n Y ι f)) (i : ι)
    (W : Set (cellDisk n)) :
    ∀ k, IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥(pPre f q i W)) (TopCat.of ↥(pPre f q i W))
      (TopCat.ofHom (subtypeInclCM (subset_refl _)))) k) := by
  have hEq : (TopCat.ofHom (subtypeInclCM (subset_refl (pPre f q i W)))
      : TopCat.of ↥(pPre f q i W) ⟶ TopCat.of ↥(pPre f q i W)) = 𝟙 _ := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro a
    exact Subtype.ext rfl
  intro k
  rw [hEq, Work.Cohomology.chainMap, CategoryTheory.Functor.map_id,
    HomologicalComplex.homologyMap_id]
  infer_instance

/-- The composite of two inclusions of preimages is a quasi-isomorphism if both factors are. -/
theorem csrInclIsoComp (f : ι → C(cellSphere n, Y)) (q : C(E, attachCells n Y ι f)) (i : ι)
    {U V W : Set (cellDisk n)} (hUV : U ⊆ V) (hVW : V ⊆ W)
    (h₁ : ∀ k, IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥(pPre f q i U)) (TopCat.of ↥(pPre f q i V))
      (TopCat.ofHom (subtypeInclCM (Set.preimage_mono hUV)))) k))
    (h₂ : ∀ k, IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥(pPre f q i V)) (TopCat.of ↥(pPre f q i W))
      (TopCat.ofHom (subtypeInclCM (Set.preimage_mono hVW)))) k)) :
    ∀ k, IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥(pPre f q i U)) (TopCat.of ↥(pPre f q i W))
      (TopCat.ofHom (subtypeInclCM (Set.preimage_mono (hUV.trans hVW))))) k) := by
  intro k
  have hfac : (TopCat.ofHom (subtypeInclCM (Set.preimage_mono (hUV.trans hVW)))
      : TopCat.of ↥(pPre f q i U) ⟶ TopCat.of ↥(pPre f q i W))
      = (TopCat.ofHom (subtypeInclCM (Set.preimage_mono hUV)))
        ≫ (TopCat.ofHom (subtypeInclCM (Set.preimage_mono hVW))) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro a
    rfl
  rw [hfac, Work.Cohomology.chainMap_comp_relChains, HomologicalComplex.homologyMap_comp]
  haveI := h₁ k
  haveI := h₂ k
  infer_instance


/-- One step of the chain in a fixed ambient: enlarging the relative part when the base pair
`(A₁, A₀)` is compressible. -/
theorem csrStepSame (f : ι → C(cellSphere n, Y)) (q : C(E, attachCells n Y ι f))
    (hq : Work.StemsB.IsSerreFibration q) (i : ι) {B A₀ A₁ : Set (cellDisk n)} (hA : A₀ ⊆ A₁)
    (hA₀ : A₀ ⊆ B) (hA₁ : A₁ ⊆ B)
    (hb : ∀ d, Work.RatHurewicz.CompressRel ↥A₁ {x : ↥A₁ | (x : cellDisk n) ∈ A₀} d) (m : ℕ) :
    Nonempty ((Work.Cohomology.relChains (TopCat.of ↥(pPre f q i B))
        {x : ↥(pPre f q i B) | (x : csrPull f q i) ∈ pPre f q i A₀}).homology m ≅
      (Work.Cohomology.relChains (TopCat.of ↥(pPre f q i B))
        {x : ↥(pPre f q i B) | (x : csrPull f q i) ∈ pPre f q i A₁}).homology m) :=
  nonempty_homologyIso_relChains_incl (X := csrPull f q i) (Set.preimage_mono hA) (subset_refl _)
    (Set.preimage_mono hA₀) (Set.preimage_mono hA₁) (csrInclIsoSelf f q i B)
    (csrInclIso f q hq i hA hb) m

/-- One step of the chain changing the ambient, with the relative part fixed. -/
theorem csrStepAmbient (f : ι → C(cellSphere n, Y)) (q : C(E, attachCells n Y ι f))
    (hq : Work.StemsB.IsSerreFibration q) (i : ι) {B₀ B₁ A : Set (cellDisk n)} (hB : B₀ ⊆ B₁)
    (hA₀ : A ⊆ B₀) (hA₁ : A ⊆ B₁)
    (hf : ∀ k, IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥(pPre f q i B₀)) (TopCat.of ↥(pPre f q i B₁))
      (TopCat.ofHom (subtypeInclCM (Set.preimage_mono hB)))) k)) (m : ℕ) :
    Nonempty ((Work.Cohomology.relChains (TopCat.of ↥(pPre f q i B₀))
        {x : ↥(pPre f q i B₀) | (x : csrPull f q i) ∈ pPre f q i A}).homology m ≅
      (Work.Cohomology.relChains (TopCat.of ↥(pPre f q i B₁))
        {x : ↥(pPre f q i B₁) | (x : csrPull f q i) ∈ pPre f q i A}).homology m) :=
  nonempty_homologyIso_relChains_incl (X := csrPull f q i) (subset_refl _) (Set.preimage_mono hB)
    (Set.preimage_mono hA₀) (Set.preimage_mono hA₁) hf
    (csrInclIsoSelf f q i A) m

/-- **The chain of the per-cell computation.** -/
theorem csrDiscChain (f : ι → C(cellSphere n, Y)) (q : C(E, attachCells n Y ι f))
    (hq : Work.StemsB.IsSerreFibration q) (i : ι) (s : ℝ) (hs : 0 < s) (hs2 : s < 1/2) (m : ℕ) :
    Nonempty ((Work.Cohomology.relChains (TopCat.of ↥(pPre f q i (dOpen n (1/2))))
        {x : ↥(pPre f q i (dOpen n (1/2))) |
          (x : csrPull f q i) ∈ pPre f q i (dPunct n (1/2))}).homology m ≅
      (Work.Cohomology.relChains (TopCat.of ↥(pPre f q i (dClosed n 1)))
        {x : ↥(pPre f q i (dClosed n 1)) |
          (x : csrPull f q i) ∈ pPre f q i (dSph n 1)}).homology m) := by
  have hs1 : s ≤ 1 := by linarith
  -- the subset facts
  have h₂₁ : dPunctClosed n s ⊆ dPunct n (1/2) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := mem_dPunctClosed.mp hx
    exact mem_dPunct.mpr ⟨mem_dOpen.mpr (lt_of_le_of_lt hx1 hs2), hx2⟩
  have h₂₀ : dPunctClosed n s ⊆ dOpen n (1/2) := h₂₁.trans (dPunct_subset_dOpen n (1/2))
  have h₁₀ : dPunct n (1/2) ⊆ dOpen n (1/2) := dPunct_subset_dOpen n (1/2)
  have hCs₀ : dClosed n s ⊆ dOpen n (1/2) := dClosed_subset_dOpen hs2
  have h₂Cs : dPunctClosed n s ⊆ dClosed n s := fun x hx => (mem_dPunctClosed.mp hx).1
  have hCsCs : dClosed n s ⊆ dClosed n 1 := by
    intro x hx
    rw [mem_dClosed] at hx ⊢
    linarith
  have h₃₂ : dSph n s ⊆ dPunctClosed n s := by
    intro x hx
    rw [mem_dSph] at hx
    exact mem_dPunctClosed.mpr ⟨le_of_eq hx, by
      rw [← norm_pos_iff, hx]
      exact hs⟩
  have h₃₄ : dSph n s ⊆ dAnn n s 1 := by
    intro x hx
    rw [mem_dSph] at hx
    exact mem_dAnn.mpr ⟨le_of_eq hx.symm, by rw [hx]; linarith⟩
  have h₅₄ : dSph n 1 ⊆ dAnn n s 1 := dSph_subset_dAnn n s 1 hs1
  have h₃₁ : dSph n s ⊆ dClosed n 1 := h₃₂.trans h₂Cs |>.trans hCsCs
  have h₅₁ : dSph n 1 ⊆ dClosed n 1 := dSph_subset_dClosed n 1
  have h₄₁ : dAnn n s 1 ⊆ dClosed n 1 := dAnn_subset_dClosed n s 1
  have h₃₀ : dSph n s ⊆ dClosed n s := h₃₂.trans h₂Cs
  -- the compressibility facts
  have hb₁ : ∀ d, Work.RatHurewicz.CompressRel ↥(dPunct n (1/2))
      {x : ↥(dPunct n (1/2)) | (x : cellDisk n) ∈ dPunctClosed n s} d := by
    intro d
    have h := Work.Serre.Csr.compressRel_dPunct n s hs hs2 d
    rw [show {x : ↥(dPunct n (1/2)) | (x : cellDisk n) ∈ dClosed n s}
        = {x : ↥(dPunct n (1/2)) | (x : cellDisk n) ∈ dPunctClosed n s} from by
      ext x
      simp only [Set.mem_setOf_eq, mem_dPunctClosed, mem_dClosed]
      exact ⟨fun h => ⟨h, x.2.2⟩, fun h => h.1⟩] at h
    exact h
  -- the six steps
  obtain ⟨e₁⟩ := csrStepSame f q hq i (B := dOpen n (1/2)) (A₀ := dPunctClosed n s)
    (A₁ := dPunct n (1/2)) h₂₁ h₂₀ h₁₀ hb₁ m
  obtain ⟨e₂⟩ := csrStepAmbient f q hq i (B₀ := dClosed n s) (B₁ := dOpen n (1/2))
    (A := dPunctClosed n s) hCs₀ h₂Cs h₂₀
    (csrInclIso f q hq i hCs₀ (fun d => Work.Serre.Csr.compressRel_dOpen n s hs hs2 d)) m
  obtain ⟨e₃⟩ := csrStepAmbient f q hq i (B₀ := dClosed n s) (B₁ := dClosed n 1)
    (A := dPunctClosed n s) hCsCs h₂Cs (h₂Cs.trans hCsCs)
    (csrInclIso f q hq i hCsCs (fun d => Work.Serre.Csr.compressRel_dClosed n s hs hs2 d)) m
  obtain ⟨e₄⟩ := csrStepSame f q hq i (B := dClosed n 1) (A₀ := dSph n s)
    (A₁ := dPunctClosed n s) h₃₂ h₃₁ (h₂Cs.trans hCsCs)
    (fun d => Work.Serre.Csr.compressRel_dPunctClosed n s hs hs2 d) m
  obtain ⟨e₅⟩ := csrStepSame f q hq i (B := dClosed n 1) (A₀ := dSph n s)
    (A₁ := dAnn n s 1) h₃₄ h₃₁ h₄₁
    (fun d => Work.Serre.Csr.compressRel_dAnnSph n s hs hs2 d) m
  obtain ⟨e₆⟩ := csrStepSame f q hq i (B := dClosed n 1) (A₀ := dSph n 1)
    (A₁ := dAnn n s 1) h₅₄ h₅₁ h₄₁
    (fun d => Work.Serre.Csr.compressRel_dAnnSphOne n s hs hs2 d) m
  exact ⟨e₁.symm ≪≫ e₂.symm ≪≫ e₃ ≪≫ e₄.symm ≪≫ e₅ ≪≫ e₆.symm⟩

end

end Work.Serre
