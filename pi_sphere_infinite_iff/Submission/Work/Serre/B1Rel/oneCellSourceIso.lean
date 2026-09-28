import Mathlib
import Submission.Work.Serre.B1Rel.Defs
import Submission.Work.Serre.SPC.One.pieceTransfer
import Submission.Work.Serre.SPC.One.ModelCompress
import Submission.Work.Serre.SPC.One.discPairStrong
import Submission.Work.Serre.Csr.Base
import Submission.Work.Serre.Csr.Five
import Submission.Work.Serre.Csr.Tools
import Submission.Work.Serre.cubeAmbient_isZero
import Submission.Work.Cohomology.relChainsHomeomorphCompat

set_option synthInstance.maxHeartbeats 400000


set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The source pair of the `1`-cell comparison

For a Serre fibration `q : E → Z` over `Z = attachOneCells Y ι f` and the `i`-th open cell
`o = cellInteriorOne Y ι f i` with centre `c`, the relative rational homology of the source pair
`(q⁻¹'o, q⁻¹'(o ∖ {c}))` is, in degree `k+1`, the homology of the fibre of `q` over `c` in degree
`k`, and it vanishes below degree `1`.

The proof compares the source pair with the pullback of `q` along the characteristic map of the
cell (the *transfer*, `Work.Serre.SPC.One.pieceHomeo`), then removes the open-cell restriction
by excision, shrinks the relative part from the punctured interval to its boundary `S⁰` (the
compression of `D¹ ∖ {0}` onto its two endpoints), transports along the affine identification
`I¹ ≅ D¹`, and applies the `E¹`-page computation of the Serre filtration
(`Work.Serre.serreE2d`).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre.B1Rel

noncomputable section

variable {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(Work.Serre.SPC.cellS0, Y)}
variable {E : Type} [TopologicalSpace E] {q : C(E, Work.Serre.SPC.attachOneCells Y ι f)}

/-- The characteristic map of the `i`-th `1`-cell. -/
abbrev chiOne (i : ι) : C(Work.Serre.SPC.cellD1, Work.Serre.SPC.attachOneCells Y ι f) :=
  Work.Serre.SPC.oneCellMap Y ι f i

/-- The pullback of `q` along the characteristic map of the `i`-th cell. -/
abbrev srcPB (i : ι) : Type := Work.StemsB.Pullback q (chiOne (f := f) i)

/-- The pullback space as a `TopCat`. -/
abbrev srcPBT (i : ι) : TopCat := TopCat.of (srcPB (f := f) (q := q) i)

/-- The relative part of the pullback pair over the punctured interval. -/
abbrev srcPunct (i : ι) : Set (srcPB (f := f) (q := q) i) :=
  (Work.StemsB.pullbackSnd q (chiOne (f := f) i)) ⁻¹' Work.Serre.SPC.One.punctDisc

/-- The relative part of the pullback pair over the boundary `S⁰` of the interval. -/
abbrev srcS0 (i : ι) : Set (srcPB (f := f) (q := q) i) :=
  (Work.StemsB.pullbackSnd q (chiOne (f := f) i)) ⁻¹' Work.Serre.SPC.One.cellS0Set

/-- The centre of the model interval `I¹`, which the affine identification `I¹ ≅ D¹` sends to the
centre of `D¹`. -/
def icOneMid : Work.Stems.Cubical.IC 1 := fun _ => ⟨1 / 2, by norm_num⟩

theorem icOneToD1_icOneMid :
    Work.Serre.SPC.One.icOneToD1 icOneMid = Work.Serre.SPC.One.cellD1Centre := by
  refine Subtype.ext ?_
  show 2 * ((1 : ℝ) / 2) - 1 = 0
  norm_num

/-- The base map of the cube model: the characteristic map precomposed with the homeomorphism
`I¹ ≅ D¹`. -/
abbrev tauOne (i : ι) : C(Work.Stems.Cubical.IC 1, Work.Serre.SPC.attachOneCells Y ι f) :=
  (chiOne (f := f) i).comp Work.Serre.SPC.One.icOneToD1

/-- The centre of the `i`-th cell, as a point of the attached space. -/
abbrev centreOne (i : ι) : Work.Serre.SPC.attachOneCells Y ι f :=
  Work.Serre.SPC.One.oneCellCentreOne Y ι f i

/-- The centre of the cube model, as a point of the pullback. -/
abbrev srcTauT (i : ι) : TopCat := TopCat.of (Work.StemsB.Pullback q (tauOne (f := f) i))

theorem tauOne_mid (i : ι) : tauOne (f := f) i icOneMid = centreOne (f := f) i := by
  show (chiOne (f := f) i) (Work.Serre.SPC.One.icOneToD1 icOneMid) = _
  rw [icOneToD1_icOneMid]
  rfl

/-- The boundary `S⁰` of the model interval is contained in the punctured interval. -/
theorem cellS0Set_subset_punctDisc :
    Work.Serre.SPC.One.cellS0Set ⊆ Work.Serre.SPC.One.punctDisc := by
  rintro x ⟨z, rfl⟩
  rw [Work.Serre.SPC.One.mem_punctDisc]
  intro h
  have h1 : ((Work.Serre.SPC.cellS0ToD1 z : Work.Serre.SPC.cellD1) : ℝ) = 0 := by
    have hh := congrArg (fun w : Work.Serre.SPC.cellD1 => (w : ℝ)) h
    simpa [Work.Serre.SPC.One.cellD1Centre] using hh
  have h2 := Work.Serre.SPC.One.norm_cellS0ToD1 z
  rw [h1] at h2
  norm_num at h2

/-- The pullback of a Serre fibration along the characteristic map is a Serre fibration. -/
theorem serre_pullbackSnd (hq : Work.StemsB.IsSerreFibration q) (i : ι) :
    Work.StemsB.IsSerreFibration (Work.StemsB.pullbackSnd q (chiOne (f := f) i)) :=
  fun d => Work.StemsB.hasHLP_pullback q (chiOne (f := f) i) (hq d)

/-! ## The chain of comparisons -/

/-- **The transfer**: the source pair is the restricted pullback along the characteristic map. -/
theorem oneCellSource_pieceIso (i : ι) (m : ℕ) :
    Nonempty (((Work.Cohomology.relChains
        (TopCat.of ↥(q ⁻¹' Work.Serre.OneCell.cellInteriorOne Y ι f i))
        (srcRelOne Y ι f q i)).homology m)
      ≅ ((Work.Cohomology.relChains
        (TopCat.of ↥(Work.Serre.SPC.One.pullCell (f := f) (q := q) i))
        (Work.Serre.SPC.One.pullCellRel (f := f) (q := q) i)).homology m)) :=
  Work.Cohomology.relChainsHomeomorphCompat
    (X := ↥(q ⁻¹' Work.Serre.OneCell.cellInteriorOne Y ι f i))
    (Y := ↥(Work.Serre.SPC.One.pullCell (f := f) (q := q) i))
    (srcRelOne Y ι f q i)
    (Work.Serre.SPC.One.pullCellRel (f := f) (q := q) i)
    (Work.Serre.SPC.One.pieceHomeo (f := f) (q := q) i)
    (fun x => (Work.Serre.SPC.One.mem_pieceXrel_iff (f := f) (q := q) i x).trans Iff.rfl) m

/-- **The excision step**: the restricted pullback pair over the open cover
`{cellInnerOne, punctDisc}` has the relative homology of the pullback over the punctured interval. -/
theorem oneCellSource_excIso (i : ι) (m : ℕ) :
    Nonempty (((Work.Cohomology.relChains
        (TopCat.of ↥(Work.Serre.SPC.One.pullCell (f := f) (q := q) i))
        (Work.Serre.SPC.One.pullCellRel (f := f) (q := q) i)).homology m)
      ≅ ((Work.Cohomology.relChains (srcPBT (f := f) (q := q) i)
        (srcPunct (f := f) (q := q) i)).homology m)) := by
  haveI := Work.Cohomology.excision_relChainsMap_isIso
    (srcPBT (f := f) (q := q) i)
    (Work.Serre.SPC.One.pullCell (f := f) (q := q) i)
    (srcPunct (f := f) (q := q) i)
    (Work.Serre.SPC.One.isOpen_pullCell (f := f) (q := q) i)
    (Work.Serre.SPC.One.isOpen_pullPunct (f := f) (q := q) i)
    (Work.Serre.SPC.One.pullCell_union_pullPunct (f := f) (q := q) i) m
  exact ⟨asIso (HomologicalComplex.homologyMap
    (Work.Cohomology.relChainsMap (srcPBT (f := f) (q := q) i)
      (Work.Serre.SPC.One.pullCell (f := f) (q := q) i)
      (srcPunct (f := f) (q := q) i)) m)⟩

/-- **The relative part shrinks to `S⁰`**: the punctured interval compresses onto its two
endpoints, so the inclusion `π⁻¹'S⁰ ↪ π⁻¹'(D¹ ∖ {0})` is a quasi-isomorphism. -/
theorem oneCellSource_punctS0Iso (i : ι) (hq : Work.StemsB.IsSerreFibration q) (m : ℕ) :
    Nonempty (((Work.Cohomology.relChains (srcPBT (f := f) (q := q) i)
        (srcPunct (f := f) (q := q) i)).homology m)
      ≅ ((Work.Cohomology.relChains (srcPBT (f := f) (q := q) i)
        (srcS0 (f := f) (q := q) i)).homology m)) := by
  have hsub : srcS0 (f := f) (q := q) i ⊆ srcPunct (f := f) (q := q) i :=
    Set.preimage_mono cellS0Set_subset_punctDisc
  have hg : ∀ k, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of ↥(srcS0 (f := f) (q := q) i))
        (TopCat.of ↥(srcPunct (f := f) (q := q) i))
        (TopCat.ofHom (Work.Serre.subtypeInclCM hsub))) k) :=
    fun k => Work.Serre.isIso_subtypeIncl_of_isZero_relChains hsub
      (fun j => Work.Serre.isZero_relChains_preimage_of_base_compress
        (Work.StemsB.pullbackSnd q (chiOne (f := f) i))
        (serre_pullbackSnd (f := f) (q := q) hq i)
        Work.Serre.SPC.One.cellS0Set Work.Serre.SPC.One.punctDisc
        cellS0Set_subset_punctDisc
        (fun d => Work.Serre.SPC.One.compressRel_punctDisc d) j) k
  have hf : ∀ k, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (srcPBT (f := f) (q := q) i)
        (srcPBT (f := f) (q := q) i) (𝟙 (srcPBT (f := f) (q := q) i))) k) := by
    intro k
    have hid : Work.Cohomology.chainMap ℤ (srcPBT (f := f) (q := q) i)
        (srcPBT (f := f) (q := q) i) (𝟙 (srcPBT (f := f) (q := q) i))
        = 𝟙 (Work.Cohomology.singularChains ℤ (srcPBT (f := f) (q := q) i)) := by
      rw [Work.Cohomology.chainMap]
      exact CategoryTheory.Functor.map_id _ _
    rw [hid, HomologicalComplex.homologyMap_id]
    infer_instance
  have hw : Work.Cohomology.subtypeIncl (srcPBT (f := f) (q := q) i)
        (srcS0 (f := f) (q := q) i) ≫ 𝟙 (srcPBT (f := f) (q := q) i)
      = TopCat.ofHom (Work.Serre.subtypeInclCM hsub) ≫
        Work.Cohomology.subtypeIncl (srcPBT (f := f) (q := q) i)
          (srcPunct (f := f) (q := q) i) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro y
    exact Subtype.ext rfl
  haveI hrel := Work.Cohomology.relChainsMapOf_homologyMap_isIso
    (srcS0 (f := f) (q := q) i) (srcPunct (f := f) (q := q) i)
    (𝟙 (srcPBT (f := f) (q := q) i))
    (TopCat.ofHom (Work.Serre.subtypeInclCM hsub)) hw m hf
    (by intro k; rw [Work.Serre.subtypeInclCM]; exact hg k)
  exact ⟨(asIso (HomologicalComplex.homologyMap
    (Work.Cohomology.relChainsMapOf
      (srcPBT (f := f) (q := q) i) (srcPBT (f := f) (q := q) i)
      (srcS0 (f := f) (q := q) i) (srcPunct (f := f) (q := q) i)
      (𝟙 (srcPBT (f := f) (q := q) i))
      (TopCat.ofHom (Work.Serre.subtypeInclCM hsub)) hw) m)).symm⟩

/-- **The identification with the cube pair**: the pullback over `(D¹, S⁰)` is the pullback of `q`
along `χ ∘ (I¹ ≅ D¹)` over the pair `(I¹, ∂I¹)`. -/
theorem oneCellSource_cubeIso (i : ι) (m : ℕ) :
    Nonempty (((Work.Cohomology.relChains (srcTauT (f := f) (q := q) i)
        (Work.Serre.pbPre q (tauOne (f := f) i) (Work.Serre.cubeBdryS 1))).homology m)
      ≅ ((Work.Cohomology.relChains (srcPBT (f := f) (q := q) i)
        (srcS0 (f := f) (q := q) i)).homology m)) :=
  Work.Cohomology.relChainsHomeomorphCompat
    (X := Work.StemsB.Pullback q (tauOne (f := f) i))
    (Y := srcPB (f := f) (q := q) i)
    (Work.Serre.pbPre q (tauOne (f := f) i) (Work.Serre.cubeBdryS 1))
    (srcS0 (f := f) (q := q) i)
    (Work.Serre.SPC.One.pbH1 q (chiOne (f := f) i))
    (fun x => Work.Serre.SPC.One.pbH1_mem q (chiOne (f := f) i) x) m

/-! ## The `E¹` page computation and the assembled chain -/

/-- **The `E¹`-page computation** (`Work.Serre.serreE2d`) transported to the pullback of `q` along
the characteristic map: the relative homology of the cube pair in degree `k+1` is the homology of
the fibre over the centre of the cell in degree `k`. -/
theorem oneCellSource_e2Iso (i : ι) (hq : Work.StemsB.IsSerreFibration q) (k : ℕ) :
    Nonempty (((Work.Cohomology.relChains (srcTauT (f := f) (q := q) i)
        (Work.Serre.pbPre q (tauOne (f := f) i) (Work.Serre.cubeBdryS 1))).homology (k + 1))
      ≅ ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.StemsB.fibre q (centreOne (f := f) i)))).homology k)) := by
  obtain ⟨e⟩ := Work.Serre.serreE2d E (Work.Serre.SPC.attachOneCells Y ι f) q 1 hq
    (tauOne (f := f) i) icOneMid k
  exact ⟨e ≪≫ eqToIso (congrArg (fun b => (Work.Cohomology.singularChains ℤ
    (TopCat.of (Work.StemsB.fibre q b))).homology k) (tauOne_mid (f := f) i))⟩

/-- **The assembled source computation over `ℤ`.** -/
theorem oneCellSource_srcZ_iso (i : ι) (hq : Work.StemsB.IsSerreFibration q) (k : ℕ) :
    Nonempty (((Work.Cohomology.relChains
        (TopCat.of ↥(q ⁻¹' Work.Serre.OneCell.cellInteriorOne Y ι f i))
        (srcRelOne Y ι f q i)).homology (k + 1))
      ≅ ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.StemsB.fibre q (centreOne (f := f) i)))).homology k)) := by
  obtain ⟨e1⟩ := oneCellSource_pieceIso (f := f) (q := q) i (k + 1)
  obtain ⟨e2⟩ := oneCellSource_excIso (f := f) (q := q) i (k + 1)
  obtain ⟨e3⟩ := oneCellSource_punctS0Iso (f := f) (q := q) i hq (k + 1)
  obtain ⟨e4⟩ := oneCellSource_cubeIso (f := f) (q := q) i (k + 1)
  obtain ⟨e5⟩ := oneCellSource_e2Iso (f := f) (q := q) i hq k
  exact ⟨e1 ≪≫ e2 ≪≫ e3 ≪≫ e4.symm ≪≫ e5⟩

/-- **The vanishing of the source pair below degree `1` over `ℤ`.** -/
theorem oneCellSource_srcZ_isZero (i : ι) (hq : Work.StemsB.IsSerreFibration q) (m : ℕ)
    (hm : m < 1) :
    IsZero ((Work.Cohomology.relChains
      (TopCat.of ↥(q ⁻¹' Work.Serre.OneCell.cellInteriorOne Y ι f i))
      (srcRelOne Y ι f q i)).homology m) := by
  obtain ⟨e1⟩ := oneCellSource_pieceIso (f := f) (q := q) i m
  obtain ⟨e2⟩ := oneCellSource_excIso (f := f) (q := q) i m
  obtain ⟨e3⟩ := oneCellSource_punctS0Iso (f := f) (q := q) i hq m
  obtain ⟨e4⟩ := oneCellSource_cubeIso (f := f) (q := q) i m
  exact (Work.Serre.cubeAmbient_isZero 1 E (Work.Serre.SPC.attachOneCells Y ι f) q hq
    (tauOne (f := f) i) m (by omega)).of_iso (e1 ≪≫ e2 ≪≫ e3 ≪≫ e4.symm)

/-! ## The target -/

theorem oneCellSourceIso (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.Serre.cellSphereZero, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.Serre.attachOneCells Y ι f)) (hq : Work.StemsB.IsSerreFibration q) (i : ι) :
    (∀ k : ℕ, Nonempty ((Work.Serre.B1Rel.srcOne Y ι f q i).homology (k + 1) ≅
      (Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q (Work.Serre.OneCell.oneCellCentreOne Y ι f i)))).homology k)) ∧
    (∀ m : ℕ, m < 1 → CategoryTheory.Limits.IsZero
      ((Work.Serre.B1Rel.srcOne Y ι f q i).homology m)) := by
  constructor
  · intro k
    obtain ⟨eR⟩ := Work.Serre.Csr.relChainsRHomologyIsoRat
      (TopCat.of ↥(q ⁻¹' Work.Serre.OneCell.cellInteriorOne Y ι f i)) (srcRelOne Y ι f q i) (k + 1)
    obtain ⟨eZ⟩ := oneCellSource_srcZ_iso (f := f) (q := q) i hq k
    obtain ⟨eA⟩ := Work.Serre.Csr.absHomologyIsoRat
      (TopCat.of (Work.StemsB.fibre q (Work.Serre.OneCell.oneCellCentreOne Y ι f i))) k
    exact ⟨eR ≪≫ Work.StemsB.IntRatF.mapIso eZ ≪≫ eA.symm⟩
  · intro m hm
    exact Work.Serre.Csr.isZero_relChainsR_rat_of_isZero_int
      (TopCat.of ↥(q ⁻¹' Work.Serre.OneCell.cellInteriorOne Y ι f i)) (srcRelOne Y ι f q i) m
      (oneCellSource_srcZ_isZero (f := f) (q := q) i hq m hm)

end

end Work.Serre.B1Rel
