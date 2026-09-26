import Mathlib
import Submission.Work.Drive.Mono.Geom3Defs
import Submission.Work.Drive.Mono.junctionGenC_of_geom2DataPlus
import Submission.Work.Drive.Mono.DataPackageSpheres
import Submission.Work.Drive.Mono.DichotomyB
import Submission.Work.Drive.Mono.ae_cutTransverse
import Submission.Work.Drive.Mono.ae_noCritValue_near
import Submission.Work.Drive.Mono.exists_badLevels
import Submission.Work.Drive.Mono.geom3Data_exists

/-!
# The `BoxGenE` data producer of the third package `GoodDataPackage3`

`Work.Drive.Mono.goodSweepGeom3_holds : ∀ p q, Work.Drive.Mono.GoodSweepGeomAEG3 p q` is the
`BoxGenE` data producer of the corrected bundle of the (L) route: at every crux configuration, at a
box level in general position for the junction route, for almost every cutting level `u` there are
tilt data satisfying `Work.Drive.Mono.GoodDataPackage3` (`DataPackage`, `GoodSweepData3` — the event
structure of the three types with `EdgeFree`, the universal `SlabBoxCrossReg`, `GammaTransverse`,
`FaceRegClosed`, `offK` for all three types, *one event per level* and `SphereCoverAt` at every
level — and the level count at *every* level of the window).  See
`Submission/Work/Drive/Mono/Geom3Defs.lean` for the interface and the producer statement
`Work.Drive.Mono.Geom3DataExists`, and the docstring of `goodSweepGeom3_of_producer` below for the
assembly. -/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- **`Geom2Data` is monotone in the exceptional set**: all clauses but the first (`TiltData`), the
fifth non-grazing clause and the level count are independent of `exc`.  (Rehomed here: the module
`Mono/goodSweepGeom2_holds.lean` that used to carry it has been retired.) -/
theorem geom2Data_mono_exc {ψ : Submission.Diffeo} {K : Knot} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc exc' : Finset ℝ}
    {lam0 lam1 : ℝ} {p q : ℕ} (hsub : (exc : Set ℝ) ⊆ (exc' : Set ℝ))
    (hB : ∀ t ∈ exc', lam0 < t ∧ t < lam1)
    (hG : Geom2Data ψ K s u c σ v h R ℓ exc lam0 lam1 p q) :
    Geom2Data ψ K s u c σ v h R ℓ exc' lam0 lam1 p q := by
  obtain ⟨hT, hwin, hcut, hlne, hthin, hvcl, hband, hcorner, hface, hnb, hng, hwall, hfaceT,
    hexc, hcount, hoffK, hknotGP, hevB, hevF, hevT⟩ := hG
  have hT' : TiltData ψ s c σ u v h R ℓ exc' lam0 lam1 := by
    have h2 := tiltData_mono_exc (B := exc') hT (fun t _ => hB t ‹t ∈ exc'›)
    rwa [Finset.union_eq_right.mpr (Finset.coe_subset.mp hsub)] at h2
  refine ⟨hT', hwin, hcut, hlne, hthin, hvcl, hband, hcorner, hface, hnb, hng, hwall, hfaceT,
    ?_, ?_, hoffK, hknotGP, hevB, hevF, hevT⟩
  · intro t ht hface
    exact hsub (hexc t ht hface)
  · intro lam hlam hne
    exact hcount lam hlam (fun hmem => hne (hsub hmem))

/-- **The assembly**: the producer `Geom3DataExists` gives the third bundle at almost every crux
configuration.  The proof is the one of `Work.Drive.Mono.goodSweepGeom2_of_inputs` (the conversion
`Geom2DataPlus + JunctionGenC → DataPackage ∧ GoodSweepData2`) with the `G3Extra` clauses carried
through the single enlargement of the exceptional set. -/
theorem goodSweepGeom3_of_producer (hdata : Geom3DataExists) :
    ∀ p q : ℕ, Work.Drive.Mono.GoodSweepGeomAEG3 p q := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice hBG hS
  -- the box-sphere trace of the knot is finite, from the crux's count
  have hfin : ({t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      Submission.boxNorm c σ (K.curve t) = s}).Finite := by
    have h1 : ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    have hne : ((↑({t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}.encard) : ENNReal)) ≠ ⊤ :=
      fun hh => h1 (top_le_iff.mp (hh ▸ hS))
    exact Set.encard_lt_top_iff.mp (ENat.toENNReal_lt_top.mp (lt_top_iff_ne_top.mpr hne))
  have hcut_ae : ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      Work.Drive.Mono.CutTransverse K s c σ u :=
    ae_cutTransverse K (lt_trans hr hrs) c σ hfin
  have hδ_ae : ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, deriv (fun r : ℝ => (K.curve r) (σ 2)) t = 0 →
        δ ≤ |(K.curve t) (σ 2) - (c (σ 2) + u)| :=
    ae_noCritValue_near K c σ
  -- the knot lies on the surface
  have hsubK : Set.range K.curve ⊆ (Work.Drive.EpsSphere.torusOf ψ).carrier := by
    rw [himg]
    exact Work.CoreTopology.ClosedCurve.range_subset_carrier _
  filter_upwards [hdata ψ K hr hrs hs c σ p q hp hq d hd hbound hsmall hbox hslice hBG hS hsubK,
    hcut_ae, hδ_ae] with u hdata _hcut _hδ
  intro hu hU
  obtain ⟨v, h, R, ℓ, lam0, lam1, exc, hG, hX, hcall⟩ := hdata hu hU
  -- the junction bundle, with a finite enlargement of the exceptional set
  obtain ⟨B, hBwin, hJun⟩ :=
    junctionGenC_of_geom2DataPlus ψ K hr hrs c σ p q v h R ℓ exc lam0 lam1 hBG.1 hG
  -- the genericity of the level frontier, again with a finite enlargement
  have hGD0 : Geom2Data ψ K s u c σ v h R ℓ exc lam0 lam1 p q := hG.1
  obtain ⟨hT0, hwin, hcut0, hlne, hthin, hvcl, hband, hcorner, hface, hnb, hng, hwall, hfaceT,
    hexc, hcount, hoffK, hknotGP, hevB, hevF, hevT⟩ := hGD0
  obtain ⟨hgen0, hv1, hℓne, hℓv, hsize, hh, hRbox, hlow, hhigh, hl, hexcw⟩ := hT0
  obtain ⟨B2, hB2win, hbad⟩ := exists_badLevels (c := c) (σ := σ) (v := v) (h := h) (ℓ := ℓ)
    (exc := exc ∪ B) (lam0 := lam0) (lam1 := lam1) (s := s) (u := u) hh hℓv hℓne hcut0 hwin
  set exc' : Finset ℝ := (exc ∪ B) ∪ B2 with hexc'def
  have hBwin' : ∀ t ∈ exc', lam0 < t ∧ t < lam1 := by
    intro t ht
    rw [hexc'def, Finset.mem_union] at ht
    rcases ht with ht | ht
    · rw [Finset.mem_union] at ht
      rcases ht with ht | ht
      · exact hexcw t ht
      · exact hBwin t ht
    · exact hB2win t ht
  have hsub : (exc : Set ℝ) ⊆ (exc' : Set ℝ) := by
    intro t ht
    rw [hexc'def]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (by simpa using ht))
  have hG' : Geom2Data ψ K s u c σ v h R ℓ exc' lam0 lam1 p q :=
    geom2Data_mono_exc hsub hBwin' hG.1
  have hJun' : JunctionGenC ψ s c σ u v h ℓ exc' lam0 lam1 := by
    have h1 : (exc ∪ B : Finset ℝ) ⊆ exc' := by
      rw [hexc'def]; exact Finset.subset_union_left
    have h2 : ((exc ∪ B : Finset ℝ) : Set ℝ) ⊆ (exc' : Set ℝ) := by
      rwa [Finset.coe_subset]
    have := junctionGenC_mono_exc (B := exc' \ (exc ∪ B)) hJun
    have hsame : (exc ∪ B) ∪ (exc' \ (exc ∪ B)) = exc' := by
      ext t; constructor
      · intro ht
        rw [Finset.mem_union] at ht
        rcases ht with ht | ht
        · exact h1 ht
        · exact (Finset.mem_sdiff.mp ht).1
      · intro ht
        by_cases hc : t ∈ (exc ∪ B)
        · exact Finset.mem_union_left _ hc
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨ht, hc⟩)
    rwa [hsame] at this
  -- the genericity of the level frontier at the final exceptional set
  have hLF : LevelFrontierGen s c σ u v h ℓ exc' lam0 lam1 :=
    fun lam hlam hne => hbad lam hlam (by rw [hexc'def] at hne ⊢; exact hne)
  obtain ⟨hT', hwin', hcut', hlne', hthin', hvcl', hband', hcorner', hface', hnb', hng', hwall',
    hfaceT', hexc', hcount', hoffK', hknotGP', hevB', hevF', hevT'⟩ := hG'
  have hDP : DataPackage ψ K s u c σ v h R ℓ exc' lam0 lam1 p q :=
    dataPackage_of_levelFrontierGen (lt_trans hr hrs) hT' hcut' hLF hJun' hface' hslice hcount'
  have hGD2 : Work.Drive.Final.GoodSweepData2 ψ K s c σ u v h R ℓ exc' lam0 lam1 :=
    ⟨⟨hT', hcut'.1, hcut'.2, hoffK', hknotGP'⟩, hBG.1, hlne', hevB', hevF', hevT'⟩
  have hGD3 : Work.Drive.Final.GoodSweepData3 ψ K s c σ u v h R ℓ exc' lam0 lam1 := by
    unfold Work.Drive.Final.GoodSweepData3
    exact ⟨hGD2, hX⟩
  exact ⟨v, h, R, ℓ, lam0, lam1, exc', hDP, hGD3, hcall⟩

/-- **The `BoxGenE` data producer of the tilted sweep, in the corrected bundle.**  At every crux
configuration, at a box level in general position for the junction route (`Work.Drive.Mono.BoxGenE`),
for almost every cutting level there are tilt data satisfying `Work.Drive.Mono.GoodDataPackage3`,
i.e. `Work.Drive.Mono.DataPackage` (the tilt data, `JunctionGenC`, the face regularity,
`SlabCutsBox`, the slicing of the box sphere, the disjoint-sphere decomposition of the level frontier
and the level count) together with `Work.Drive.Final.GoodSweepData3` (the three event types with *one
event per level*, `EdgeFree`, the universal `SlabBoxCrossReg`, `GammaTransverse`, `FaceRegClosed`,
`offK` for all three types and the sphere cover `SphereCoverAt` at every level of the window).

This is the producer of BOTH fields of the tilted sweep in the bundle that the (L) route actually
needs (project lead, `Submission/Work/Drive/Final/NOTES_LEAD_L4_L1.md` §2 and §4, and
`Submission/Work/Drive/Mono/NOTES_LEAD_gammaWitness.md` §4–§5).  Its ingredients, all proved:

* the merged witness with the arc clauses: `Work.Drive.Mono.noGraze_witness_arcs`;
* the arcs: `Work.Drive.Mono.gammaArcs_exist`, and `Work.Drive.Mono.gammaArc_noBend` for its
  `hbend` hypothesis;
* the junction bundle: `Work.Drive.Mono.junctionGenC_of_arcs`;
* the edge margin: `Work.Drive.Mono.edgeFree_of_margin` (with `Work.Drive.Mono.exists_unitOrth_avoid`);
* the level count at every level: `Work.Drive.Mono.levelCount_lt_min_all`;
* the disjoint-sphere decomposition of the level frontier:
  `Work.Drive.Mono.levelSphereDecomposition_of_data`;
* the thin-slab data with the face regularity and the width margin:
  `Work.Drive.Mono.tiltData_in_window_export`;
* the universal slab-box crossing: `Work.Drive.Mono.ae_slabBoxCrossReg` (at a.e. half-width in the
  admissible interval).

Route I of `NOTES_LEAD_L4_L1.md` §3 is the intended proof of the "one event per level" clause: take
`(v, n)` from a COUNTABLE family independent of `u`, and for each family member take the conull set of
`(u, h)` on which the clause holds; this is why `u` may be fixed before `(v, n, h)` here.  The three
clauses flagged as unproduced in that note (`hnd`, the type-2 `offK`, and `SphereCoverAt` at the
degenerate levels) are part of this obligation. -/
theorem goodSweepGeom3_holds : ∀ p q : ℕ, Work.Drive.Mono.GoodSweepGeomAEG3 p q := by
  exact goodSweepGeom3_of_producer geom3Data_exists

end

end Work.Drive.Mono
