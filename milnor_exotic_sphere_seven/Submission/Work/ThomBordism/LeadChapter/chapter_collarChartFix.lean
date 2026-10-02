import Mathlib
import Submission.Work.ThomBordism.LeadChapter.Defs
import Submission.Work.ThomBordism.sourceRegion_extChart_transition_det_pos
import Submission.Work.PTGeometric.LevelModel
import Submission.Work.ThomBordism.LeadChapter.CollarChartDefs
import Submission.Work.ThomBordism.LeadChapter.CollarChartCore
import Submission.Work.ThomBordism.collarChart_continuous_toFun
import Submission.Work.ThomBordism.collarChart_continuous_inv
import Submission.Work.ThomBordism.collarChart_left_inv
import Submission.Work.ThomBordism.collarChart_right_inv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-! Guidance from the project lead (the requester):

CORRECTED S4. The previous statement Work.ThomBordism.LeadChapter.chapter_collarChart (agent H2950) was declared false for ONE formalisation slip, conjunct 7: `g.source = {q | (q : levelModel …) ∈ ψ.source}` elaborated as an IMAGE (`Subtype.val '' g.source = …`) and contradicted conjuncts 2–4. The ONLY change here is that conjunct 7 now reads `g.source = Subtype.val ⁻¹' ψ.source` (the intended preimage).
START FROM H2950's complete development: Submission/Work/ThomBordism/LeadChapter/CollarChartDefs.lean and CollarChartCore.lean (sorry-free; import them) and the proof body in Submission/Work/ThomBordism/LeadChapter/chapter_collarChart.lean. In that body ψ = psiC T, κ = kappaC T, g, hbdry, the κ clauses and clause 9 are all proved; with the corrected conjunct, h7 should be `rfl` (or ext + Iff.rfl). Copy the body, rename the theorem, close h7, and assemble ⟨δ, ψ, κ, g, h1…h9⟩. Verify with `lake build <your module>` and #print axioms. Do not use respectTransparency false.
-/

set_option maxHeartbeats 4000000

namespace Work.ThomBordism.LeadChapter

open Work.PTGeometric

noncomputable section

open Classical in
/-- **The collar chart of the level set at a piece.** -/
def psiCFix {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]
    (T : CollarData k D ι Fam) : OpenPartialHomeomorph (DataLW T) (EuclideanHalfSpace 9) where
  toFun := toFunC T
  invFun := collarW T
  source := srcC T
  target := tgtC T.εcl T.a T.i
  map_source' := fun q hq => toFunC_mem_tgtC T q hq
  map_target' := fun z hz => collarW_mem_srcC T hz
  left_inv' := fun q hq => Work.ThomBordism.collarChart_left_inv T q hq
  right_inv' := fun z hz => Work.ThomBordism.collarChart_right_inv T hz
  open_source := isOpen_srcC T
  open_target := isOpen_tgtC T.εcl T.a T.i
  continuousOn_toFun := Work.ThomBordism.collarChart_continuous_toFun T
  continuousOn_invFun := Work.ThomBordism.collarChart_continuous_inv T

open Classical in
/-- **The interior part of the collar chart** (the `ℝ⁹`-valued chart on the interior points). -/
def kappaCFix {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]
    (T : CollarData k D ι Fam) : OpenPartialHomeomorph (DataLW T) CofAtlas.E9 :=
  (psiCFix T).trans Work.ThomBordism.PosAtlas.intHalf

theorem kappaCFix_source {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]
    (T : CollarData k D ι Fam) :
    (kappaCFix T).source = (psiCFix T).source ∩ {q | 0 < (psiCFix T q).1 0} := by
  rw [kappaCFix, OpenPartialHomeomorph.trans_source]
  rfl

theorem kappaCFix_apply {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]
    (T : CollarData k D ι Fam) {q : DataLW T} (hq : q ∈ (kappaCFix T).source) :
    kappaCFix T q = (psiCFix T q).1 := by
  rw [kappaCFix, OpenPartialHomeomorph.trans_apply]
  rfl


end

open scoped Manifold ContDiff Topology in
open CategoryTheory Work.PTGeometric in
theorem chapter_collarChartFix {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]
    (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1)
    (hphi : SourceRegionPhiInteriorSign k (sourceZeroSet G m hpow)
      (sourceBasepoint (D := D) (Fam := Fam) G m hpow))
    (hweak : ∀ x : EuclideanHalfSpace ((8 + k) + 1), sourcePhi G m hpow hphi x = 0 →
      mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
        (modelWithCornersSelf ℝ ℝ) (sourcePhi G m hpow hphi) x ≠ 0)
    (h : BdryId G m hpow) (hspec : BdryIdSpec G m hpow h)
    (w : (sourceRegionSetup G m hpow hphi hweak).Region → EuclideanSpace ℝ (Fin (k + G.mU)))
    (εcl : ℝ) (hεcl : 0 < εcl)
    (hwv : ∀ x : (sourceRegionSetup G m hpow hphi hweak).Region,
      x.1.1 0 ≤ εcl → w x = vSrc G m hpow x.1.1) :
    (by
      letI : ChartedSpace (EuclideanHalfSpace (8 + k + 1))
          (sourceRegionSetup G m hpow hphi hweak).Region :=
        (sourceRegionSetup G m hpow hphi hweak).chartedSpaceOfRegion
      letI : IsManifold (𝓡∂ (8 + k + 1)) ∞ (sourceRegionSetup G m hpow hphi hweak).Region :=
        (sourceRegionSetup G m hpow hphi hweak).isManifoldOfRegion
      letI : CompactSpace (sourceRegionSetup G m hpow hphi hweak).Region :=
        (sourceRegionSetup G m hpow hphi hweak).compactSpaceOfRegion
      letI : T2Space (sourceRegionSetup G m hpow hphi hweak).Region :=
        (sourceRegionSetup G m hpow hphi hweak).t2SpaceOfRegion
      exact
        ∀ (hWcl : IsClosed {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0})
          (L : LocalLevelData k (sourceRegionSetup G m hpow hphi hweak).Region
            {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0}),
          (by
            letI : ChartedSpace (EuclideanHalfSpace 9)
                (levelModel {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0}
                  hWcl L) :=
              Work.PTGeometric.Lvl.Setup.instChartedSpace
                (levelSetup {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0}
                  hWcl L)
            exact
              ∀ (a : Fin m × ι) (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)),
                ∃ (δ : ℝ) (ψ : OpenPartialHomeomorph
                    (levelModel {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0}
                      hWcl L) (EuclideanHalfSpace 9))
                  (κ : OpenPartialHomeomorph
                    (levelModel {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0}
                      hWcl L) CofAtlas.E9)
                  (g : OpenPartialHomeomorph
                    ↥((modelWithCornersEuclideanHalfSpace 9).boundary
                      (levelModel {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0}
                        hWcl L)) (EuclideanSpace ℝ (Fin 8))),
                  0 < δ ∧
                  ψ.target = {z : EuclideanHalfSpace 9 | z.1 0 < δ ∧
                    tail 8 z.1 ∈ (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.target} ∧
                  (∀ z ∈ ψ.target,
                    (ψ.symm z).1.1.1 = collarPiece G m hpow h a i z.1) ∧
                  (∀ q ∈ ψ.source,
                    q ∈ (modelWithCornersEuclideanHalfSpace 9).boundary
                      (levelModel {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0}
                        hWcl L) ↔ (ψ q).1 0 = 0) ∧
                  κ.source = ψ.source ∩ {q | 0 < (ψ q).1 0} ∧
                  (∀ q ∈ κ.source, κ q = (ψ q).1) ∧
                  g.source = Subtype.val ⁻¹' ψ.source ∧
                  (∀ q ∈ g.source, g q = tail 8 (ψ q).1) ∧
                  (∀ (q : ↥((modelWithCornersEuclideanHalfSpace 9).boundary
                      (levelModel {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0}
                        hWcl L))) (z : (Fam a.2).pt),
                    z ∈ Work.ThomBordism.FrameSigns.src (Fam a.2) i →
                    q.1.1.1.1 = ((h.symm ⟨a, z⟩).1).1 →
                    q ∈ g.source ∧
                      g q = (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 z))) := by
  classical
  intro hWcl L
  intro a i
  let T : CollarData k D ι Fam :=
    { G := G, m := m, hpow := hpow, hphi := hphi, hweak := hweak, h := h,
      a := a, i := i, εcl := εcl, hεcl := hεcl, w := w, hwv := hwv }
  let ψ : OpenPartialHomeomorph
      (levelModel {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0} hWcl L)
      (EuclideanHalfSpace 9) := psiCFix T
  let κ : OpenPartialHomeomorph
      (levelModel {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0} hWcl L)
      CofAtlas.E9 := kappaCFix T
  -- ## the boundary characterization
  have hbdry : ∀ q ∈ ψ.source,
      q ∈ (modelWithCornersEuclideanHalfSpace 9).boundary
          (levelModel {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0} hWcl L) ↔
        (ψ q).1 0 = 0 := by
    intro q hq
    have hqC : q ∈ srcC T := hq
    have h1 : (q ∈ (modelWithCornersEuclideanHalfSpace 9).boundary
          (levelModel {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0} hWcl L)) ↔
        q.1 ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
          (sourceRegionSetup G m hpow hphi hweak).Region :=
      Work.PTGeometric.Lvl.Setup.mem_boundary_iff
        (levelSetup {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0} hWcl L) q
    have h2 : (q.1 ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
          (sourceRegionSetup G m hpow hphi hweak).Region) ↔
        (q.1.1 ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
            (sourceRegionSetup G m hpow hphi hweak).A ∨
          (sourceRegionSetup G m hpow hphi hweak).Φ q.1.1 = 0) :=
      Work.PTGeometric.WeakRegion.RegionSetupWeak.mem_boundary_iff
        (sourceRegionSetup G m hpow hphi hweak) q.1
    have h3 : (q.1.1 ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
          (sourceRegionSetup G m hpow hphi hweak).A) ↔ q.1.1.1 0 = 0 :=
      Work.PTGeometric.mem_boundary_halfSpace_iff ((8 + k) + 1)
    have h4 : (sourceRegionSetup G m hpow hphi hweak).Φ q.1.1 = 0 → q.1.1.1 0 = 0 := by
      intro hΦ0
      have hz : q.1.1 ∈ sourceZeroSet G m hpow := mem_sourceZeroSet_ambient T hqC.1
      exact (sourcePhi_spec G m hpow hphi).2.2.2.2.1 ⟨hz, hΦ0⟩
    have h5 : (ψ q).1 0 = q.1.1.1 0 := toFunC_apply_zero T q hqC
    constructor
    · intro hqbd
      rcases h2.mp (h1.mp hqbd) with h | h
      · rw [h5]; exact h3.mp h
      · rw [h5]; exact h4 h
    · intro h
      have h6 : q.1.1.1 0 = 0 := h5 ▸ h
      exact h1.mpr (h2.mpr (Or.inl (h3.mpr h6)))
  -- ## a boundary point of the level model (the junk value of `g.symm`)
  haveI hconn : ConnectedSpace (Fam a.2).pt := G.hconn a.2
  have hyne : Nonempty (Fam a.2).pt := inferInstance
  let y₀ : (Fam a.2).pt := Classical.arbitrary _
  let xb : ↥(bdryDom G m hpow) := h.symm ⟨a, y₀⟩
  have hxM : (xb : SrcHS k) ∈ sourceZeroSet G m hpow := xb.2.1
  have hΦb : (sourceRegionSetup G m hpow hphi hweak).Φ (xb : SrcHS k) ≤ 0 :=
    (sourcePhi_spec G m hpow hphi).2.1 hxM
  have hw0b : w ⟨(xb : SrcHS k), hΦb⟩ = 0 := by
    have hle : (⟨(xb : SrcHS k), hΦb⟩ :
        (sourceRegionSetup G m hpow hphi hweak).Region).1.1 0 ≤ εcl := by
      show (xb : SrcHS k).1 0 ≤ εcl
      rw [xb.2.2]; exact le_of_lt hεcl
    rw [hwv _ hle]
    exact vSrc_eq_zero_of_mem_core T hxM
  let q₀ : levelModel {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0} hWcl L :=
    ⟨⟨(xb : SrcHS k), hΦb⟩, hw0b⟩
  have hq₀bd : q₀ ∈ (modelWithCornersEuclideanHalfSpace 9).boundary
      (levelModel {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0} hWcl L) := by
    have h1 : (q₀ ∈ (modelWithCornersEuclideanHalfSpace 9).boundary
          (levelModel {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0} hWcl L)) ↔
        q₀.1 ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
          (sourceRegionSetup G m hpow hphi hweak).Region :=
      Work.PTGeometric.Lvl.Setup.mem_boundary_iff
        (levelSetup {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0} hWcl L) q₀
    refine h1.mpr ?_
    have h2 : (q₀.1 ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
          (sourceRegionSetup G m hpow hphi hweak).Region) ↔
        (q₀.1.1 ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
            (sourceRegionSetup G m hpow hphi hweak).A ∨
          (sourceRegionSetup G m hpow hphi hweak).Φ q₀.1.1 = 0) :=
      Work.PTGeometric.WeakRegion.RegionSetupWeak.mem_boundary_iff
        (sourceRegionSetup G m hpow hphi hweak) q₀.1
    refine h2.mpr (Or.inl ?_)
    have h3 : (q₀.1.1 ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
          (sourceRegionSetup G m hpow hphi hweak).A) ↔ q₀.1.1.1 0 = 0 :=
      Work.PTGeometric.mem_boundary_halfSpace_iff ((8 + k) + 1)
    exact h3.mpr xb.2.2
  let x₀ : ↥((modelWithCornersEuclideanHalfSpace 9).boundary
      (levelModel {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0} hWcl L)) :=
    ⟨q₀, hq₀bd⟩
  -- ## the boundary chart
  have gTgtMem : ∀ u : EuclideanSpace ℝ (Fin 8), u ∈ (chartE T.a T.i).target →
      hsTail u ∈ ψ.target := by
    intro u hu
    refine ⟨?_, ?_⟩
    · rw [hsTail_apply_zero]; exact deltaC_pos T.hεcl
    · rw [tail_hsTail]; exact hu
  have gInv (u : EuclideanSpace ℝ (Fin 8)) (hu : u ∈ (chartE T.a T.i).target) :
      ψ.symm (hsTail u) ∈ (modelWithCornersEuclideanHalfSpace 9).boundary
        (levelModel {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0} hWcl L) :=
    (hbdry (ψ.symm (hsTail u)) (ψ.map_target' (gTgtMem u hu))).mpr
      ((congrArg (fun z : EuclideanHalfSpace 9 => z.1 0)
        (ψ.right_inv' (gTgtMem u hu))).trans (hsTail_apply_zero u))
  let gToFun (q : ↥((modelWithCornersEuclideanHalfSpace 9).boundary (levelModel {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0} hWcl L))) : EuclideanSpace ℝ (Fin 8) :=
    Work.PTGeometric.tail 8 (ψ q.1).1
  let gInvFun (u : EuclideanSpace ℝ (Fin 8)) : ↥((modelWithCornersEuclideanHalfSpace 9).boundary (levelModel {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0} hWcl L)) :=
    if hu : u ∈ (chartE T.a T.i).target then ⟨ψ.symm (hsTail u), gInv u hu⟩ else x₀
  let g : OpenPartialHomeomorph ↥((modelWithCornersEuclideanHalfSpace 9).boundary (levelModel {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0} hWcl L)) (EuclideanSpace ℝ (Fin 8)) :=
    { toFun := gToFun
      invFun := gInvFun
      source := {q | (q.1 : (levelModel {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0} hWcl L)) ∈ ψ.source}
      target := (chartE T.a T.i).target
      map_source' := fun q hq => (ψ.map_source' hq).2
      map_target' := fun u hu => by
        have hval : (gInvFun u).1 = ψ.symm (hsTail u) := by
          show (if hu0 : u ∈ (chartE T.a T.i).target then
              (⟨ψ.symm (hsTail u), gInv u hu0⟩ : ↥((modelWithCornersEuclideanHalfSpace 9).boundary (levelModel {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0} hWcl L))) else x₀).1 = ψ.symm (hsTail u)
          rw [dif_pos hu]
        show (gInvFun u).1 ∈ ψ.source
        rw [hval]
        exact ψ.map_target' (gTgtMem u hu)
      left_inv' := fun q hq => by
        have hqbd : (ψ q.1).1 0 = 0 := (hbdry q.1 hq).mp q.2
        have hcond : Work.PTGeometric.tail 8 (ψ q.1).1 ∈ (chartE T.a T.i).target :=
          (ψ.map_source' hq).2
        have hval : (gInvFun (gToFun q)).1 =
            ψ.symm (hsTail (Work.PTGeometric.tail 8 (ψ q.1).1)) := by
          show (if hu : Work.PTGeometric.tail 8 (ψ q.1).1 ∈ (chartE T.a T.i).target then
              (⟨ψ.symm (hsTail (Work.PTGeometric.tail 8 (ψ q.1).1)),
                gInv (Work.PTGeometric.tail 8 (ψ q.1).1) hu⟩ : ↥((modelWithCornersEuclideanHalfSpace 9).boundary (levelModel {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0} hWcl L))) else x₀).1 = _
          rw [dif_pos hcond]
        refine Subtype.ext ?_
        rw [hval]
        show ψ.symm (hsTail (Work.PTGeometric.tail 8 (ψ q.1).1)) = q.1
        rw [eq_hsTail hqbd, ψ.left_inv hq]
      right_inv' := fun u hu => by
        have hval : (gInvFun u).1 = ψ.symm (hsTail u) := by
          show (if hu0 : u ∈ (chartE T.a T.i).target then
              (⟨ψ.symm (hsTail u), gInv u hu0⟩ : ↥((modelWithCornersEuclideanHalfSpace 9).boundary (levelModel {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0} hWcl L))) else x₀).1 = ψ.symm (hsTail u)
          rw [dif_pos hu]
        show Work.PTGeometric.tail 8 (ψ (gInvFun u).1).1 = u
        rw [hval, ψ.right_inv (gTgtMem u hu)]
        exact tail_hsTail u
      open_source := ψ.open_source.preimage continuous_subtype_val
      open_target := (chartE T.a T.i).open_target
      continuousOn_toFun :=
        (Work.PTGeometric.continuous_tail 8).comp_continuousOn
          (continuous_subtype_val.comp_continuousOn
            (ψ.continuousOn_toFun.comp continuous_subtype_val.continuousOn (fun q hq => hq)))
      continuousOn_invFun := by
        rw [continuousOn_iff_continuous_domRestrict]
        have hcont1 : Continuous fun u : ↥(chartE T.a T.i).target => hsTail u.1 :=
          Continuous.subtype_mk (f := fun u : ↥(chartE T.a T.i).target => euCons 0 u.1)
            (continuous_euCons.comp (continuous_const.prodMk continuous_subtype_val))
            (fun u => by simp [euCons_zero])
        have hmap2 : Continuous fun u : ↥(chartE T.a T.i).target =>
            (⟨hsTail u.1, gTgtMem u.1 u.2⟩ : ↥(tgtC T.εcl T.a T.i)) :=
          Continuous.subtype_mk hcont1 (fun u => gTgtMem u.1 u.2)
        have hpsi := (continuousOn_iff_continuous_domRestrict.mp
            (Work.ThomBordism.collarChart_continuous_inv T)).comp hmap2
        have hfin : Continuous fun u : ↥(chartE T.a T.i).target =>
            (⟨ψ.symm (hsTail u.1), gInv u.1 u.2⟩ : ↥((modelWithCornersEuclideanHalfSpace 9).boundary (levelModel {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0} hWcl L))) :=
          Continuous.subtype_mk hpsi (fun u => gInv u.1 u.2)
        refine hfin.congr (fun u => ?_)
        show (⟨ψ.symm (hsTail u.1), gInv u.1 u.2⟩ : ↥((modelWithCornersEuclideanHalfSpace 9).boundary (levelModel {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0} hWcl L))) =
          (if hu : u.1 ∈ (chartE T.a T.i).target then
            (⟨ψ.symm (hsTail u.1), gInv u.1 hu⟩ : ↥((modelWithCornersEuclideanHalfSpace 9).boundary (levelModel {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0} hWcl L))) else x₀)
        rw [dif_pos u.2] }
  have h1 : 0 < deltaC εcl := deltaC_pos hεcl
  have h2 : ψ.target = {z : EuclideanHalfSpace 9 | z.1 0 < deltaC εcl ∧
      Work.PTGeometric.tail 8 z.1 ∈
        (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.target} := rfl
  have h3 : ∀ z ∈ ψ.target, (ψ.symm z).1.1.1 = collarPiece G m hpow h a i z.1 :=
    fun z hz => collarW_eq_piece T hz
  have h5 : κ.source = ψ.source ∩ {q | 0 < (ψ q).1 0} := kappaCFix_source T
  have h6 : ∀ q ∈ κ.source, κ q = (ψ q).1 := fun q hq => kappaCFix_apply T hq
  have h7 : g.source = Subtype.val ⁻¹' ψ.source :=
    rfl
  have h8 : ∀ q ∈ g.source, g q = Work.PTGeometric.tail 8 (ψ q.1).1 := fun q hq => rfl
  have h9 : ∀ (q : ↥((modelWithCornersEuclideanHalfSpace 9).boundary (levelModel {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0} hWcl L)))
      (z : (Fam a.2).pt), z ∈ (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.source →
      q.1.1.1.1 = ((h.symm ⟨a, z⟩).1).1 →
      q ∈ g.source ∧
        g q = (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 z := by
    intro q z hz hqvec
    let q' : DataLW T := ⟨q.1.1, q.1.2⟩
    have hqq : (q' : (levelModel {x : (sourceRegionSetup G m hpow hphi hweak).Region | w x = 0} hWcl L)) = q.1 := rfl
    have hvec : (q'.1.1.1 : SrcVS k) = ((h.symm ⟨a, z⟩).1).1 := by
      show (q.1.1.1).1 = ((h.symm ⟨a, z⟩).1).1
      exact hqvec
    have hbd0 : q'.1.1.1 0 = 0 := by
      show (q'.1.1).1 0 = 0
      rw [hvec]
      exact (h.symm ⟨a, z⟩).2.2
    let hh : q'.1.1.1 0 < deltaC T.εcl := by
      rw [hbd0]; exact deltaC_pos T.hεcl
    have hx : projPt (q'.1.1) ∈ bdryDom G m hpow := projPt_mem_bdryDom T hh
    have hprov : T.h ⟨projPt (q'.1.1), hx⟩ = ⟨T.a, z⟩ := by
      have h1 : (⟨projPt (q'.1.1), hx⟩ : ↥(bdryDom G m hpow)) = T.h.symm ⟨T.a, z⟩ := by
        refine Subtype.ext ?_
        refine Subtype.ext ?_
        show ((projPt (q'.1.1)).1 : SrcVS k) =
          (((T.h.symm ⟨T.a, z⟩ : ↥(bdryDom G m hpow)) : SrcHS k)).1
        rw [projPt_coe, tailVec_eq_self_of_zero (k := k) hbd0]
        exact hvec
      exact (congrArg T.h h1).trans (T.h.apply_symm_apply _)
    have hsrc : q' ∈ srcC T := by
      refine ⟨hh, ?_⟩
      refine (mem_Ofam_iff (x := projPt (q'.1.1)) hx).mpr ?_
      rw [hprov]
      exact ⟨z, hz, rfl⟩
    have hsrcψ : q.1 ∈ ψ.source := by
      rw [← hqq]
      exact hsrc
    refine ⟨hsrcψ, ?_⟩
    show Work.PTGeometric.tail 8 (ψ q.1).1 =
      (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 z
    rw [← hqq]
    show Work.PTGeometric.tail 8 (toFunC T q').1 = (chartE T.a T.i) z
    rw [toFunC_apply T q' hsrc, tail_hsCons]
    congr 1
    have hx2 : projPt (q'.1.1) ∈ bdryDom G m hpow := projPt_mem_bdryDom T hsrc.1
    have h3 : T.h ⟨projPt (q'.1.1), hx2⟩ = ⟨T.a, z⟩ := by
      rw [show hx2 = hx from Subsingleton.elim _ _]
      exact hprov
    have h1 : Sigma.mk T.a (pieceOf T q' hsrc) = T.h ⟨projPt (q'.1.1), hx2⟩ :=
      fibreHomeo_mk (Fam := Fam) T.a _
    have h5 : (⟨⟨T.a, pieceOf T q' hsrc⟩, Set.mem_range_self (pieceOf T q' hsrc)⟩ :
        ↥(Set.range (Sigma.mk (β := fun c : Fin T.m × ι => (Fam c.2).pt) T.a))) =
        ⟨⟨T.a, z⟩, Set.mem_range_self z⟩ := Subtype.ext (h1.trans h3)
    have h6 := congrArg (fibreHomeo (Fam := Fam) T.a) h5
    rw [fibreHomeo_apply T.a (pieceOf T q' hsrc), fibreHomeo_apply T.a z] at h6
    exact h6
  exact ⟨deltaC εcl, ψ, κ, g, h1, h2, h3, hbdry, h5, h6, h7, h8, h9⟩

end Work.ThomBordism.LeadChapter
