import Mathlib
import Submission.Work.ThomBordism.sourceCoord
import Submission.Work.ThomBordism.exists_relFundClass_of_collar_loc
import Submission.Work.ThomBordism.levelBdryHomeoOf
import Submission.Work.ThomBordism.levelBdryPushClass
import Submission.Work.ThomBordism.collarDerivTransport
import Submission.Work.ThomBordism.sourceRegionChartId
import Submission.Work.ThomBordism.regionPhiNeg
import Submission.Work.ThomBordism.LeadChapter.Defs
import Submission.Work.ThomBordism.range_ogFrameCLM
import Submission.Work.ThomBordism.LeadChapter.chapter_K1det
import Submission.Work.ThomBordism.LeadChapter.chapter_bdryTransfer
import Submission.Work.ThomBordism.LeadChapter.chapter_tubeDet
import Submission.Work.ThomBordism.LeadChapter.chapter_collarChartFix
import Submission.Work.ThomBordism.LeadChapter.CollarChartDefs
import Submission.Work.ThomBordism.locClass_push_chartTr
import Submission.Work.ThomBordism.det_ellOf_ogFrameCLM_pos
import Submission.Work.ThomBordism.levelModelVal
import Submission.Work.ThomBordism.exists_lift_of_range_le
import Submission.Work.ThomBordism.sourceBoundaryCoord_assembly
import Submission.Work.ThomBordism.sourceRawAmbientData_tied
import Submission.Work.ThomBordism.sourceRawAmbientData_tube_ne
import Submission.Work.ThomBordism.chartVec_of_phi_neg
import Submission.Work.ThomBordism.orientOfCollar
import Submission.Work.PTGeometric.LevelModel
import Submission.Work.PTGeometric.SourceNull
import Submission.Work.PTGeometric.FlatSource
import Submission.Work.PTGeometric.sourceZeroSet_boundary_homeo_spec
import Submission.Work.ThomBordism.sourceZeroSet_boundary_homeo_spec_coord
import Submission.Work.Tubular.hasCollar_normalDiscSub
import Submission.Work.ThomBordism.collarOfStrip
import Submission.Work.PTGeometric.WeakRegion.Manifold
-- import Submission.Work.PTGeometric.CanonicalLevel (removed: import cycle)
import Submission.Work.PTGeometric.ContinuousToPreData
-- import Submission.Work.PTGeometric.SourceWiring (removed: it created an import cycle with the collar consumer)
import Submission.Work.PTGeometric.mem_sourceZeroSet_of_collarRay
import Submission.Work.PTGeometric.exists_epigraph_at_boundaryPoint
import Submission.Work.PTGeometric.smoothMap_into_tautTotal_eqOn_close
import Submission.Work.PTGeometric.nonempty_ambCharts_of_family_verbatim
import Submission.Work.PTGeometric.exists_cutoffs
import Submission.Work.PTGeometric.AmbientPerturbation
import Submission.Work.PTGeometric.exists_Rmap_lipschitz
import Submission.Work.ThomBordism.tangentBall_regionSetupCore
import Submission.Work.ThomBordism.coframingOrientBase
import Submission.Work.ThomBordism.coframingExplicitOfLift
import Submission.Work.ThomBordism.orientationFamily_valued_of_coframing
import Submission.Work.ThomBordism.exists_orientedLift_of_close
import Submission.Work.ThomBordism.exists_orientedLift_of_Rmap_eq
import Submission.Work.ThomBordism.Grassmann.exists_coframing_of_orientedLift
import Submission.Work.ThomBordism.sourceRegion_extChart_transition_det_pos
import Submission.Work.PTGeometric.range_mfderiv_eq_fixed_of_ambGood
import Submission.Work.PTGeometric.smoothMap_into_tautTotal_eqOn_close_pm

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.ThomBordism

open Work.PTGeometric

/-- The proof that `consVec s (tailVec u)` is a point of the half-space. -/
theorem halfConsProof (k : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (u : EuclideanSpace ℝ (Fin ((8 + k) + 1))) :
    0 ≤ (Work.PTGeometric.consVec s (Work.PTGeometric.tailVec u)).ofLp 0 := by
  rw [Work.PTGeometric.consVec_apply_zero, Work.PTGeometric.tailVec_apply_zero, add_zero]
  exact hs

/-- The half-space point with `0`-th coordinate `s ≥ 0` and the other coordinates of `u`. -/
def halfCons (k : ℕ) (s : ℝ) (hs : 0 ≤ s) (u : EuclideanSpace ℝ (Fin ((8 + k) + 1))) :
    EuclideanHalfSpace ((8 + k) + 1) :=
  ⟨Work.PTGeometric.consVec s (Work.PTGeometric.tailVec u), halfConsProof k s hs u⟩

theorem halfCons_coe {k : ℕ} (s : ℝ) (hs : 0 ≤ s)
    (u : EuclideanSpace ℝ (Fin ((8 + k) + 1))) :
    (halfCons k s hs u).1 = Work.PTGeometric.consVec s (Work.PTGeometric.tailVec u) := rfl

theorem halfCons_head {k : ℕ} (s : ℝ) (hs : 0 ≤ s)
    (u : EuclideanSpace ℝ (Fin ((8 + k) + 1))) : (halfCons k s hs u).1 0 = s := by
  rw [halfCons_coe, Work.PTGeometric.consVec_apply_zero, Work.PTGeometric.tailVec_apply_zero,
    add_zero]

theorem halfCons_tail {k : ℕ} (s : ℝ) (hs : 0 ≤ s)
    (u : EuclideanSpace ℝ (Fin ((8 + k) + 1))) :
    Work.PTGeometric.tailVec (halfCons k s hs u).1 = Work.PTGeometric.tailVec u := by
  rw [halfCons_coe]
  exact Work.PTGeometric.tailVec_consVec s (Work.PTGeometric.tailVec_apply_zero u)

theorem halfCons_zero_eq {k : ℕ} (u : EuclideanSpace ℝ (Fin ((8 + k) + 1))) (hu : u 0 = 0) :
    (halfCons k 0 (le_refl 0) u).1 = u := by
  rw [halfCons_coe, ← hu, Work.PTGeometric.consVec_tailVec]

/-- **The level set of an ambient function on the half-space, over a set `Z`.** -/
def lvlSet (k : ℕ) (Φ : EuclideanHalfSpace ((8 + k) + 1) → ℝ)
    (Z : Set (EuclideanHalfSpace ((8 + k) + 1))) :
    Set {x : EuclideanHalfSpace ((8 + k) + 1) // Φ x ≤ 0} := {x | x.1 ∈ Z}

/-- Continuity of a map into a subtype, read on the ambient space. -/
theorem continuous_subtype_iff {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y]
    {p : Y → Prop} (f : X → {y : Y // p y}) : Continuous f ↔ Continuous fun x => (f x : Y) :=
  IsInducing.subtypeVal.continuous_iff

/-- The domain of the collar map: the boundary of the level model times the half-open interval. -/
abbrev colX (k : ℕ) (ε : ℝ) (P : Type) [TopologicalSpace P]
    [ChartedSpace (EuclideanHalfSpace 9) P] : Type :=
  (modelWithCornersEuclideanHalfSpace 9).boundary P × {s : ℝ // 0 ≤ s ∧ s < ε}

/-- The open subset of the level set on which the collar is defined. -/
abbrev raySet (k : ℕ) (Φ : EuclideanHalfSpace ((8 + k) + 1) → ℝ)
    (Z : Set (EuclideanHalfSpace ((8 + k) + 1))) (ε : ℝ) :
    Set ↥(lvlSet k Φ Z) := {x | x.1.1.1 0 < ε}

/-- **The collar of a level set that is saturated along the collar rays.** -/
theorem nonempty_collar_of_collarRay {k : ℕ}
    (Φ : EuclideanHalfSpace ((8 + k) + 1) → ℝ)
    (Z : Set (EuclideanHalfSpace ((8 + k) + 1)))
    (W : Set {x : EuclideanHalfSpace ((8 + k) + 1) // Φ x ≤ 0})
    (hWeq : W = lvlSet k Φ Z) (hWcl : IsClosed W)
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1))
      {x : EuclideanHalfSpace ((8 + k) + 1) // Φ x ≤ 0}]
    [IsManifold (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      ((⊤ : ℕ∞) : WithTop ℕ∞) {x : EuclideanHalfSpace ((8 + k) + 1) // Φ x ≤ 0}]
    [CompactSpace {x : EuclideanHalfSpace ((8 + k) + 1) // Φ x ≤ 0}]
    [T2Space {x : EuclideanHalfSpace ((8 + k) + 1) // Φ x ≤ 0}]
    (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hZs : ∀ x ∈ Z, x.1 0 ≤ ε → ∀ (s : ℝ) (hs : 0 ≤ s), s ≤ ε →
      halfCons k s hs x.1 ∈ Z)
    (hray : ∀ x ∈ Z, x.1 0 = 0 → ∀ (s : ℝ) (hs : 0 ≤ s), s ≤ ε →
      Φ (halfCons k s hs x.1) ≤ 0)
    (hΦ0 : ∀ x ∈ Z, x.1 0 < ε → Φ (halfCons k 0 (le_refl 0) x.1) ≤ 0)
    (L : Work.PTGeometric.LocalLevelData k
      {x : EuclideanHalfSpace ((8 + k) + 1) // Φ x ≤ 0} W)
    (inst : ChartedSpace (EuclideanHalfSpace 9)
      (Work.PTGeometric.levelModel W hWcl L))
    (hbdry : (modelWithCornersEuclideanHalfSpace 9).boundary
        (Work.PTGeometric.levelModel W hWcl L) =
      {x : Work.PTGeometric.levelModel W hWcl L | x.1.1.1 0 = 0}) :
    @Nonempty (@Work.Surgery.Collar 8 (Work.PTGeometric.levelModel W hWcl L)
      _ inst) := by
  subst hWeq
  letI := inst
  -- ## the ambient points of a point of the level set
  let vecHS : ↥(lvlSet k Φ Z) → EuclideanHalfSpace ((8 + k) + 1) := fun y => y.1.1
  let vec : ↥(lvlSet k Φ Z) → EuclideanSpace ℝ (Fin ((8 + k) + 1)) := fun y => (vecHS y).1
  have hnn : ∀ y : ↥(lvlSet k Φ Z), 0 ≤ (vec y) 0 := fun y => (vecHS y).2
  have hmem : ∀ x : ↥(lvlSet k Φ Z),
      x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary
        (Work.PTGeometric.levelModel (lvlSet k Φ Z) hWcl L) ↔ (vec x) 0 = 0 := by
    intro x
    show x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary
        (Work.PTGeometric.levelModel (lvlSet k Φ Z) hWcl L) ↔ x.1.1.1 0 = 0
    rw [hbdry]
    exact Iff.rfl
  have hhead_cont : Continuous fun x : ↥(lvlSet k Φ Z) => (vec x) 0 := by
    show Continuous fun x : ↥(lvlSet k Φ Z) =>
      (x.1.1.1 : EuclideanSpace ℝ (Fin ((8 + k) + 1))) 0
    fun_prop
  have hbz : ∀ q : (modelWithCornersEuclideanHalfSpace 9).boundary
      (Work.PTGeometric.levelModel (lvlSet k Φ Z) hWcl L), (vec q.1) 0 = 0 :=
    fun q => (hmem q.1).mp q.2
  -- ## the collar map, in stages
  let cvec : colX k ε (Work.PTGeometric.levelModel (lvlSet k Φ Z) hWcl L) →
      EuclideanSpace ℝ (Fin ((8 + k) + 1)) :=
    fun p => Work.PTGeometric.consVec p.2.1 (Work.PTGeometric.tailVec (vec p.1.1))
  have cvec_def : ∀ p : colX k ε (Work.PTGeometric.levelModel (lvlSet k Φ Z) hWcl L),
      cvec p = Work.PTGeometric.consVec p.2.1 (Work.PTGeometric.tailVec (vec p.1.1)) :=
    fun p => rfl
  let cHS : colX k ε (Work.PTGeometric.levelModel (lvlSet k Φ Z) hWcl L) →
      EuclideanHalfSpace ((8 + k) + 1) :=
    fun p => ⟨cvec p, halfConsProof k p.2.1 p.2.2.1 (vec p.1.1)⟩
  have cHS_def : ∀ p : colX k ε (Work.PTGeometric.levelModel (lvlSet k Φ Z) hWcl L),
      cHS p = halfCons k p.2.1 p.2.2.1 (vec p.1.1) := fun p => Subtype.ext rfl
  let cM : colX k ε (Work.PTGeometric.levelModel (lvlSet k Φ Z) hWcl L) →
      {x : EuclideanHalfSpace ((8 + k) + 1) // Φ x ≤ 0} := fun p =>
    ⟨cHS p, hray (vecHS p.1.1) p.1.1.2 (hbz p.1) p.2.1 p.2.2.1 (le_of_lt p.2.2.2)⟩
  let cP : colX k ε (Work.PTGeometric.levelModel (lvlSet k Φ Z) hWcl L) →
      ↥(lvlSet k Φ Z) := fun p =>
    ⟨cM p, hZs (vecHS p.1.1) p.1.1.2 (by rw [hbz p.1]; exact le_of_lt hε) p.2.1 p.2.2.1
      (le_of_lt p.2.2.2)⟩
  let cU : colX k ε (Work.PTGeometric.levelModel (lvlSet k Φ Z) hWcl L) →
      raySet k Φ Z ε := fun p => ⟨cP p, by
    show (cHS p).1 0 < ε
    rw [cHS_def p, halfCons_head]
    exact p.2.2.2⟩
  have cU_vec : ∀ p : colX k ε (Work.PTGeometric.levelModel (lvlSet k Φ Z) hWcl L),
      vec (cU p).1 = cvec p := fun p => rfl
  -- ## the inverse, in stages
  let gvec : raySet k Φ Z ε → EuclideanSpace ℝ (Fin ((8 + k) + 1)) :=
    fun x => Work.PTGeometric.consVec 0 (Work.PTGeometric.tailVec (vec x.1))
  have gvec_def : ∀ x : raySet k Φ Z ε,
      gvec x = Work.PTGeometric.consVec 0 (Work.PTGeometric.tailVec (vec x.1)) := fun x => rfl
  let gHS : raySet k Φ Z ε → EuclideanHalfSpace ((8 + k) + 1) :=
    fun x => ⟨gvec x, halfConsProof k 0 (le_refl 0) (vec x.1)⟩
  have gHS_def : ∀ x : raySet k Φ Z ε, gHS x = halfCons k 0 (le_refl 0) (vec x.1) :=
    fun x => Subtype.ext rfl
  let gM : raySet k Φ Z ε → {x : EuclideanHalfSpace ((8 + k) + 1) // Φ x ≤ 0} :=
    fun x => ⟨gHS x, hΦ0 (vecHS x.1) x.1.2 x.2⟩
  let gP : raySet k Φ Z ε → ↥(lvlSet k Φ Z) := fun x =>
    ⟨gM x, hZs (vecHS x.1) x.1.2 (le_of_lt x.2) 0 (le_refl 0) (le_of_lt hε)
      ⟩
  let gb : raySet k Φ Z ε → (modelWithCornersEuclideanHalfSpace 9).boundary
      (Work.PTGeometric.levelModel (lvlSet k Φ Z) hWcl L) := fun x =>
    ⟨gP x, (hmem (gP x)).mpr (by
      show (gvec x) 0 = 0
      rw [gvec_def x, Work.PTGeometric.consVec_apply_zero, Work.PTGeometric.tailVec_apply_zero,
        add_zero])⟩
  let g : raySet k Φ Z ε → (modelWithCornersEuclideanHalfSpace 9).boundary
        (Work.PTGeometric.levelModel (lvlSet k Φ Z) hWcl L) × {s : ℝ // 0 ≤ s ∧ s < ε} :=
    fun x => (gb x, ⟨(vec x.1) 0, ⟨(vecHS x.1).2, x.2⟩⟩)
  have gb_vec : ∀ x : raySet k Φ Z ε, vec (gb x).1 = gvec x := fun x => rfl
  have g_head : ∀ x : raySet k Φ Z ε, (g x).2.1 = (vec x.1) 0 := fun x => rfl
  -- ## the two inverse identities
  have hgc : g ∘ cU = id := by
    funext p
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      show gvec (cU p) = vec p.1.1
      rw [gvec_def, cU_vec, cvec_def p]
      rw [Work.PTGeometric.tailVec_consVec p.2.1 (Work.PTGeometric.tailVec_apply_zero _)]
      exact halfCons_zero_eq _ (hbz p.1)
    · apply Subtype.ext
      show (vec (cU p).1) 0 = p.2.1
      rw [cU_vec, cvec_def p, Work.PTGeometric.consVec_apply_zero,
        Work.PTGeometric.tailVec_apply_zero, add_zero]
  have hcg : cU ∘ g = id := by
    funext x
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    show cvec (g x) = vec x.1
    rw [cvec_def, g_head x]
    show Work.PTGeometric.consVec ((vec x.1) 0) (Work.PTGeometric.tailVec (vec (gb x).1)) = vec x.1
    rw [gb_vec, gvec_def]
    rw [Work.PTGeometric.tailVec_consVec 0 (Work.PTGeometric.tailVec_apply_zero _)]
    rw [Work.PTGeometric.consVec_tailVec]
  -- ## continuity
  have hcU_cont : Continuous cU := by
    have h1 : Continuous cvec := by
      rw [show cvec = fun p : colX k ε (Work.PTGeometric.levelModel (lvlSet k Φ Z) hWcl L) =>
          p.1.1.1.1.1 - (p.1.1.1.1.1 0) •
            (Work.PTGeometric.eZero : EuclideanSpace ℝ (Fin ((8 + k) + 1)))
          + p.2.1 • (Work.PTGeometric.eZero : EuclideanSpace ℝ (Fin ((8 + k) + 1))) from rfl]
      fun_prop
    have h2 : Continuous cHS := h1.subtype_mk (fun p => halfConsProof k p.2.1 p.2.2.1 (vec p.1.1))
    have h3 : Continuous cM := h2.subtype_mk (fun p =>
      hray (vecHS p.1.1) p.1.1.2 (hbz p.1) p.2.1 p.2.2.1 (le_of_lt p.2.2.2))
    have h4 : Continuous cP := h3.subtype_mk (fun p =>
      hZs (vecHS p.1.1) p.1.1.2 (by rw [hbz p.1]; exact le_of_lt hε) p.2.1 p.2.2.1
        (le_of_lt p.2.2.2))
    exact h4.subtype_mk (fun p => by
      show (cHS p).1 0 < ε
      rw [cHS_def p, halfCons_head]
      exact p.2.2.2)
  have hg_cont : Continuous g := by
    have h1 : Continuous gvec := by
      rw [show gvec = fun x : raySet k Φ Z ε =>
          x.1.1.1.1 - (x.1.1.1.1 0) • (Work.PTGeometric.eZero : EuclideanSpace ℝ (Fin ((8 + k) + 1)))
          + (0 : ℝ) • (Work.PTGeometric.eZero : EuclideanSpace ℝ (Fin ((8 + k) + 1))) from rfl]
      fun_prop
    have h2 : Continuous gHS := h1.subtype_mk (fun x => halfConsProof k 0 (le_refl 0) (vec x.1))
    have h3 : Continuous gM := h2.subtype_mk (fun x => hΦ0 (vecHS x.1) x.1.2 x.2)
    have h4 : Continuous gP := h3.subtype_mk (fun x => hZs (vecHS x.1) x.1.2
      (le_of_lt x.2) 0 (le_refl 0) (le_of_lt hε))
    have h5 : Continuous gb := h4.subtype_mk (fun x => (hmem (gP x)).mpr (by
      show (gvec x) 0 = 0
      rw [gvec_def x, Work.PTGeometric.consVec_apply_zero, Work.PTGeometric.tailVec_apply_zero,
        add_zero]))
    refine h5.prodMk ?_
    refine (continuous_subtype_iff (f := fun x : raySet k Φ Z ε =>
      (⟨(vec x.1) 0, ⟨(vecHS x.1).2, x.2⟩⟩ : {s : ℝ // 0 ≤ s ∧ s < ε}))).mpr ?_
    show Continuous fun x : raySet k Φ Z ε => (vec x.1) 0
    exact hhead_cont.comp continuous_subtype_val
  -- ## the embedding
  have hemb : IsEmbedding cU :=
    IsEmbedding.of_comp hcU_cont hg_cont (by
      rw [hgc]
      exact IsEmbedding.id)
  -- ## the map to the ambient space
  have hembP : IsEmbedding (fun p : colX k ε (Work.PTGeometric.levelModel (lvlSet k Φ Z) hWcl L) =>
      (cU p : ↥(lvlSet k Φ Z))) := IsEmbedding.subtypeVal.comp hemb
  have hrange : Set.range (fun p : colX k ε (Work.PTGeometric.levelModel (lvlSet k Φ Z) hWcl L) =>
      (cU p : ↥(lvlSet k Φ Z))) = raySet k Φ Z ε := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact (cU p).2
    · intro hx
      refine ⟨g ⟨x, hx⟩, ?_⟩
      have h : cU (g ⟨x, hx⟩) = ⟨x, hx⟩ := congrFun hcg ⟨x, hx⟩
      exact congrArg (fun y : ↥(raySet k Φ Z ε) => (y : ↥(lvlSet k Φ Z))) h
  have hopen : IsOpen (Set.range (fun p : colX k ε
      (Work.PTGeometric.levelModel (lvlSet k Φ Z) hWcl L) =>
      (cU p : ↥(lvlSet k Φ Z)))) := by
    rw [hrange]
    exact isOpen_lt hhead_cont continuous_const
  have hOE : IsOpenEmbedding (fun p : colX k ε
      (Work.PTGeometric.levelModel (lvlSet k Φ Z) hWcl L) => (cU p : ↥(lvlSet k Φ Z))) :=
    IsOpenEmbedding.mk hembP hopen
  -- ## the reparametrisation of the collar parameter
  let Ehom : (modelWithCornersEuclideanHalfSpace 9).boundary
        (Work.PTGeometric.levelModel (lvlSet k Φ Z) hWcl L) × Work.Surgery.HalfLine ≃ₜ
      colX k ε (Work.PTGeometric.levelModel (lvlSet k Φ Z) hWcl L) :=
    Homeomorph.prodCongr (Homeomorph.refl _) (Work.ThomBordism.stripHomeomorph ε hε)
  have he : IsOpenEmbedding (⇑Ehom) :=
    IsOpenEmbedding.mk Ehom.isEmbedding (by
      rw [Set.range_eq_univ.mpr Ehom.surjective]
      exact isOpen_univ)
  refine ⟨{ toFun := (fun p : colX k ε (Work.PTGeometric.levelModel (lvlSet k Φ Z) hWcl L) =>
                (cU p : ↥(lvlSet k Φ Z))) ∘ ⇑Ehom,
             isOpenEmbedding := hOE.comp he,
             toFun_zero := ?_ }⟩
  intro x
  show ((fun p : colX k ε (Work.PTGeometric.levelModel (lvlSet k Φ Z) hWcl L) =>
      (cU p : ↥(lvlSet k Φ Z))) ∘ ⇑Ehom) (x, ⟨0, le_refl 0⟩) = x.1
  show ((cU (Ehom (x, ⟨0, le_refl 0⟩)) : ↥(raySet k Φ Z ε)) : ↥(lvlSet k Φ Z)) = x.1
  show ((cU (x, (Work.ThomBordism.stripHomeomorph ε hε) ⟨0, le_refl 0⟩) : ↥(raySet k Φ Z ε)) :
      ↥(lvlSet k Φ Z)) = x.1
  rw [Work.ThomBordism.stripHomeomorph_zero]
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  show vec (cU (x, ⟨0, ⟨le_refl 0, hε⟩⟩)) = vec x.1
  rw [cU_vec, cvec_def]
  show Work.PTGeometric.consVec (0 : ℝ) (Work.PTGeometric.tailVec (vec x.1)) = vec x.1
  exact halfCons_zero_eq _ (hbz x)


/-- **The source construction, with the pin, the boundary coordination, and (new) the collar and the
orientation family of its level set.**

The three conjuncts of the produced datum are

* the **tied pin** (`ellE j` is the frame reading of `tiedND G i`);
* `Work.ThomBordism.SourceBoundaryCoord D0` — **the boundary coordination, the project's last
  geometric gap** (its proof is the single `sorry` of this file: the pieces bound the level set with
  the given orientations; equivalently, `hPairδ` of the relative fundamental class of the level set is
  the sum of the pieces' classes pushed along `hend`.  See `NOTE_SESSION32.md` §2–§3 for the sharpest
  form — the *uniformity of the boundary sign across the pieces* — and the routes already ruled out);
* `∃ hWcl L, Work.ThomBordism.SourceOrientHyp D0 hWcl L` — the collar of the canonical level model and
  a half-orientation family of it in the `Lvl` chart structure.  This is proved *by the
  construction*: the smoothed matrix part `Pm` (via
  `Work.PTGeometric.smoothMap_into_tautTotal_eqOn_close_pm`), the oriented lift
  `Work.ThomBordism.exists_orientedLift_of_close`, the positively oriented coframing
  `Work.ThomBordism.Grassmann.exists_coframing_of_orientedLift`, the positive atlas
  `Work.ThomBordism.sourceRegion_extChart_transition_det_pos`, the link
  `Work.PTGeometric.range_mfderiv_eq_fixed_of_ambGood` and
  `Work.ThomBordism.orientationFamily_of_coframingDataBase` (all in step 11bis below). -/
-- **The bundle of the source construction** (see `NOTE_SESSION48.md` §9/§9b): the raw ambient datum
-- produced by the construction together with the conjuncts it comes with, so that the datum can be a
-- *named* `def` and the boundary coordination a *standalone* statement.
structure SourceRawBundle {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ) where
  /-- the raw ambient datum of the source construction -/
  datum : Work.PTGeometric.RawAmbientData (k + G.mU) k (Fin m × ι) (fun a => Fam a.2)
  /-- **the tied pin**: every prescribed chart is the frame reading of `tiedND G i` -/
  tied : ∀ j : Fin datum.mE, ∃ (i : ι) (w0 : (Fam i).pt)
      (j' : Work.ThomBordism.PontryaginThom.CoverIdx (Fam i) k)
      (hb : w0 ∈ (Work.ThomBordism.tiedND G i).D.baseSet j'),
      datum.ellE j =
        (Work.Tubular.readCLM (G.emb i) (Work.ThomBordism.tiedND G i) j' w0).comp
          (Work.PTGeometric.projEuc k G.mU G.hmU)
  /-- the level set is closed -/
  hWcl : IsClosed {x : datum.M | datum.v x = 0}
  /-- local level data of the level set -/
  L : Work.PTGeometric.LocalLevelData k datum.M {x : datum.M | datum.v x = 0}
  /-- the collar of the canonical level model and a half-orientation family of it -/
  orient : Work.ThomBordism.SourceOrientHyp datum hWcl L
  /-- the boundary coordination (route (1): discharged in place, per branch) -/
  coord : Work.ThomBordism.SourceBoundaryCoord datum

noncomputable def sourceRawBundle
  {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
  {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]
  (hk : 11 ≤ k) (hne : ∀ i, Nonempty (Fam i).pt)
  (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam)
  (m : ℕ) (hm : 0 < m)
  (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
  (hwk : Work.PTGeometric.RegionManifoldTheoremOfIsCompactWeak k)
  (hphi : Work.PTGeometric.SourceRegionPhiInteriorSign k
    (Work.PTGeometric.sourceZeroSet G m hpow)
    {x : EuclideanHalfSpace ((8 + k) + 1) |
      Work.PTGeometric.flatSourceHomotopy8 (k := k)
        (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
        (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ x.1 = D.t₀}) :
  SourceRawBundle G m := by
  classical
  suffices h : Nonempty (SourceRawBundle G m) by exact Classical.choice h
  haveI := t2Space_halfSpace ((8 + k) + 1)
  -- ### Step 1: the clauses of the defining function
  obtain ⟨hΦ, hZsub, hdisj, hK, hzero, hsub, hone, hsign⟩ := sourcePhi_spec G m hpow hphi
  -- ### Step 2: the weak regularity clause
  have hweak : ∀ x : EuclideanHalfSpace ((8 + k) + 1),
      sourcePhi G m hpow hphi x = 0 →
      mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
        (modelWithCornersSelf ℝ ℝ) (sourcePhi G m hpow hphi) x ≠ 0 :=
    mfderiv_ne_zero_of_phi_zero hΦ hsub hone
  -- ### Step 3: the region structure of the source
  let S := sourceRegionSetup (D := D) (Fam := Fam) G m hpow hphi hweak
  let M := S.Region
  letI : ChartedSpace (EuclideanHalfSpace (8 + k + 1)) M := S.chartedSpaceOfRegion
  letI : IsManifold (𝓡∂ (8 + k + 1)) ∞ M := S.isManifoldOfRegion
  letI : CompactSpace M := S.compactSpaceOfRegion
  letI : T2Space M := S.t2SpaceOfRegion
  -- ### Step 3bis: the degenerate case of an empty index type
  rcases isEmpty_or_nonempty ι with hιempty | hιne
  · -- the family is empty: build the data from a constant field on a ball model
    haveI := hιempty
    have hk0 : 0 < k := by omega
    obtain ⟨hΦc, hweakc, hbdc, hKc⟩ := Work.ThomBordism.tangentBall_regionSetupCore k
    let S₀ : Work.PTGeometric.WeakRegion.RegionSetupWeak k :=
      { A := EuclideanHalfSpace ((8 + k) + 1)
        Φ := fun x => ‖x.1‖ ^ 2 - 6 * (x.1 0) + 8
        hΦ := hΦc
        hweak := hweakc
        hsign := by
          intro x hx hx0
          exact absurd hx0 (hbdc x hx)
        hone := by
          intro x hx hx0
          exact absurd hx0 (hbdc x hx)
        hK := hKc }
    letI : ChartedSpace (EuclideanHalfSpace (8 + k + 1)) S₀.Region := S₀.chartedSpaceOfRegion
    letI : IsManifold (𝓡∂ (8 + k + 1)) ∞ S₀.Region := S₀.isManifoldOfRegion
    letI : CompactSpace S₀.Region := S₀.compactSpaceOfRegion
    letI : T2Space S₀.Region := S₀.t2SpaceOfRegion
    have hpt0 : (0 : ℝ) ≤
        ((3 : ℝ) • (Work.PTGeometric.eZero : EuclideanSpace ℝ (Fin ((8 + k) + 1)))).ofLp 0 := by
      rw [PiLp.smul_apply, Work.PTGeometric.eZero_apply]; norm_num
    have hpt : S₀.Φ ⟨(3 : ℝ) • (Work.PTGeometric.eZero : EuclideanSpace ℝ (Fin ((8 + k) + 1))),
        hpt0⟩ ≤ 0 := by
      show ‖((3 : ℝ) • (Work.PTGeometric.eZero : EuclideanSpace ℝ (Fin ((8 + k) + 1))))‖ ^ 2
        - 6 * (((3 : ℝ) • (Work.PTGeometric.eZero : EuclideanSpace ℝ (Fin ((8 + k) + 1)))).ofLp 0)
        + 8 ≤ 0
      rw [norm_smul, PiLp.smul_apply, Work.PTGeometric.eZero_apply]
      have h1 : ‖(Work.PTGeometric.eZero : EuclideanSpace ℝ (Fin ((8 + k) + 1)))‖ = 1 := by
        rw [Work.PTGeometric.eZero, PiLp.norm_single]; simp
      rw [h1]; norm_num
    haveI hMne₀ : Nonempty S₀.Region := ⟨⟨_, hpt⟩⟩
    let c₀ : EuclideanSpace ℝ (Fin (k + G.mU)) :=
      Work.PTGeometric.padEuc k G.mU G.hmU (Work.PTGeometric.stdVec k hk0)
    have hc₀ : c₀ ≠ 0 := fun h =>
      Work.PTGeometric.stdVec_ne_zero k hk0
        (Work.PTGeometric.padEuc_injective k G.mU G.hmU (by simpa using h))
    have hLeft₀ : IsEmpty ↥((∅ : Set S₀.Region) ∩ {x : S₀.Region |
        (fun _ : S₀.Region => c₀) x = 0}) :=
      ⟨fun x => Set.notMem_empty x.1 x.2.1⟩
    have hRight₀ : IsEmpty (Σ a : Fin m × ι, (Fam a.2).pt) :=
      ⟨fun y => isEmptyElim y.1.2⟩
    let D0 : Work.PTGeometric.RawAmbientData (k + G.mU) k (Fin m × ι) (fun a => Fam a.2) := {
      M := S₀.Region
      P := fun _ => Work.PTGeometric.padEndEuc k G.mU G.hmU (Work.PTGeometric.stdProj k)
      v := fun _ => c₀
      hPc := continuous_const
      hvc := continuous_const
      hProj := fun _ => Work.PTGeometric.padEndEuc_mem_Gr G.hmU (Work.PTGeometric.stdProj_mem_Gr k)
      hMem := fun _ => by
        rw [Work.PTGeometric.padEndEuc_apply_padEuc, Work.PTGeometric.stdProj_apply_stdVec k hk0]
      V := Set.univ
      hVopen := isOpen_univ
      S0 := ∅
      hS0cl := isClosed_empty
      hS0V := Set.empty_subset _
      hPsmV := contMDiff_const.contMDiffOn
      hvsmV := contMDiff_const.contMDiffOn
      S := ∅
      hScl := isClosed_empty
      hSsub := Set.empty_subset _
      hSS0 := Set.empty_subset _
      hend := Work.PTGeometric.homeoOfIsEmpty hLeft₀ hRight₀
      hzero_sub := by
        intro x _ hx0
        exact (hc₀ hx0).elim
      δ := 1
      hδpos := one_pos
      hδ := by
        intro x _ _
        show (1 : ℝ) ≤ ‖c₀‖
        rw [show c₀ = Work.PTGeometric.padEuc k G.mU G.hmU (Work.PTGeometric.stdVec k hk0)
            from rfl,
          Work.PTGeometric.norm_padEuc, Work.PTGeometric.norm_stdVec k hk0]
      mE := 0
      ellE := fun j => isEmptyElim j
      UE := fun j => isEmptyElim j
      isOpen_UE := fun j => isEmptyElim j
      UE_int := fun j => isEmptyElim j
      ellE_inj := fun j => isEmptyElim j
      ellE_inj_cl := fun j => isEmptyElim j
      bndZero_cov := by
        intro x _ hx0
        exact (hc₀ hx0).elim
      bndZero_trans := fun j => isEmptyElim j }
    have hWempty : {x : D0.M | D0.v x = 0} = ∅ := by
      ext x
      exact ⟨fun h => hc₀ h, fun h => h.elim⟩
    have hWcl : IsClosed {x : D0.M | D0.v x = 0} := by
      rw [hWempty]; exact isClosed_empty
    haveI : IsEmpty ↥{x : D0.M | D0.v x = 0} := ⟨fun x => hc₀ x.2⟩
    let L : Work.PTGeometric.LocalLevelData k D0.M {x : D0.M | D0.v x = 0} :=
      { U := fun x => isEmptyElim x
        isOpen_U := fun x => isEmptyElim x
        mem_U := fun x => isEmptyElim x
        g := fun x => isEmptyElim x
        contMDiff_g := fun x => isEmptyElim x
        zero_iff := fun x => isEmptyElim x
        isSubmersion_g := fun x => isEmptyElim x
        bndSubmersion := fun x => isEmptyElim x }
    refine ⟨?_⟩
    refine { datum := D0
             tied := fun j => isEmptyElim j
             hWcl := hWcl
             L := L
             orient := ?_
             coord := ?_ }
    · haveI hLe : IsEmpty ↥{x : D0.M | D0.v x = 0} :=
        ⟨fun x => hc₀ (show c₀ = 0 from x.2)⟩
      letI hCh : ChartedSpace (EuclideanHalfSpace 9)
          (Work.PTGeometric.levelModel {x : D0.M | D0.v x = 0} hWcl L) :=
        Work.PTGeometric.Lvl.Setup.instChartedSpace
          (Work.PTGeometric.levelSetup {x : D0.M | D0.v x = 0} hWcl L)
      haveI hLe' : IsEmpty
          (Work.PTGeometric.levelSetup (sourceLevelSet D0) hWcl L).Pre :=
        ⟨fun x => hLe.false x⟩
      refine ⟨@Work.Surgery.hasCollar_of_boundary_eq_empty 8
        (Work.PTGeometric.levelModel {x : D0.M | D0.v x = 0} hWcl L) _ _ (by
          ext x
          constructor
          · intro hx
            exact (hLe.false x).elim
          · intro hx
            exact absurd hx (Set.notMem_empty x)), ?_⟩
      exact ⟨fun x _ => (hLe'.false x).elim,
        ⟨fun x _ => (hLe'.false x).elim,
          fun K _ _ => ⟨0, fun x _ _ => (hLe'.false x).elim⟩⟩⟩
    · -- the family is empty, so the sum of the pieces is `0`
      rw [Work.ThomBordism.SourceBoundaryCoord, Work.ThomBordism.sourceBoundaryClass,
        Finset.sum_eq_zero (by intro a _; exact (hιempty.false a.2).elim), map_zero]
  -- ### Step 3ter: the region is nonempty (the pieces are)
  haveI hMne : Nonempty M := by
    obtain ⟨i⟩ := hιne
    have hSig : Nonempty (Σ a : Fin m × ι, (Fam a.2).pt) :=
      ⟨⟨⟨0, hm⟩, i⟩, Classical.choice (hne i)⟩
    obtain ⟨hp⟩ := hSig.map (Classical.choice (sourceZeroSet_boundary_homeo G m hpow)).symm
    exact ⟨⟨hp.1, hZsub hp.2.1⟩⟩
  -- ### Step 4: the ambient field
  let Hf : EuclideanSpace ℝ (Fin ((8 + k) + 1)) → D.T :=
    Work.PTGeometric.flatSourceHomotopy8 (k := k)
      (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
      (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ
  have hne' : ∀ x : M, Hf x.1.1 ≠ D.t₀ := by
    intro x hx
    have h : x.1 ∈ ({x : EuclideanHalfSpace ((8 + k) + 1) |
        sourcePhi G m hpow hphi x ≤ 0} ∩
        sourceBasepoint (D := D) (Fam := Fam) G m hpow) := ⟨x.2, hx⟩
    rw [hdisj] at h
    exact h
  let P : M → Work.PTGeometric.EndOp (k + G.mU) := fun x =>
    (G.coord ⟨Hf x.1.1, hne' x⟩).1
  let v : M → Work.PTGeometric.Amb (k + G.mU) := fun x =>
    (G.coord ⟨Hf x.1.1, hne' x⟩).2
  have hbase : Continuous fun x : M => Hf x.1.1 :=
    (Work.PTGeometric.continuous_flatSourceHomotopy8 k
      (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
      (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  have hcont : Continuous fun x : M => (⟨Hf x.1.1, hne' x⟩ : {y : D.T // y ≠ D.t₀}) :=
    hbase.subtype_mk (fun x => hne' x)
  have hPc : Continuous P := (G.continuous_coord.comp hcont).fst
  have hvc : Continuous v := (G.continuous_coord.comp hcont).snd
  -- ### Step 5: the collar, the sub-collar, the collapse end
  let V : Set M := {x | x.1.1 0 < 1 / 2}
  let S0 : Set M := {x | x.1.1 0 ≤ 1 / 4}
  let Send : Set M := {x | x.1.1 0 = 0}
  have hcoord0 : Continuous fun x : M => x.1.1 0 :=
    ((continuous_apply (0 : Fin ((8 + k) + 1))).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin ((8 + k) + 1) => ℝ)).continuous).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  have hVopen : IsOpen V := isOpen_lt hcoord0 continuous_const
  have hS0cl : IsClosed S0 := isClosed_le hcoord0 continuous_const
  have hS0V : S0 ⊆ V := by intro x hx; dsimp [V, S0] at *; linarith
  have hScl : IsClosed Send := isClosed_eq hcoord0 continuous_const
  have hS0_cont : Continuous fun x : M => x.1.1 :=
    continuous_subtype_val.comp continuous_subtype_val
  -- the boundary of the half-space model, in coordinates
  have hbnd : ∀ y : EuclideanHalfSpace ((8 + k) + 1),
      y ∈ (𝓡∂ (8 + k + 1)).boundary (EuclideanHalfSpace ((8 + k) + 1)) ↔ y.1 0 = 0 :=
    fun y => mem_boundary_halfSpace_iff ((8 + k) + 1)
  have hSsub : Send ⊆ (𝓡∂ (8 + k + 1)).boundary M := by
    intro x hx
    rw [S.mem_boundary_iff]
    exact Or.inl ((hbnd x.1).mpr hx)
  have hSS0 : Send ⊆ S0 := by
    intro x hx; dsimp [Send, S0] at *; linarith
  -- ### Step 5bis: every boundary zero of `v` lies on the collapse end
  have hzero_sub : ∀ x ∈ (𝓡∂ (8 + k + 1)).boundary M, v x = 0 → x ∈ Send := by
    intro x hx hx0
    have hxZ : Hf x.1.1 ∈ G.core := (G.core_iff_vec ⟨Hf x.1.1, hne' x⟩).mpr hx0
    rw [S.mem_boundary_iff] at hx
    rcases hx with hA | hΦ
    · exact (hbnd x.1).mp hA
    · exact hzero ⟨hxZ, hΦ⟩
  -- ### Step 5ter: the smoothness of the ambient field on the collar
  have hsmval : ContMDiff (𝓡∂ (8 + k + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin ((8 + k) + 1)))) ∞
      (fun x : M => x.1.1) := by
    have h1 : ContMDiff (𝓡∂ (8 + k + 1)) (𝓡∂ (8 + k + 1)) ∞
        (fun m : S.Region => m.1) := S.contMDiff_val
    have h2 : ContMDiff (𝓡∂ (8 + k + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin ((8 + k) + 1)))) ∞
        ((𝓡∂ (8 + k + 1)) : EuclideanHalfSpace (8 + k + 1) →
          EuclideanSpace ℝ (Fin (8 + k + 1))) := ModelWithCorners.contMDiff (𝓡∂ (8 + k + 1))
    exact h2.comp h1
  have hcoord_sm := contMDiffOn_coord_flatSource_collar (D := D) (Fam := Fam) (M := M) G m hpow
    (e := fun x : M => x.1.1) hsmval (fun x => hne' x)
  have hPsmV : ContMDiffOn (𝓡∂ (8 + k + 1)) (𝓘(ℝ, Work.PTGeometric.EndOp (k + G.mU))) ∞ P V :=
    ((ContinuousLinearMap.fst ℝ (Work.PTGeometric.EndOp (k + G.mU))
        (Work.PTGeometric.Amb (k + G.mU))).contMDiff.comp_contMDiffOn hcoord_sm)
  have hvsmV : ContMDiffOn (𝓡∂ (8 + k + 1)) (𝓘(ℝ, Work.PTGeometric.Amb (k + G.mU))) ∞ v V :=
    ((ContinuousLinearMap.snd ℝ (Work.PTGeometric.EndOp (k + G.mU))
        (Work.PTGeometric.Amb (k + G.mU))).contMDiff.comp_contMDiffOn hcoord_sm)
  -- ### Step 5quater: the uniform lower bound
  have hbnd_closed : IsClosed {x : M | x ∈ (𝓡∂ (8 + k + 1)).boundary M} := by
    have hΦc : Continuous fun x : M => sourcePhi G m hpow hphi x.1 :=
      hΦ.continuous.comp continuous_subtype_val
    have hset : {x : M | x ∈ (𝓡∂ (8 + k + 1)).boundary M} =
        {x : M | x.1.1 0 = 0} ∪ {x : M | sourcePhi G m hpow hphi x.1 = 0} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_union]
      rw [S.mem_boundary_iff]
      constructor
      · rintro (h | h)
        · exact Or.inl ((hbnd x.1).mp h)
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl ((hbnd x.1).mpr h)
        · exact Or.inr h
    rw [hset]
    exact (isClosed_eq hcoord0 continuous_const).union (isClosed_eq hΦc continuous_const)
  have hKδ : IsCompact {x : M | x ∈ (𝓡∂ (8 + k + 1)).boundary M ∧ (1 : ℝ) / 4 ≤ x.1.1 0} :=
    (hbnd_closed.inter (isClosed_le continuous_const hcoord0)).isCompact
  have hv_ne : ∀ x ∈ {x : M | x ∈ (𝓡∂ (8 + k + 1)).boundary M ∧ (1 : ℝ) / 4 ≤ x.1.1 0},
      v x ≠ 0 := by
    intro x hx hvx
    have hS : x ∈ Send := hzero_sub x hx.1 hvx
    dsimp [Send] at hS
    linarith [hx.2, hS]
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ : ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ {x : M | x ∈ (𝓡∂ (8 + k + 1)).boundary M ∧ (1 : ℝ) / 4 ≤ x.1.1 0},
        δ ≤ ‖v x‖ := by
    by_cases hneK : ({x : M | x ∈ (𝓡∂ (8 + k + 1)).boundary M
        ∧ (1 : ℝ) / 4 ≤ x.1.1 0} : Set M).Nonempty
    · obtain ⟨x₀, hx₀, hmin⟩ := hKδ.exists_isMinOn hneK hvc.continuousOn.norm
      exact ⟨‖v x₀‖, norm_pos_iff.mpr (hv_ne x₀ hx₀), fun x hx => hmin hx⟩
    · exact ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hneK⟩
  -- ### Step 6: the *pinned* pointwise local datum at every boundary zero
  have hpoint : ∀ x ∈ ((𝓡∂ (8 + k + 1)).boundary M ∩ {x : M | v x = 0}),
      ∃ (a : { ℓ : Work.PTGeometric.Amb (k + G.mU) →L[ℝ] Work.PTGeometric.Amb k //
          ∃ (i : ι) (w0 : (Fam i).pt)
            (j : Work.ThomBordism.PontryaginThom.CoverIdx (Fam i) k)
            (hb : w0 ∈ (Work.ThomBordism.tiedND G i).D.baseSet j),
            ℓ = (Work.Tubular.readCLM (G.emb i) (Work.ThomBordism.tiedND G i) j w0).comp
              (Work.PTGeometric.projEuc k G.mU G.hmU) })
        (U : Set M),
        IsOpen U ∧ x ∈ U ∧ closure U ⊆ interior S0 ∧
        (∀ y ∈ closure U, ∀ z : Work.PTGeometric.Amb (k + G.mU), P y z = z → a.1 z = 0 →
          z = 0) ∧
        (∀ y ∈ U, ∀ (hy : y ∈ (𝓡∂ (8 + k + 1)).boundary M), v y = 0 →
          Manifold.IsSubmersionAt (𝓡∂ (8 + k + 1)) (𝓡 k) ∞ (fun y : M => a.1 (v y)) y ∧
          Manifold.IsSubmersionAt (𝓡 (8 + k)) (𝓡 k) ∞
            (fun y : ↥((𝓡∂ (8 + k + 1)).boundary M) => a.1 (v y)) ⟨y, hy⟩) := by
    intro x hxK
    obtain ⟨i, w0, j, hb, U, h1, h2, h3, h4, h5⟩ :=
      Work.ThomBordism.localDataTied (D := D) (Fam := Fam) G m hpow hphi hweak hne'
        x hxK.1 hxK.2
    exact ⟨⟨(Work.Tubular.readCLM (G.emb i) (Work.ThomBordism.tiedND G i) j w0).comp
        (Work.PTGeometric.projEuc k G.mU G.hmU), ⟨i, w0, j, hb, rfl⟩⟩,
      U, h1, h2, h3, h4, h5⟩
  -- ### Step 7: the finite cover of the boundary zeros, indexed by the pin data
  obtain ⟨mE, ℓU, UE, hUEopen, hUEcl, hUEinj, hUEtrans, hUEcov⟩ :=
    exists_finite_cover_of_pointwise
      (K := ((𝓡∂ (8 + k + 1)).boundary M ∩ {x : M | v x = 0}))
      (T := interior S0)
      (hbnd_closed.inter (isClosed_eq hvc continuous_const)).isCompact
      (fun (a : { ℓ : Work.PTGeometric.Amb (k + G.mU) →L[ℝ] Work.PTGeometric.Amb k //
          ∃ (i : ι) (w0 : (Fam i).pt)
            (j : Work.ThomBordism.PontryaginThom.CoverIdx (Fam i) k)
            (hb : w0 ∈ (Work.ThomBordism.tiedND G i).D.baseSet j),
            ℓ = (Work.Tubular.readCLM (G.emb i) (Work.ThomBordism.tiedND G i) j w0).comp
              (Work.PTGeometric.projEuc k G.mU G.hmU) }) (U : Set M) =>
        ∀ y ∈ U, ∀ (hy : y ∈ (𝓡∂ (8 + k + 1)).boundary M), v y = 0 →
          Manifold.IsSubmersionAt (𝓡∂ (8 + k + 1)) (𝓡 k) ∞ (fun y : M => a.1 (v y)) y ∧
          Manifold.IsSubmersionAt (𝓡 (8 + k)) (𝓡 k) ∞
            (fun y : ↥((𝓡∂ (8 + k + 1)).boundary M) => a.1 (v y)) ⟨y, hy⟩)
      (fun (a : { ℓ : Work.PTGeometric.Amb (k + G.mU) →L[ℝ] Work.PTGeometric.Amb k //
          ∃ (i : ι) (w0 : (Fam i).pt)
            (j : Work.ThomBordism.PontryaginThom.CoverIdx (Fam i) k)
            (hb : w0 ∈ (Work.ThomBordism.tiedND G i).D.baseSet j),
            ℓ = (Work.Tubular.readCLM (G.emb i) (Work.ThomBordism.tiedND G i) j w0).comp
              (Work.PTGeometric.projEuc k G.mU G.hmU) }) (S' : Set M) =>
        ∀ y ∈ S', ∀ z : Work.PTGeometric.Amb (k + G.mU), P y z = z → a.1 z = 0 → z = 0)
      (by
        intro x hxK
        exact hpoint x hxK)
      (by
        intro a U U' hU hUU' y hy hyb hvy
        exact hU y (hUU' hy) hyb hvy)
  have hUEint : ∀ j, UE j ⊆ interior S0 := fun j => subset_trans subset_closure (hUEcl j)
  -- **The spec'd zero-set boundary homeomorphism**, provided by `sourceZeroSet_boundary_homeo_spec`:
  -- obtained *explicitly* so that its specification (the tube dictionary of the boundary
  -- identification) is available in the rest of the proof.
  obtain ⟨hZero, hZeroSpec⟩ :=
    Work.ThomBordism.sourceZeroSet_boundary_homeo_spec_coord (D := D) (Fam := Fam) G m hpow
  have hzv : ∀ x : M, v x = 0 ↔ Hf x.1.1 ∈ G.core :=
    fun x => (G.core_iff_vec ⟨Hf x.1.1, hne' x⟩).symm
  have hset1 : (Send ∩ {x : M | v x = 0}) =
      {x : M | x.1.1 0 = 0 ∧ Hf x.1.1 ∈ G.core} := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨hx1, (hzv x).mp hx2⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨hx1, (hzv x).mpr hx2⟩
  -- **The middle identification, *specified***: it is the explicit map
  -- `fwd = fun x => x.1.1` transported along the compact-to-T2 homeomorphism, so its `coe` is
  -- `fwd` by `rfl` — the opacity of `Classical.choice` is removed here (`NOTE_HEND_OPAQUE.md`).
  let hmidH : (↥{x : M | x.1.1 0 = 0 ∧ Hf x.1.1 ∈ G.core}) ≃ₜ
      (↥(sourceZeroSet G m hpow ∩
        {y : EuclideanHalfSpace ((8 + k) + 1) | y.1 0 = 0})) := by
    have hcl : IsClosed {x : M | x.1.1 0 = 0 ∧ Hf x.1.1 ∈ G.core} :=
      (isClosed_eq hcoord0 continuous_const).inter (G.isClosed_core.preimage hbase)
    haveI : CompactSpace ↥{x : M | x.1.1 0 = 0 ∧ Hf x.1.1 ∈ G.core} :=
      isCompact_iff_compactSpace.mp
        (IsCompact.of_isClosed_subset isCompact_univ hcl (fun _ _ => mem_univ _))
    let fwd : ↥{x : M | x.1.1 0 = 0 ∧ Hf x.1.1 ∈ G.core} →
        ↥(sourceZeroSet G m hpow ∩
          {y : EuclideanHalfSpace ((8 + k) + 1) | y.1 0 = 0}) :=
      fun x => ⟨x.1.1, x.2.2, x.2.1⟩
    have hf : Continuous fun x : ↥{x : M | x.1.1 0 = 0 ∧ Hf x.1.1 ∈ G.core} => x.1.1 :=
      continuous_subtype_val.comp continuous_subtype_val
    have hfwd : Continuous fwd := hf.subtype_mk (fun x => ⟨x.2.2, x.2.1⟩)
    have hbij : Function.Bijective fwd := by
      constructor
      · intro a b hab
        have h2 : (a.1 : S.A) = (b.1 : S.A) := by
          have h3 := congrArg (fun t : ↥(sourceZeroSet G m hpow ∩
            {y : EuclideanHalfSpace ((8 + k) + 1) | y.1 0 = 0}) =>
              (t.1 : EuclideanHalfSpace ((8 + k) + 1))) hab
          simpa only [fwd] using h3
        exact Subtype.ext (Subtype.ext h2)
      · rintro ⟨y, hyZ, hy0⟩
        refine ⟨⟨⟨y, hZsub hyZ⟩, hy0, hyZ⟩, ?_⟩
        rfl
    exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective fwd hbij) hfwd
  let hHend : ↥(Send ∩ {x : M | v x = 0}) ≃ₜ (Σ i : Fin m × ι, (Fam i.2).pt) :=
    Homeomorph.trans (Homeomorph.trans (Homeomorph.setCongr hset1) hmidH) hZero

  -- ### Step 5quater: the **tube dictionary** of the boundary identification
  --
  -- The zero-set boundary identification `hHend = hZero ∘ hmidH ∘ setCongr hset1` is the *specified*
  -- one (`sourceZeroSet_boundary_homeo_spec`): for every point of the collapse end the piece
  -- coordinate in the tube chart is the image of an element of the unit cube under the cube
  -- parametrisation, and the corresponding loop of the block decomposition is the source homotopy's
  -- loop.  This is the raw coordinate input of the boundary-sign computation
  -- (`NOTE_SESSION50_EXPLICIT_GAMMA.md` §3, (T2)).
  have hHendTube : ∀ x : ↥(Send ∩ {x : M | v x = 0}),
      (G.emb (hZero (hmidH (Homeomorph.setCongr hset1 x))).1.2).e
          (hZero (hmidH (Homeomorph.setCongr hset1 x))).2
        = Work.Tubular.cubeToEuc (8 + k) G.R
            (Work.ThomBordism.blockTubePoint (D := D) (Fam := Fam) G m
              (cubeCoord (k + 8) (tail (k + 8)
                (srcCast k (hmidH (Homeomorph.setCongr hset1 x)).1.1)))) :=
    fun x => (hZeroSpec (hmidH (Homeomorph.setCongr hset1 x))).1

  let D0raw : Work.PTGeometric.RawAmbientData (k + G.mU) k (Fin m × ι) (fun a => Fam a.2) := {
    M := M
    P := P
    v := v
    hPc := hPc
    hvc := hvc
    hProj := by
      intro x
      exact G.coord_isProj ⟨Hf x.1.1, hne' x⟩
    hMem := by
      intro x
      exact G.coord_mem ⟨Hf x.1.1, hne' x⟩
    V := V
    hVopen := hVopen
    S0 := S0
    hS0cl := hS0cl
    hS0V := hS0V
    hPsmV := hPsmV
    hvsmV := hvsmV
    S := Send
    hScl := hScl
    hSsub := hSsub
    hSS0 := hSS0
    hend := hHend
    hzero_sub := hzero_sub
    δ := δ₀
    hδpos := hδ₀pos
    hδ := by
      intro x hx hxS0
      exact hδ₀ x ⟨hx, le_of_lt (not_le.mp hxS0)⟩
    mE := mE
    ellE := fun j => (ℓU j).1
    UE := UE
    isOpen_UE := hUEopen
    UE_int := hUEint
    ellE_inj := fun j y hy z hz hz0 => hUEinj j y (subset_closure hy) z hz hz0
    ellE_inj_cl := hUEinj
    bndZero_cov := fun x hx hvx => hUEcov x ⟨hx, hvx⟩
    bndZero_trans := fun j x hx hxb hvx => hUEtrans j x hx hxb hvx }


  -- ==================================================================================
  -- ## The zero set of the raw field
  -- ==================================================================================
  have hzv : ∀ x : M, v x = 0 ↔ Hf x.1.1 ∈ G.core :=
    fun x => (G.core_iff_vec ⟨Hf x.1.1, hne' x⟩).symm
  have hzvZ : ∀ x : M, v x = 0 ↔ x.1 ∈ sourceZeroSet G m hpow := by
    intro x
    rw [hzv x]
    rfl
  -- ==================================================================================
  -- ## Step 7bis: the smoothing of the raw field
  -- ==================================================================================
  obtain ⟨Lr, hLr⟩ := exists_Rmap_lipschitz (k + G.mU) k (Nat.le_add_right k G.mU)
  set εsm : ℝ := δ₀ / 2 with hεsm_def
  have hεsm : 0 < εsm := by rw [hεsm_def]; linarith
  obtain ⟨P₁, v₁, Pm, hP₁sm, hv₁sm, hPmsm, hPmclose, hP₁Rmap, hmem₁, heq₁, hclose₁⟩ :=
    smoothMap_into_tautTotal_eqOn_close_pm (k + G.mU) k (Nat.le_add_right k G.mU) (by omega) M P v
      hPc hvc S0 hS0cl V hVopen hS0V hPsmV hvsmV
      (fun x => G.coord_isProj ⟨Hf x.1.1, hne' x⟩)
      (fun x => G.coord_mem ⟨Hf x.1.1, hne' x⟩) Lr hLr εsm hεsm
  have heqP₁ : ∀ x ∈ S0, P₁ x = P x := fun x hx => (heq₁ x hx).1
  have heqP₁' : ∀ x ∈ S0, P₁ x = D0raw.P x := heqP₁
  have heqv₁ : ∀ x ∈ S0, v₁ x = v x := fun x hx => (heq₁ x hx).2
  have hP₁proj : ∀ x : M, P₁ x ∈ Gr (k + G.mU) k := fun x => (hmem₁ x).1
  have hP₁mem : ∀ x : M, P₁ x (v₁ x) = v₁ x := fun x => (hmem₁ x).2
  have hv₁ne : ∀ x ∈ (𝓡∂ (8 + k + 1)).boundary M, x ∉ S0 → v₁ x ≠ 0 := by
    intro x hx hxS0 hvx
    have hδx : δ₀ ≤ ‖v x‖ := hδ₀ x ⟨hx, le_of_lt (not_le.mp hxS0)⟩
    have htri : ‖v x‖ ≤ ‖v₁ x‖ + ‖v₁ x - v x‖ := by
      have h1 := norm_sub_le (v₁ x) (v₁ x - v x)
      have hvv : v₁ x - (v₁ x - v x) = v x := by abel
      rw [hvv] at h1
      exact h1
    have h0 : ‖v₁ x‖ = 0 := by rw [hvx, norm_zero]
    rw [h0, zero_add] at htri
    have h2 : ‖v₁ x - v x‖ < εsm := hclose₁ x
    rw [hεsm_def] at h2
    linarith
  have hv₁S0 : ∀ x ∈ (𝓡∂ (8 + k + 1)).boundary M, v₁ x = 0 → x ∈ S0 := by
    intro x hx hvx
    by_contra hxS0
    exact hv₁ne x hx hxS0 hvx
  -- ==================================================================================
  -- ## Step 7ter: the chart family
  -- ==================================================================================
  have hclAll : ∀ j : Fin D0raw.mE, closure (D0raw.UE j) ⊆
      {y : M | ∀ z : EuclideanSpace ℝ (Fin (k + G.mU)), P₁ y z = z →
        D0raw.ellE j z = 0 → z = 0} := by
    intro j y hy z hz h0
    have hyS0 : y ∈ S0 := interior_subset (hUEcl j hy)
    rw [heqP₁ y hyS0] at hz
    exact D0raw.ellE_inj_cl j hy z hz h0
  obtain ⟨m', C, hC⟩ := nonempty_ambCharts_of_family_verbatim M hP₁sm hP₁proj D0raw.mE
    D0raw.ellE D0raw.UE D0raw.isOpen_UE hclAll
  -- ==================================================================================
  -- ## Step 7quater: the boundary goodness and the perturbation
  -- ==================================================================================
  have hoff : ∀ x ∈ (𝓡∂ (8 + k + 1)).boundary M, AmbGood C v₁ x := by
    intro x hx
    by_cases h0 : v₁ x = 0
    · have hxS0 : x ∈ S0 := hv₁S0 x hx h0
      have hvx : v x = 0 := by rw [← heqv₁ x hxS0]; exact h0
      obtain ⟨j, hj⟩ := D0raw.bndZero_cov x hx hvx
      obtain ⟨hsub, -⟩ := D0raw.bndZero_trans j x hj hx hvx
      obtain ⟨l, hlell, hUeq⟩ := hC j
      refine Or.inr ⟨l, hUeq ▸ hj, ?_⟩
      have hev : (fun y => D0raw.ellE j (v y)) =ᶠ[𝓝 x] (fun y => D0raw.ellE j (v₁ y)) := by
        filter_upwards [isOpen_interior.mem_nhds (D0raw.UE_int j hj)] with y hy
        rw [heqv₁ y (interior_subset hy)]
      rw [hlell]
      exact (IsSubmersionAt.congr_iff hev).mp hsub
    · exact Or.inl h0
  obtain ⟨χ, hχsm, hχrange, hχU, hχint, hχbd, hχcov⟩ := exists_cutoffs C v₁ hv₁sm hoff
  obtain ⟨w, hwsm, hwmem, hwv, hwgood⟩ := exists_ambient_perturbation C v₁ hv₁sm hP₁mem χ
    hχsm hχrange hχU hχint hχbd hχcov
  -- ==================================================================================
  -- ## Step 7quinquies: the collar parameter and the agreement of `w` with `v₁`
  -- ==================================================================================
  obtain ⟨Vχ, hVχopen, hbdVχ, hχVχ⟩ := hχbd
  have hheadnn : ∀ x : M, 0 ≤ x.1.1 0 := fun x => x.1.2
  have hθ : ∃ θ : ℝ, 0 < θ ∧ ∀ x : M, x ∉ Vχ → θ ≤ x.1.1 0 := by
    by_cases hne : ((Vχ)ᶜ : Set M).Nonempty
    · have hKc : IsCompact ((Vχ)ᶜ : Set M) := hVχopen.isClosed_compl.isCompact
      obtain ⟨x₀, hx₀, hmin⟩ := hKc.exists_isMinOn hne hcoord0.continuousOn
      have hx₀pos : 0 < x₀.1.1 0 := by
        rcases lt_or_eq_of_le (hheadnn x₀) with h | h
        · exact h
        · exfalso
          have hmem : x₀ ∈ (𝓡∂ (8 + k + 1)).boundary M := by
            rw [S.mem_boundary_iff]
            exact Or.inl ((hbnd x₀.1).mpr h.symm)
          exact hx₀ (hbdVχ hmem)
      exact ⟨x₀.1.1 0, hx₀pos, fun x hx => hmin hx⟩
    · exact ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hne⟩
  obtain ⟨θ, hθpos, hθbound⟩ := hθ
  set εcl : ℝ := min (θ / 2) (1 / 8) with hεcl_def
  have hεcl_pos : 0 < εcl := lt_min (by linarith) (by norm_num)
  have hεcl_half : εcl ≤ 1 / 2 := by
    rw [hεcl_def]
    exact le_trans (min_le_right _ _) (by norm_num)
  have hεcl_quarter : εcl ≤ 1 / 4 := by
    rw [hεcl_def]
    exact le_trans (min_le_right _ _) (by norm_num)
  have hεcl_θ : εcl < θ := by
    rw [hεcl_def]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεclVχ : ∀ x : M, x.1.1 0 ≤ εcl → x ∈ Vχ := by
    intro x hx
    by_contra hc
    have h := hθbound x hc
    linarith
  have hwv₁ : ∀ x : M, x.1.1 0 ≤ εcl → w x = v₁ x :=
    fun x hx => hwv x (fun l => hχVχ l x (hεclVχ x hx))
  have hv₁v : ∀ x : M, x.1.1 0 ≤ εcl → v₁ x = v x :=
    fun x hx => heqv₁ x (hεcl_quarter.trans' hx)
  have hS0le : ∀ x : M, x.1.1 0 ≤ εcl → x ∈ S0 :=
    fun x hx => (hεcl_quarter.trans' hx)
  have hwS0 : ∀ x : M, x.1.1 0 ≤ εcl → w x = v x :=
    fun x hx => (hwv₁ x hx).trans (hv₁v x hx)
  -- ==================================================================================
  -- ## Step 8: the boundary transfer to the perturbed field
  -- ==================================================================================
  have hwBdry : ∀ x ∈ (𝓡∂ (8 + k + 1)).boundary M, w x = 0 → v x = 0 := by
    intro x hx hxw
    have h1 : w x = v₁ x := hwv x (fun l => hχVχ l x (hbdVχ hx))
    have hxS0 : x ∈ S0 := by
      by_contra hc
      exact hv₁ne x hx hc (by rw [← h1]; exact hxw)
    exact (heqv₁ x hxS0).symm.trans (by rw [← h1]; exact hxw)
  have hwSend : ∀ x ∈ Send, w x = v x := by
    intro x hx
    have hxS0 : x ∈ S0 := by
      show x.1.1 0 ≤ 1 / 4
      rw [hx]
      norm_num
    exact (hwv x (fun l => hχVχ l x (hbdVχ (hSsub hx)))).trans (heqv₁ x hxS0)
  have hwCov : ∀ x ∈ (𝓡∂ (8 + k + 1)).boundary M, w x = 0 → ∃ j, x ∈ UE j :=
    fun x hx hxw => D0raw.bndZero_cov x hx (hwBdry x hx hxw)
  have hwTrans : ∀ j : Fin D0raw.mE, ∀ x ∈ D0raw.UE j, ∀ hx : x ∈ (𝓡∂ (8 + k + 1)).boundary M,
      w x = 0 →
      IsSubmersionAt (𝓡∂ (8 + k + 1)) (𝓡 k) ∞ (fun y => D0raw.ellE j (w y)) x ∧
      IsSubmersionAt (𝓡 (8 + k)) (𝓡 k) ∞
        (fun y : ↥((𝓡∂ (8 + k + 1)).boundary M) => D0raw.ellE j (w y.1)) ⟨x, hx⟩ := by
    intro j x hxj hx hxw
    have hvx : v x = 0 := hwBdry x hx hxw
    obtain ⟨h1, h2⟩ := D0raw.bndZero_trans j x hxj hx hvx
    have hxint : x ∈ interior S0 := D0raw.UE_int j hxj
    have hev : (fun y => D0raw.ellE j (v y)) =ᶠ[𝓝 x] (fun y => D0raw.ellE j (w y)) := by
      filter_upwards [isOpen_interior.mem_nhds hxint, hVχopen.mem_nhds (hbdVχ hx)] with y hy hyV
      rw [← heqv₁ y (interior_subset hy), ← hwv y (fun l => hχVχ l y hyV)]
    have hev2 : (fun y : ↥((𝓡∂ (8 + k + 1)).boundary M) => D0raw.ellE j (v y.1))
        =ᶠ[𝓝 (⟨x, hx⟩ : ↥((𝓡∂ (8 + k + 1)).boundary M))]
        (fun y : ↥((𝓡∂ (8 + k + 1)).boundary M) => D0raw.ellE j (w y.1)) := by
      have hop : (Subtype.val ⁻¹' interior S0) ∈
          𝓝 (⟨x, hx⟩ : ↥((𝓡∂ (8 + k + 1)).boundary M)) :=
        (continuous_subtype_val (p := fun z : M =>
          z ∈ (𝓡∂ (8 + k + 1)).boundary M)).continuousAt.preimage_mem_nhds
          (isOpen_interior.mem_nhds hxint)
      filter_upwards [hop] with y hy
      have hyVχ : (y : M) ∈ Vχ := hbdVχ y.2
      rw [← heqv₁ (y : M) (interior_subset hy), ← hwv (y : M) (fun l => hχVχ l (y : M) hyVχ)]
    exact ⟨(IsSubmersionAt.congr_iff hev).mp h1, (IsSubmersionAt.congr_iff hev2).mp h2⟩
  -- ==================================================================================
  -- ## Step 9: the level data of the perturbed zero set
  -- ==================================================================================
  have hgetW : ∀ x : {y : M | w y = 0}, ∃ l : Fin m', (x : M) ∈ C.U l ∧
      IsSubmersionAt (𝓡∂ (8 + k + 1)) (𝓡 k) ∞ (fun y => C.ell l (w y)) (x : M) ∧
      ((hxb : (x : M) ∈ (𝓡∂ (8 + k + 1)).boundary M) →
        IsSubmersionAt (𝓡 (8 + k)) (𝓡 k) ∞
          (fun z : ↥((𝓡∂ (8 + k + 1)).boundary M) => C.ell l (w z.1)) ⟨(x : M), hxb⟩) := by
    intro x
    by_cases hx : (x : M) ∈ (𝓡∂ (8 + k + 1)).boundary M
    · obtain ⟨j, hj⟩ := hwCov x.1 hx x.2
      obtain ⟨l, hlell, hUeq⟩ := hC j
      obtain ⟨hsub, hbsub⟩ := hwTrans j x.1 hj hx x.2
      refine ⟨l, hUeq ▸ hj, ?_, ?_⟩
      · rw [hlell]; exact hsub
      · intro _
        rw [hlell]; exact hbsub
    · rcases hwgood x.1 with h | ⟨l, hxl, hsub⟩
      · exact absurd x.2 h
      · exact ⟨l, hxl, hsub, fun hcontra => absurd hcontra hx⟩
  choose lW hlW using hgetW
  let L : Work.PTGeometric.LocalLevelData k M {y : M | w y = 0} :=
    { U := fun x => C.U (lW x)
      isOpen_U := fun x => C.isOpen_U (lW x)
      mem_U := fun x => (hlW x).1
      g := fun x y => C.ell (lW x) (w y)
      contMDiff_g := fun x => (C.ell (lW x)).contMDiff.comp hwsm
      zero_iff := fun x y hy => by
        constructor
        · intro h0
          exact C.ell_inj (lW x) y hy (w y) (hwmem y) h0
        · intro hyw
          rw [show w y = 0 from hyw, map_zero]
      isSubmersion_g := fun x => (hlW x).2.1
      bndSubmersion := fun x hx => (hlW x).2.2 hx }
  -- ==================================================================================
  -- ## Step 10: the collar set and its ray structure
  -- ==================================================================================
  let Z : Set (EuclideanHalfSpace ((8 + k) + 1)) :=
    {y | ∃ h : S.Φ y ≤ 0, w ⟨y, h⟩ = 0}
  have hWeqNew : {x : M | w x = 0} = lvlSet k S.Φ Z := by
    ext x
    constructor
    · intro hx
      show ∃ h : S.Φ x.1 ≤ 0, w ⟨x.1, h⟩ = 0
      exact ⟨x.2, hx⟩
    · rintro ⟨h2, h3⟩
      have he : (⟨x.1, h2⟩ : M) = x := Subtype.ext rfl
      rw [← he]
      exact h3
  have hZmem : ∀ (y : EuclideanHalfSpace ((8 + k) + 1))
      (h : S.Φ y ≤ 0), Z y → w ⟨y, h⟩ = 0 := by
    intro y h hyZ
    obtain ⟨h', hw'⟩ := hyZ
    have he : (⟨y, h'⟩ : M) = ⟨y, h⟩ := Subtype.ext rfl
    rwa [he] at hw'
  have hZraw : ∀ y ∈ Z, S.Φ y ≤ 0 → y.1 0 ≤ εcl →
      y ∈ sourceZeroSet G m hpow := by
    intro y hyZ hyΦ hyε
    have hw0 : w ⟨y, hyΦ⟩ = 0 := hZmem y hyΦ hyZ
    have hv₁0 : v₁ ⟨y, hyΦ⟩ = 0 := by rw [← hwv₁ ⟨y, hyΦ⟩ hyε]; exact hw0
    have hv0 : v ⟨y, hyΦ⟩ = 0 := by
      rw [← hv₁v ⟨y, hyΦ⟩ hyε]
      exact hv₁0
    exact (hzvZ ⟨y, hyΦ⟩).mp hv0
  have hZsNew : ∀ y ∈ Z, y.1 0 ≤ εcl → ∀ (s : ℝ) (hs : 0 ≤ s), s ≤ εcl →
      halfCons k s hs y.1 ∈ Z := by
    intro y hyZ hyε s hs hsε
    have hyΦ : S.Φ y ≤ 0 := hyZ.1
    have hyZraw : y ∈ sourceZeroSet G m hpow := hZraw y hyZ hyΦ hyε
    have hraise : halfCons k s hs y.1 ∈ sourceZeroSet G m hpow :=
      mem_sourceZeroSet_of_collarRay G m hpow hyZraw (le_trans hyε hεcl_half)
        (fun i hi => by
          rw [halfCons_coe, Work.PTGeometric.consVec_ofLp_ne_zero s (Work.PTGeometric.tailVec y.1) hi,
            Work.PTGeometric.tailVec_ofLp_ne_zero hi])
        (by rw [halfCons_head]; exact le_trans hsε hεcl_half)
    have hΦraise : S.Φ (halfCons k s hs y.1) ≤ 0 := hZsub hraise
    refine ⟨hΦraise, ?_⟩
    show w ⟨halfCons k s hs y.1, hΦraise⟩ = 0
    have hhead : (halfCons k s hs y.1).1 0 ≤ εcl := by rw [halfCons_head]; exact hsε
    rw [hwv₁ ⟨halfCons k s hs y.1, hΦraise⟩ hhead]
    rw [hv₁v ⟨halfCons k s hs y.1, hΦraise⟩ hhead]
    exact (hzvZ ⟨halfCons k s hs y.1, hΦraise⟩).mpr hraise
  have hrayNew : ∀ y ∈ Z, y.1 0 = 0 → ∀ (s : ℝ) (hs : 0 ≤ s), s ≤ εcl →
      S.Φ (halfCons k s hs y.1) ≤ 0 := by
    intro y hyZ hy0 s hs hsε
    have hyΦ : S.Φ y ≤ 0 := hyZ.1
    have hyZraw : y ∈ sourceZeroSet G m hpow :=
      hZraw y hyZ hyΦ (by rw [hy0]; exact le_of_lt hεcl_pos)
    have hraise : halfCons k s hs y.1 ∈ sourceZeroSet G m hpow :=
      mem_sourceZeroSet_of_collarRay G m hpow hyZraw
        (by rw [hy0]; exact le_trans (le_of_lt hεcl_pos) hεcl_half)
        (fun i hi => by
          rw [halfCons_coe, Work.PTGeometric.consVec_ofLp_ne_zero s (Work.PTGeometric.tailVec y.1) hi,
            Work.PTGeometric.tailVec_ofLp_ne_zero hi])
        (by rw [halfCons_head]; exact le_trans hsε hεcl_half)
    exact hZsub hraise
  have hΦ0New : ∀ y ∈ Z, y.1 0 < εcl →
      S.Φ (halfCons k 0 (le_refl 0) y.1) ≤ 0 := by
    intro y hyZ hyε
    have hyΦ : S.Φ y ≤ 0 := hyZ.1
    have hyZraw : y ∈ sourceZeroSet G m hpow := hZraw y hyZ hyΦ (le_of_lt hyε)
    have hraise : halfCons k 0 (le_refl 0) y.1 ∈ sourceZeroSet G m hpow :=
      mem_sourceZeroSet_of_collarRay G m hpow hyZraw (le_trans (le_of_lt hyε) hεcl_half)
        (fun i hi => by
          rw [halfCons_coe,
            Work.PTGeometric.consVec_ofLp_ne_zero (0 : ℝ) (Work.PTGeometric.tailVec y.1) hi,
            Work.PTGeometric.tailVec_ofLp_ne_zero hi])
        (by rw [halfCons_head]; norm_num)
    exact hZsub hraise
  -- ==================================================================================
  -- ## Step 11: the collar
  -- ==================================================================================
  letI hTopReg : ChartedSpace (EuclideanHalfSpace (8 + k + 1))
      {x : EuclideanHalfSpace ((8 + k) + 1) // S.Φ x ≤ 0} := S.chartedSpaceOfRegion
  letI hManReg : IsManifold (𝓡∂ (8 + k + 1)) ∞
      {x : EuclideanHalfSpace ((8 + k) + 1) // S.Φ x ≤ 0} := S.isManifoldOfRegion
  letI hCompReg : CompactSpace {x : EuclideanHalfSpace ((8 + k) + 1) // S.Φ x ≤ 0} :=
    S.compactSpaceOfRegion
  letI hT2Reg : T2Space {x : EuclideanHalfSpace ((8 + k) + 1) // S.Φ x ≤ 0} := S.t2SpaceOfRegion
  letI hNeReg : Nonempty {x : EuclideanHalfSpace ((8 + k) + 1) // S.Φ x ≤ 0} := hMne
  have hWclNew : IsClosed {x : M | w x = 0} := isClosed_eq hwsm.continuous continuous_const
  letI hChNew : ChartedSpace (EuclideanHalfSpace 9)
      (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L) :=
    Work.PTGeometric.Lvl.Setup.instChartedSpace
      (Work.PTGeometric.levelSetup {x : M | w x = 0} hWclNew L)
  have hWzero : ∀ w' : ↥{y : M | w y = 0}, (S.Φ w'.1.1 = 0) → w'.1.1.1 0 = 0 := by
    intro w' hΦ0
    have hzb : w'.1 ∈ (𝓡∂ (8 + k + 1)).boundary M := by
      rw [S.mem_boundary_iff]
      exact Or.inr hΦ0
    exact D0raw.hzero_sub w'.1 hzb (hwBdry w'.1 hzb w'.2)
  have hbdryNew : (modelWithCornersEuclideanHalfSpace 9).boundary
      (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L) =
      {x : Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L | x.1.1.1 0 = 0} := by
    ext w'
    constructor
    · intro hw
      have h1 : w'.1 ∈ (𝓡∂ (8 + k + 1)).boundary M :=
        (Work.PTGeometric.Lvl.Setup.mem_boundary_iff
          (Work.PTGeometric.levelSetup {x : M | w x = 0} hWclNew L) w').mp hw
      rcases (S.mem_boundary_iff w'.1).mp h1 with h | h
      · exact (hbnd w'.1.1).mp h
      · exact hWzero w' h
    · intro h
      refine (Work.PTGeometric.Lvl.Setup.mem_boundary_iff
        (Work.PTGeometric.levelSetup {x : M | w x = 0} hWclNew L) w').mpr ?_
      exact (S.mem_boundary_iff w'.1).mpr (Or.inl ((hbnd w'.1.1).mpr h))
  have hcollarNew : @Nonempty (@Work.Surgery.Collar 8
      (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L) _
      (Work.PTGeometric.Lvl.Setup.instChartedSpace
        (Work.PTGeometric.levelSetup {x : M | w x = 0} hWclNew L))) :=
    nonempty_collar_of_collarRay S.Φ Z {x : M | w x = 0} hWeqNew hWclNew
      εcl hεcl_pos hεcl_half hZsNew hrayNew hΦ0New L
      (Work.PTGeometric.Lvl.Setup.instChartedSpace
        (Work.PTGeometric.levelSetup {x : M | w x = 0} hWclNew L)) hbdryNew
  -- ==================================================================================
  -- ## Step 12: the raw ambient data carrying the perturbed field
  -- ==================================================================================
  have hHset : (Send ∩ {x : M | w x = 0}) = (Send ∩ {x : M | v x = 0}) := by
    ext x
    constructor
    · rintro ⟨hx, hxw⟩
      refine ⟨hx, ?_⟩
      show v x = 0
      exact hwBdry x (hSsub hx) (show w x = 0 from hxw)
    · rintro ⟨hx, hxv⟩
      refine ⟨hx, ?_⟩
      show w x = 0
      rw [hwSend x hx]
      exact (show v x = 0 from hxv)
  let hHendNew : ↥(Send ∩ {x : M | w x = 0}) ≃ₜ (Σ i : Fin m × ι, (Fam i.2).pt) :=
    (Homeomorph.setCongr hHset).trans hHend

  -- **The tube dictionary for the perturbed identification `hHendNew`** (the `hend` of the datum
  -- `D0'` below): for every point of the collapse end, the piece coordinate in its tube chart is the
  -- image under the cube parametrisation of an element of the unit cube, and the corresponding block
  -- loop is the source homotopy's loop.  This is the raw coordinate input of the boundary-sign
  -- computation (`NOTE_SESSION50_EXPLICIT_GAMMA.md` §3, (T2)).
  have hHendNewTube := fun x : ↥(Send ∩ {x : M | w x = 0}) =>
    hHendTube (Homeomorph.setCongr hHset x)
  -- ==================================================================================
  -- ## Step 11bis: the coframing of the perturbed plane field, and the orientation family
  -- ==================================================================================
  haveI hιneI : Nonempty ι := hιne
  have hΓc : Continuous (fun x : M => G.gauss ⟨Hf x.1.1, hne' x⟩) :=
    G.continuous_gauss.comp hcont
  have hΓp : ∀ x : M, projOfPlane k G.mU (G.gauss ⟨Hf x.1.1, hne' x⟩) = P x :=
    fun x => by rw [G.gauss_proj ⟨Hf x.1.1, hne' x⟩]
  -- **This is the place where the coorientation of the level set is pinned**: the oriented lift
  -- `Γ₂` is produced from the Gauss field `x ↦ G.gauss ⟨Hf x, _⟩` by the *pointwise* deformation
  -- `t ↦ olQ x t` of `Work.ThomBordism.exists_orientedLift_of_Rmap_eq` (the `Rmap`-form of
  -- `exists_orientedLift_of_close`), called with `S := S0 = {x | x 0 ≤ 1/4}` -- the slab that
  -- contains every piece (`Send ⊆ S0`).  The hypothesis is discharged by `hP₁Rmap` + `heqP₁`
  -- (`P₁ = Rmap ∘ Pm` everywhere and `P₁ = P` on `S0`), so the fourth clause records, *locally*,
  -- that on the slab the coorientation used for the level set IS the Gauss field's orientation:
  --
  --   hΓ₂eqS0 : ∀ x ∈ S0, Γ₂ x = G.gauss ⟨Hf x.1.1, hne' x⟩ .            -- (†)
  --
  -- Combined with `famGauss = proj ∘ famUnpack` and `Work.ThomBordism.gaussTubeDataFibre` (PROVED,
  -- the plane of `famUnpack` IS the plane of the tube's classifying map) this says that the
  -- coorientation of the level set at the pieces is the *frame orientation of `pulledThom`* -- and
  -- the piece's own class is, by the field `GenuineTubeGeometry.localDegree` together with
  -- `Work.PTGeometric.proj_relCapPair_pulledThom_collapse` (PROVED), exactly the tube push of that
  -- same orientation.  So the remaining comparison of the boundary sign is *self-consistent* on the
  -- `pulledThom` side: the only constant left in it is the universal Koszul sign of the linear model
  -- (`Work.ThomBordism.stdHalfBallBoundarySign`), the same at every piece.  See
  -- `NOTE_SESSION41.md` §1 and `NOTE_SESSION42.md`.
  obtain ⟨Γ₂, hΓ₂c, hΓ₂spec, hΓ₂eqS0⟩ :=
    Work.ThomBordism.exists_orientedLift_of_Rmap_eq k G.mU (M := M) (P := P)
      (G := fun x : M => G.gauss ⟨Hf x.1.1, hne' x⟩) (Pm := Pm) (S := S0)
      hPc (fun x => G.coord_isProj ⟨Hf x.1.1, hne' x⟩) hΓc hΓp hPmsm.continuous hPmclose
      (fun x hx => (hP₁Rmap x).symm.trans (heqP₁ x hx))
  have hΓ₂eq : ∀ x : M, projOfPlane k G.mU (Γ₂ x) = P₁ x := fun x => by
    rw [hΓ₂spec x, ← hP₁Rmap x]
  -- **The coframing is taken *explicitly*** (`Work.ThomBordism.coframingExplicitOfLift`, PROVED):
  -- its witnesses are named (`cfU`, `cfℓ`, `cfe`), and it is positively oriented for the lift `Γ₂`
  -- (`Work.ThomBordism.Grassmann.eOfOriented`, the last clause `hcfpos`).  Naming the witness is
  -- what makes the *value* of the orientation family below computable (session 57, §1(b)/§2).
  obtain ⟨cfmE, cfU, cfℓ, cfe, hcfUopen, hcfUcov, hcfℓe, hcfinj, hcfpos, _hcfname, hcforient⟩ :=
    Work.ThomBordism.coframingExplicitOfLift (k := k) (m := G.mU) (M := M) (P := P₁)
      hP₁sm.continuous hP₁proj Γ₂ hΓ₂c hΓ₂eq {x : M | w x = 0}
  have hcof : PlaneFieldCoframing (k + G.mU) k M P₁ {x : M | w x = 0} :=
    ⟨cfmE, cfU, cfℓ, cfe, hcfUopen, hcfUcov, hcfℓe, hcfinj, hcfpos⟩
  have hMdet : AmbientPositiveAtlas k M :=
    Work.ThomBordism.sourceRegion_extChart_transition_det_pos (D := D) (Fam := Fam)
      G m hpow hphi hweak
  have hlinkW : ∀ x ∈ {x : M | w x = 0},
      Set.range (mfderiv (𝓡∂ (8 + k + 1)) (modelWithCornersSelf ℝ (Amb (k + G.mU))) w x) =
        {z : Amb (k + G.mU) | P₁ x z = z} :=
    fun x hx => Work.PTGeometric.range_mfderiv_eq_fixed_of_ambGood (P := P₁) (m := m')
      C hP₁sm hwsm hwmem hx (hwgood x)
  obtain ⟨i₀⟩ := hιne
  obtain ⟨y₀⟩ := hne i₀
  have hWneNew : ({x : M | w x = 0} : Set M).Nonempty :=
    ⟨(hHendNew.symm ⟨(⟨0, hm⟩, i₀), y₀⟩ : M),
      (hHendNew.symm ⟨(⟨0, hm⟩, i₀), y₀⟩).2.2⟩
  -- The bundled coframed level-set datum, so that the *valued* orientation-family theorem applies
  -- (`Work.ThomBordism.orientationFamily_valued_of_coframing`): its `γ` is the corrected atlas's
  -- family, whose value on every interior point is `flipSign x` times the `Lvl`-chart transfer of
  -- the Euclidean generator.  This is the replacement of the opaque
  -- `orientationFamily_of_coframingDataBase` that session 57 asked for (§3 steps 1-2).
  let Dcf : Work.ThomBordism.CofAtlas.Cof k (k + G.mU) M :=
    { hMdet := hMdet
      P := P₁
      hPgr := hP₁proj
      v := w
      hvsm := hwsm
      hPv := hwmem
      W := {x : M | w x = 0}
      hWcl := hWclNew
      hW := rfl
      hlink := hlinkW
      L := L
      m := cfmE
      U := cfU
      ℓ := cfℓ
      e := cfe
      hUopen := hcfUopen
      hUcov := hcfUcov
      hℓe := hcfℓe
      heinj := hcfinj
      hpos := hcfpos }
  obtain ⟨γ, hγ, hγval⟩ :=
    Work.ThomBordism.orientationFamily_valued_of_coframing (k := k) (n := k + G.mU) Dcf
      hWneNew hcollarNew

  let D0' : Work.PTGeometric.RawAmbientData (k + G.mU) k (Fin m × ι) (fun a => Fam a.2) := {
    M := M
    P := P₁
    v := w
    hPc := hP₁sm.continuous
    hvc := hwsm.continuous
    hProj := hP₁proj
    hMem := hwmem
    V := Set.univ
    hVopen := isOpen_univ
    S0 := Set.univ
    hS0cl := isClosed_univ
    hS0V := Set.subset_univ _
    hPsmV := hP₁sm.contMDiffOn
    hvsmV := hwsm.contMDiffOn
    S := Send
    hScl := hScl
    hSsub := hSsub
    hSS0 := Set.subset_univ _
    hend := hHendNew
    hzero_sub := fun x hx hxw => D0raw.hzero_sub x hx (hwBdry x hx hxw)
    δ := 1
    hδpos := one_pos
    hδ := fun x hx hxS0 => absurd (Set.mem_univ x) hxS0
    mE := D0raw.mE
    ellE := D0raw.ellE
    UE := D0raw.UE
    isOpen_UE := D0raw.isOpen_UE
    UE_int := fun j => by rw [interior_univ]; exact Set.subset_univ _
    ellE_inj := fun j y hy z hz h0 =>
      D0raw.ellE_inj j y hy z
        (by rw [← heqP₁' y (interior_subset (D0raw.UE_int j hy))]; exact hz) h0
    ellE_inj_cl := fun j y hy z hz h0 =>
      D0raw.ellE_inj_cl j hy z
        (by rw [← heqP₁' y (interior_subset (hUEcl j hy))]; exact hz) h0
    bndZero_cov := hwCov
    bndZero_trans := fun j x hxj hx hxw => hwTrans j x hxj hx hxw }
  refine ⟨?_⟩
  refine { datum := D0'
           tied := fun j => (ℓU j).2
           hWcl := hWclNew
           L := L
           orient := ?_
           coord := ?_ }
  exact ⟨hcollarNew, γ, hγ⟩
  -- ==================================================================================
  -- **THE RESIDUAL**, in place: `SourceBoundaryCoord D0'`.
  -- ==================================================================================
  --
  -- Everything the assembly consumes is proved and in scope here; what is missing is the
  -- *uniformity of the orientation polarity of `hend` across the pieces* -- see
  -- `NOTE_SESSION58_GEOMETRY_OF_THE_SIGN.md` (the full re-derivation: the sign is a
  -- Koszul/outward-normal computation in the *tube* coordinates, uniform because it is one formula
  -- per piece) and `NOTE_S53_TUBE_DICT_AND_T1T2.md` §3.  Concretely, the two available
  -- bricks (child H4-L2828 `Work.ThomBordism.boundarySign_chartLocal` and child H4-L2830
  -- `Work.ThomBordism.sourceBoundaryClass_localGenerator`) are BOTH sign-blind: together they give
  -- `locClass (hPairδ w) x = ε x • locClass ῆ x` with `ε` locally constant on `∂W`, hence constant
  -- on each *component* = each piece; the consumer needs ONE `ε`.
  --
  -- The plan of the remaining computation, with everything it needs already in scope or PROVED:
  --
  -- 1. `w` with prescribed interior local classes: `obtain ⟨w, hwfund, hwloc⟩ :=
  --    Work.ThomBordism.exists_relFundClass_of_collar_loc (n := 8) hcollarNew γ hγ` — so the local
  --    class of `w` at every interior point is `γ x hx`, which by construction is
  --    `Work.PTGeometric.HOF.chartTr (icChart 8 _ x) x _ (HOF.eucFam 9 _ _)` (the coframing atlas).
  --    **This is now *available*: `hγval` (from `orientationFamily_valued_of_coframing`, session 58)
  --    states exactly `γ x hx = flipSign x • chartTr (icChart 8 _ x) x _ (eucFam 9 _)`, so
  --    `boundarySign_chartLocal` (T1) can be *applied* to `w₀` here (up to the `flipSign x₀ ∈ {±1}`
  --    factor, absorbed by T1's free constant).**
  -- 2. `locClass (hPairδ w) x` at a boundary point `x` is determined by the interior class at one
  --    interior point of a coordinate half-ball around `x` (PROVED:
  --    `Work.ThomBordism.locClass_hPairDelta_eq_of_localClass_eq` +
  --    `Work.ThomBordism.halfBallLocalisation_hPairDelta_eq`).
  -- 3. `locClass ῆ x` is the transfer along `piecePush D0' a` of `locClass ((Fam a.2).c) y`
  --    (PROVED: `Work.ThomBordism.locClass_sourceBoundaryClass_piece`).
  -- 4. **The tube dictionary** (`hHendNewTube`, Step 5quater above) puts the boundary point `x` at
  --    `(G.emb i).e x = cubeToEuc (8 + k) G.R u`, i.e. in the tube chart; the parametrisation
  --    `cubeToEuc` has *positive* determinant (its coordinates are `2R (t - 1/2)`, `R > 0`), which
  --    transfers to `eucFam`-invariance via `Work.PTGeometric.HOF.eucFam_germ_ball`.
  -- 5. The coorientation of the level set at the pieces is read off `G.gauss ∘ Hf` (`hΓ₂eqS0`
  --    above), whose plane is `padGaussFunM (emb i) (ND i)` up to the branch
  --    (`Work.PTGeometric.canonicalLift_plane`, `GenuineTubeGeometry.tie`, PROVED), and TEL
  --    (`Work.ThomBordism.sigmaTelescope_gauss`, PROVED) turns `(c_i-oriented tangent frame) ∧
  --    gframe = ambient orientation` into the c_i-orientation of the piece.
  -- 6. The branch is UNIFORM over the pieces: `Work.ThomBordism.gaussBranch_uniform` (PROVED) from
  --    `Work.ThomBordism.localDegree_universalThomClass` (PROVED).  Hence the polarity in 4/5 is
  --    the same at every piece, and the comparison of steps 2 and 3 gives the single `ε` for
  --    `Work.ThomBordism.sourceBoundaryCoord_of_assemblyDataRaw` (PROVED) applied to `D0'`.
  --
  -- The last two steps are chart-level determinant/local-class computations; they cannot be
  -- delegated (they live inside this proof), and `boundarySign_transfer` (PROVED) is the template
  -- (its global `Φ : W ≃ₜ ↥(stdHalfBall 9)` does not exist for a bordism, so its *local* version is
  -- the plumbing to build).
  --
  -- **What is already plumbed in place**: the canonical identification of the level model's
  -- boundary with the pieces (`Work.ThomBordism.levelBdryHomeoOf`, PROVED, cycle-free and generic
  -- in `D0`) together with its agreement with `piecePush`, so the assembly datum
  -- `SourceBoundaryCoordAssemblyData` is instantiated below and the goal is now exactly the
  -- pointwise local-class comparison (with the single `ε`).
  obtain ⟨eBdry, heBdry⟩ :=
    Work.ThomBordism.levelBdryHomeoOf (k := k) (mU := G.mU) (m := m) (ι := ι)
      (Fam := Fam) (D0 := D0') (hWcl := hWclNew) (L := L)
  -- the canonical relative fundamental class: the one with the prescribed local classes `γ`
  -- (the orientation family produced by the coframing of the smoothed plane field, Step 11bis)
  haveI hManLvl : IsManifold (modelWithCornersEuclideanHalfSpace 9) ∞
      (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L) :=
    Work.PTGeometric.Lvl.Setup.instIsManifold
      (Work.PTGeometric.levelSetup {x : M | w x = 0} hWclNew L)
  haveI hManLvl1 : IsManifold (modelWithCornersEuclideanHalfSpace 9) 1
      (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L) :=
    IsManifold.of_le (n := ∞) (by simp)
  haveI hNeLvl : Nonempty (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L) :=
    ⟨⟨hWneNew.choose, hWneNew.choose_spec⟩⟩
  obtain ⟨hcolNew⟩ := hcollarNew
  obtain ⟨w₀, _hw₀fund, hw₀loc⟩ :=
    Work.ThomBordism.exists_relFundClass_of_collar_loc (n := 8) hcolNew γ hγ
  -- ==================================================================================
  -- **THE GEOMETRIC COMPARISON** -- the single remaining goal of the whole project.
  --
  -- **The sign is kept OPEN** (project lead, round 48): the polarity of the tube chart against the
  -- coframing family is *not* known to be `+1`, so we do not fix `ε = 1` while also committing to
  -- the specific class `w₀` (whose interior local classes are the coframing family `γ`).  The goal
  -- below is
  --
  --     `∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ x ∈ ∂W, locClass (hPairδ w₀) x = ε • locClass ῆ x`,
  --
  -- which is *equivalent* to `SourceBoundaryCoord D0'` (replace `w₀` by `ε • w₀` on the other
  -- side, using `Work.Orient.eq_of_locClass_eq`) and is the form the assembly datum
  -- `SourceBoundaryCoordAssemblyData` consumes: the polarity's **uniformity** is the content, its
  -- *value* is absorbed.
  --
  -- Everything the comparison needs is in scope and PROVED:
  --
  --  * `Work.ThomBordism.locClass_hPairDelta_eq_of_localClass_eq` (the boundary class is determined
  --    by the interior class at ONE point of a half-ball) together with `hw₀loc` (the interior
  --    classes of `w₀` are exactly `γ`);
  --  * `Work.ThomBordism.locClass_sourceBoundaryClass_piece` and
  --    `Work.ThomBordism.sourceBoundaryClass_localGenerator` (the local class of `ῆ`) and the
  --    partition `Work.ThomBordism.piecePush_isClopen_and_cover`;
  --  * the tube dictionary `hHendNewTube`; the coorientation identification `hΓ₂eqS0` (Step 11bis),
  --    i.e. `Γ₂ = G.gauss ∘ Hf` on the slab `S0` containing every piece; `GenuineTubeGeometry.tie`
  --    with `Work.ThomBordism.canonicalLift_plane` and
  --    `Work.ThomBordism.padGaussFunM_eq_of_normalData`; the uniform branch
  --    `Work.ThomBordism.gaussBranch_uniform` (from
  --    `Work.ThomBordism.localDegree_universalThomClass`); and TEL
  --    `Work.ThomBordism.sigmaTelescope_gauss`;
  --  * the ambient positivity (ORI-M) `Work.ThomBordism.sourceRegion_extChart_transition_det_pos`,
  --    and (`NOTE_OWNER_ORIENTATION3.md` (F1)) the region charts at the pieces are the ambient
  --    identity composed with a shear of determinant `+1`.
  --
  -- What remains are the two chart-level computations of `NOTE_S53_TUBE_DICT_AND_T1T2.md` §3:
  -- **(det)** the sign of the `Lvl` chart against the pin frame (the pins are
  -- `readCLM (G.emb i) (tiedND G i) j' w0 ∘ projEuc`, positively oriented by
  -- `Work.ThomBordism.orthFrameOrientation`) and **(kos)** the signed boundary-orientation (Koszul)
  -- formula.  Both are *uniform in the piece*: they are computed by the same recipe from the tube
  -- data of the piece, and TEL is the statement that closes the piece's `c`-oriented tangent frame
  -- with the `gframe` of the tube to the ambient orientation.  The two sign-blind bricks
  -- T1 (`Work.ThomBordism.boundarySign_chartLocal`, PROVED) and T2
  -- (`Work.ThomBordism.sourceBoundaryClass_localGenerator`, PROVED) then convert the pointwise
  -- identity into the single `ε` below.
  -- ==================================================================================
  -- **SESSION 64 (see `NOTE_SESSION64.md`) -- what exactly is left here, and what is NOT.**
  --
  -- The goal below is the *only* content.  Two simplifications are DEAD:
  --
  --  * `Work.ThomBordism.localBoundaryTransfer'` (the `stdHalfBall` form) cannot be used per piece:
  --    its `hw'`/`hψ'` pin the model classes to `stdIntOrient`/`stdFlatGen`, so its transport
  --    hypotheses fail by the per-piece factor `c₀ * FrameSigns.frameSign (Fam a) i y`.  The usable
  --    form is `Work.ThomBordism.localBoundaryTransfer_congr` (free model classes), whose `hPair'`
  --    is *content-free* (both sides are generators of a rank-one free ℤ-module and `w'`, `ψ'`, `c`
  --    are free): all content is the RATIO of the two transported classes.
  --  * the naive global `Phi` for that congruence form (convex blend `β • e z + (1-β) • e c` with
  --    `(e c)0 = 0`) is NOT injective at `x₀` -- on the ray through `e x₀` the scalar `β(s)s`
  --    re-crosses `‖e x₀ - e c‖`.  Any construction of `Phi` must avoid that.
  --
  -- The residual is therefore statement (4) of `NOTE_SESSION63.md` §3, i.e. (in the tube
  -- coordinates of a piece, with `τ` the piece's chart frame, `gframe` the Gauss normal frame,
  -- `s_a` the (uniform!) branch of `GenuineTubeGeometry.pulledThom_gauss` and
  -- `ε_a = FrameSigns.frameSign (Fam a) i y`):
  --
  --      (4)  or(W) = ± s_a ε_a • (e₀ ∧ τ)  -- equivalently  or(∂W) = ± s_a ε_a • τ ,
  --
  -- because then `ῆ = c₀ ε_a • (the boundary chart generator)` (PROVED:
  -- `Work.ThomBordism.locClass_sourceBoundaryClass_eq_chartTr`, brick 2) and the per-piece factor
  -- `ε_a` CANCELS, giving the uniform `ε = ± s_a / c₀` required below.  Every ingredient of (4) is
  -- PROVED and in scope: `hΓ₂eqS0` + `tie` + `canonicalLift_plane` + `padGaussFunM_eq_of_normalData`
  -- (the coorientation frame is `s_a • padIsomM ∘ gframe`), `gaussBranch_uniform` (the uniformity of
  -- `s_a`), TEL `Work.ThomBordism.sigmaTelescope_gauss` / `pairSign_tanFrame_gframe`
  -- (`or_spatial = flipTan ε_a τ ∧ gframe`), the ambient (det) input
  -- (`det_cubeEuc_cubeCoord_pos`, `sourceRegion_extChart_transition_det_pos`,
  -- `flatSourceHomotopy8_eq_collapse`), and the universal Koszul constant
  -- (`Work.ThomBordism.koszulComplementOrientation`, `modelOrientation`).  What (4) still needs is
  -- the *assembly* of those ingredients across the `Lvl`/`CofAtlas` charts -- see
  -- `NOTE_SESSION64.md` §6/§7; note that the `∃ ε` form is ESSENTIAL and is what makes the
  -- `CofAtlas.sigma` opacity harmless (it produces only a global flip).
  -- ==================================================================================
  -- **G1** (site glue of the lead's `LeadChapter/ASSEMBLY.md`): the local class of the pieces'
  -- boundary class `ῆ` at a boundary point of the `a`-th piece is the `RelHmapOf` of the piece's
  -- local fundamental class along the collapse identification `z ↦ eBdry.symm ⟨a,z⟩`.
  --
  -- Route: `sum_pushClass_eq_sourceBoundaryClass` (the two avatars of `ῆ` coincide),
  -- `relHmapOf_locClass_singleton` (naturality of the local class),
  -- `locClass_sourceBoundaryClass_piece` (the piece's localisation) and `RelHmapOf_comp` +
  -- `RelHmapOf_congr` (the composite of the piece push with the transfer homeomorphism is the
  -- collapse identification).  No geometry: pure functoriality of the local class.
  -- ==================================================================================
  have hG1 := Work.ThomBordism.locClass_sum_pushClass_eq_relHmapOf
    (k := k) (D := D) (ι := ι) (Fam := Fam) hk G m hm hpow D0' (hWcl := hWclNew) (L := L)
    eBdry heBdry

  -- ==================================================================================
  -- **G5** (site glue of the lead's `LeadChapter/ASSEMBLY.md`): the collapse identification `eBdry`
  -- of the level model with the pieces has the same ambient coordinates as the specified zero-set
  -- identification `hZero`.  Pure bookkeeping: `heBdry` + the definitions of `piecePush`,
  -- `hHendNew`, `hHend` and `hmidH`.
  -- ==================================================================================
  have hG5 : ∀ (a : Fin m × ι) (z : (Fam a.2).pt),
      (eBdry.symm ⟨a, z⟩ : ↥((modelWithCornersEuclideanHalfSpace 9).boundary (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L))).1.1.1 = (hZero.symm ⟨a, z⟩).1 := by
    intro a z
    have h1 : (eBdry.symm ⟨a, z⟩ : ↥((modelWithCornersEuclideanHalfSpace 9).boundary (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L))).1
        = ((piecePush D0' a z : ↥(sourceLevelBdry D0')) : ↥(sourceLevelSet D0')) := heBdry a z
    rw [h1]
    have h2 : (((piecePush D0' a z : ↥(sourceLevelBdry D0')) : ↥(sourceLevelSet D0'))).1
        = (hHendNew.symm ⟨a, z⟩ : ↥(Send ∩ {x : M | w x = 0})).1 := rfl
    rw [h2]
    have h3 : (hHendNew.symm ⟨a, z⟩ : ↥(Send ∩ {x : M | w x = 0})).1
        = (hmidH.symm (hZero.symm ⟨a, z⟩) :
            ↥{x : M | x.1.1 0 = 0 ∧ Hf x.1.1 ∈ G.core}).1 := by
      rw [show hHendNew = (Homeomorph.setCongr hHset).trans hHend from rfl]
      rw [show hHend = ((Homeomorph.setCongr hset1).trans hmidH).trans hZero from rfl]
      simp only [Homeomorph.symm_trans_apply]
      rfl
    rw [h3]
    have h4 : (hmidH.symm (hZero.symm ⟨a, z⟩) :
          ↥{x : M | x.1.1 0 = 0 ∧ Hf x.1.1 ∈ G.core}).1.1
        = (hZero.symm ⟨a, z⟩).1 := by
      have h5 : (hmidH (hmidH.symm (hZero.symm ⟨a, z⟩))).1
          = (hmidH.symm (hZero.symm ⟨a, z⟩) :
              ↥{x : M | x.1.1 0 = 0 ∧ Hf x.1.1 ∈ G.core}).1.1 := rfl
      have h6 : hmidH (hmidH.symm (hZero.symm ⟨a, z⟩)) = hZero.symm ⟨a, z⟩ :=
        Homeomorph.apply_symm_apply hmidH _
      rw [← h5, h6]
    exact h4
  -- ==================================================================================
  -- **G4 / G3 (site glue of `LeadChapter/ASSEMBLY.md`)**
  --
  -- At a collar point `x` of the level set (a point of `{w = 0}` in the collar slab, interior to the
  -- region) the region chart is the ambient identity (`hchartVal`), the perturbed field `w` agrees
  -- with the raw field `vSrc` (`hvSrc` + `hwS0`), and consequently:
  --  * `mfderiv w x = fderiv vSrc x.1.1` (`hG4deriv.1`), so with `hlinkW` + the tie `hΓ₂eqS0`
  --    + `range_ogFrameCLM`, the **Gauss plane lies in the range of the raw derivative** (`hG3`) —
  --    the hypothesis of `Work.ThomBordism.exists_comp_eq_of_range_le` producing the normal-frame
  --    datum `N` of S3 (`chapter_tubeDet`);
  --  * the chart reading `u ↦ w ((extChartAt x).symm u)` has derivative `fderiv vSrc x.1.1`
  --    (`hG4deriv.2.1`) — the `hLv` hypothesis of S1 (`chapter_K1det`) — and the raw field itself
  --    has derivative `mfderiv w x` (`hG4deriv.2.2`) — the `Lv` of S3.
  -- ==================================================================================
  have hvSrc : ∀ x : M, v x = Work.ThomBordism.LeadChapter.vSrc G m hpow x.1.1 := by
    intro x
    have hx : Work.ThomBordism.LeadChapter.srcHf G m hpow x.1.1 ≠ D.t₀ := hne' x
    have hv : v x = (G.coord ⟨Hf x.1.1, hne' x⟩).2 := rfl
    have hsub : (⟨Hf x.1.1, hne' x⟩ : {y : D.T // y ≠ D.t₀})
        = ⟨Work.ThomBordism.LeadChapter.srcHf G m hpow x.1.1, hx⟩ := Subtype.ext rfl
    rw [Work.ThomBordism.LeadChapter.vSrc, dif_neg hx, hv, hsub]
  have hchartVal : ∀ (x : M) (hx : x ∉ (𝓡∂ (8 + k + 1)).boundary M),
      ∀ p ∈ (extChartAt (𝓡∂ (8 + k + 1)) x).source,
        (extChartAt (𝓡∂ (8 + k + 1)) x) p = p.1.1 :=
    fun x hx => Work.ThomBordism.sourceRegionMk_extChartAt_apply_of_phi_neg G m hpow hphi hweak x
      (Work.PTGeometric.WeakRegion.RegionSetupWeak.phi_neg_of_not_mem_boundary S x hx)
  have hchartVal_symm : ∀ (x : M) (hx : x ∉ (𝓡∂ (8 + k + 1)).boundary M),
      ∀ u ∈ (extChartAt (𝓡∂ (8 + k + 1)) x).target,
        ((extChartAt (𝓡∂ (8 + k + 1)) x).symm u : M).1.1 = u :=
    fun x hx => Work.ThomBordism.sourceRegionMk_extChartAt_symm_val G m hpow hphi hweak x
      (Work.PTGeometric.WeakRegion.RegionSetupWeak.phi_neg_of_not_mem_boundary S x hx)
  have hpos0 : ∀ (x : M), x ∉ (𝓡∂ (8 + k + 1)).boundary M → 0 < x.1.1 0 := by
    intro x hx
    have h1 : x.1 ∉ (𝓡∂ (8 + k + 1)).boundary S.A := fun hmem =>
      hx ((S.mem_boundary_iff x).mpr (Or.inl hmem))
    have h2 : x.1.1 0 ≠ 0 := fun h0 =>
      h1 ((Work.PTGeometric.mem_boundary_halfSpace_iff ((8 + k) + 1)).mpr h0)
    exact lt_of_le_of_ne x.1.2 (Ne.symm h2)
  have hint : ∀ (x : M) (hx : x ∉ (𝓡∂ (8 + k + 1)).boundary M),
      (extChartAt (𝓡∂ (8 + k + 1)) x) x ∈ interior (range (𝓡∂ (8 + k + 1))) := by
    intro x hx
    rw [hchartVal x hx x (mem_extChartAt_source x),
      interior_range_modelWithCornersEuclideanHalfSpace ((8 + k) + 1)]
    exact hpos0 x hx
  have hG4ev : ∀ (x : M) (_hxε : x.1.1 0 < εcl) (hx : x ∉ (𝓡∂ (8 + k + 1)).boundary M),
      (fun u => w ((extChartAt (𝓡∂ (8 + k + 1)) x).symm u))
        =ᶠ[𝓝 ((extChartAt (𝓡∂ (8 + k + 1)) x) x)]
          Work.ThomBordism.LeadChapter.vSrc G m hpow := by
    intro x hxε hx
    have hvalx := hchartVal x hx
    have hpx : (extChartAt (𝓡∂ (8 + k + 1)) x) x = x.1.1 := hvalx x (mem_extChartAt_source x)
    have hsymm := hchartVal_symm x hx
    have hrange : range (𝓡∂ (8 + k + 1)) ∈ 𝓝 ((extChartAt (𝓡∂ (8 + k + 1)) x) x) :=
      mem_interior_iff_mem_nhds.mp (hint x hx)
    have hmem : (extChartAt (𝓡∂ (8 + k + 1)) x).target ∩ {u | u 0 < εcl}
        ∈ 𝓝 ((extChartAt (𝓡∂ (8 + k + 1)) x) x) := by
      have hlt : {u : Work.PTGeometric.Amb (8 + k + 1) | u 0 < εcl}
          ∈ 𝓝 ((extChartAt (𝓡∂ (8 + k + 1)) x) x) := by
        have hopen : IsOpen ({u : Work.PTGeometric.Amb (8 + k + 1) | u 0 < εcl}) :=
          isOpen_lt ((continuous_apply (0 : Fin ((8 + k) + 1))).comp
            (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin ((8 + k) + 1) => ℝ)).continuous)
            continuous_const
        exact hopen.mem_nhds (by rw [hpx]; exact hxε)
      have hs : (extChartAt (𝓡∂ (8 + k + 1)) x).target ∩ {u | u 0 < εcl}
          ∈ 𝓝[range (𝓡∂ (8 + k + 1))] ((extChartAt (𝓡∂ (8 + k + 1)) x) x) :=
        Filter.inter_mem (extChartAt_target_mem_nhdsWithin x)
          (mem_nhdsWithin_of_mem_nhds hlt)
      rwa [nhdsWithin_eq_nhds.mpr hrange] at hs
    refine Filter.eventuallyEq_of_mem hmem ?_
    intro u hu
    obtain ⟨hut, huε⟩ := hu
    have hc0 : ((extChartAt (𝓡∂ (8 + k + 1)) x).symm u : M).1.1 0 = u 0 := by
      rw [hsymm u hut]
    calc w ((extChartAt (𝓡∂ (8 + k + 1)) x).symm u)
        = v ((extChartAt (𝓡∂ (8 + k + 1)) x).symm u) :=
          hwS0 _ (by rw [hc0]; exact le_of_lt huε)
      _ = Work.ThomBordism.LeadChapter.vSrc G m hpow
            ((extChartAt (𝓡∂ (8 + k + 1)) x).symm u).1.1 := hvSrc _
      _ = Work.ThomBordism.LeadChapter.vSrc G m hpow u := by rw [hsymm u hut]
  have hG4deriv : ∀ (x : M) (hxε : x.1.1 0 < εcl) (hx : x ∉ (𝓡∂ (8 + k + 1)).boundary M),
      mfderiv (𝓡∂ (8 + k + 1)) (𝓘(ℝ, Work.PTGeometric.Amb (k + G.mU))) w x
          = fderiv ℝ (Work.ThomBordism.LeadChapter.vSrc G m hpow) x.1.1
      ∧ HasFDerivAt (fun u => w ((extChartAt (𝓡∂ (8 + k + 1)) x).symm u))
          (fderiv ℝ (Work.ThomBordism.LeadChapter.vSrc G m hpow) x.1.1) x.1.1
      ∧ HasFDerivAt (Work.ThomBordism.LeadChapter.vSrc G m hpow)
          (mfderiv (𝓡∂ (8 + k + 1)) (𝓘(ℝ, Work.PTGeometric.Amb (k + G.mU))) w x) x.1.1 := by
    intro x hxε hx
    have hwdiff : MDifferentiableAt (𝓡∂ (8 + k + 1))
        (𝓘(ℝ, Work.PTGeometric.Amb (k + G.mU))) w x := hwsm.mdifferentiableAt (by simp)
    have hev := hG4ev x hxε hx
    have hintx := hint x hx
    have h1 := Work.ThomBordism.mfderiv_eq_fderiv_of_eventuallyEq (𝓡∂ (8 + k + 1)) hwdiff hintx hev
    have h2 := Work.ThomBordism.hasFDerivAt_chartSymm_eq_fderiv (𝓡∂ (8 + k + 1)) hwdiff hintx hev
    have h3 := Work.ThomBordism.hasFDerivAt_of_chartSymm_eventuallyEq
      (𝓡∂ (8 + k + 1)) hwdiff hintx hev
    have hpx : (extChartAt (𝓡∂ (8 + k + 1)) x) x = x.1.1 :=
      hchartVal x hx x (mem_extChartAt_source x)
    rw [hpx] at h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hG3 : ∀ (x : M) (hxε : x.1.1 0 < εcl) (hx : x ∉ (𝓡∂ (8 + k + 1)).boundary M)
      (hxw : w x = 0),
      Set.range (Work.ThomBordism.LeadChapter.ogFrameCLM (G.gauss ⟨Hf x.1.1, hne' x⟩))
        ⊆ Set.range (fderiv ℝ (Work.ThomBordism.LeadChapter.vSrc G m hpow) x.1.1) := by
    intro x hxε hx hxw
    have hS0x : x ∈ S0 := hS0le x (le_of_lt hxε)
    have hgauss : G.gauss ⟨Hf x.1.1, hne' x⟩ = Γ₂ x := (hΓ₂eqS0 x hS0x).symm
    have h1 : Set.range (Work.ThomBordism.LeadChapter.ogFrameCLM (Γ₂ x))
        = Set.range (fderiv ℝ (Work.ThomBordism.LeadChapter.vSrc G m hpow) x.1.1) := by
      rw [Work.ThomBordism.range_ogFrameCLM]
      have h2 : {z : Work.PTGeometric.Amb (k + G.mU) |
            Work.ThomBordism.Grassmann.memPlane (Γ₂ x) z} = {z | P₁ x z = z} := by
        ext z
        rw [Set.mem_setOf_eq, Set.mem_setOf_eq, ← hΓ₂eq x,
          Work.PTGeometric.projOfPlane_fixed_iff]
      rw [h2, ← hlinkW x hxw, (hG4deriv x hxε hx).1]
      rfl
    rw [hgauss]
    exact h1.le
  -- **G3, packaged**: the normal-frame datum `N` of S3 (`chapter_tubeDet`) exists — the Gauss
  -- frame of the tube point factors through the derivative of the raw level function.
  have hN : ∀ (x : M) (hxε : x.1.1 0 < εcl) (hx : x ∉ (𝓡∂ (8 + k + 1)).boundary M)
      (hxw : w x = 0),
      ∃ N : EuclideanSpace ℝ (Fin k) →L[ℝ] Work.PTGeometric.Amb ((8 + k) + 1),
        (fderiv ℝ (Work.ThomBordism.LeadChapter.vSrc G m hpow) x.1.1).comp N
          = Work.ThomBordism.LeadChapter.ogFrameCLM (G.gauss ⟨Hf x.1.1, hne' x⟩) := by
    intro x hxε hx hxw
    exact Work.ThomBordism.exists_comp_eq_of_range_le _ _ (hG3 x hxε hx hxw)
  -- ==================================================================================
  -- **THE ASSEMBLY** (`LeadChapter/ASSEMBLY.md`; session 99)
  --
  -- S1, S2, S3 are proved and imported; the collar chart S4 (`chapter_collarChart`) is not yet
  -- importable, so its statement at the site's data is recorded below as `hS4` (a single `sorry`
  -- to be replaced by the instantiation of the chapter the moment it lands).  Everything else of
  -- the per-point argument below is written against these four statements.
  -- ==================================================================================
  have hk1 : 1 ≤ k := by omega
  obtain ⟨ε₁, hε₁, hS1⟩ := Work.ThomBordism.LeadChapter.chapter_K1det k (k + G.mU)
  obtain ⟨c₂, hc₂, hS2⟩ := Work.ThomBordism.LeadChapter.chapter_bdryTransfer 8 (by norm_num)
  obtain ⟨ε₃, hε₃, hS3⟩ :=
    Work.ThomBordism.LeadChapter.chapter_tubeDet (k := k) hk1 (D := D) (ι := ι) (Fam := Fam)
      G m hpow hZero hZeroSpec
  -- **S4** (`chapter_collarChartFix`), instantiated at the site's data.
  have hS4 : ∀ (a : Fin m × ι) (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)),
      ∃ (δ : ℝ) (ψ : OpenPartialHomeomorph
            (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L) (EuclideanHalfSpace 9))
          (κ : OpenPartialHomeomorph
            (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L) Work.ThomBordism.CofAtlas.E9)
          (g : OpenPartialHomeomorph
            ↥((modelWithCornersEuclideanHalfSpace 9).boundary
              (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L))
            (EuclideanSpace ℝ (Fin 8))),
        0 < δ ∧
        ψ.target = {z : EuclideanHalfSpace 9 | z.1 0 < δ ∧
          tail 8 z.1 ∈ (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.target} ∧
        (∀ z ∈ ψ.target,
          (ψ.symm z).1.1.1 = Work.ThomBordism.LeadChapter.collarPiece G m hpow hZero a i z.1) ∧
        (∀ q ∈ ψ.source,
          q ∈ (modelWithCornersEuclideanHalfSpace 9).boundary
            (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L) ↔ (ψ q).1 0 = 0) ∧
        κ.source = ψ.source ∩ {q | 0 < (ψ q).1 0} ∧
        (∀ q ∈ κ.source, κ q = (ψ q).1) ∧
        (∀ q : ↥((modelWithCornersEuclideanHalfSpace 9).boundary
              (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L)),
            q ∈ g.source ↔ (q : Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L)
              ∈ ψ.source) ∧
        (∀ q ∈ g.source, g q = tail 8 (ψ q).1) ∧
        (∀ (q : ↥((modelWithCornersEuclideanHalfSpace 9).boundary
              (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L)))
            (z : (Fam a.2).pt),
          z ∈ Work.ThomBordism.FrameSigns.src (Fam a.2) i →
          q.1.1.1.1 = ((hZero.symm ⟨a, z⟩).1).1 →
          q ∈ g.source ∧ g q = (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 z) := by
    intro a i
    obtain ⟨δ, ψ, κ, g, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
      Work.ThomBordism.LeadChapter.chapter_collarChartFix (k := k) (D := D) (ι := ι) (Fam := Fam)
        G m hpow hphi hweak hZero hZeroSpec w εcl hεcl_pos
        (fun x hx => (hwS0 x hx).trans (hvSrc x)) hWclNew L a i
    exact ⟨δ, ψ, κ, g, h1, h2, h3, h4, h5, h6, (fun q => by rw [h7, Set.mem_preimage]), h8, h9⟩
  have hsign : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ∀ x : ↥((modelWithCornersEuclideanHalfSpace 9).boundary
          (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L)),
        Work.Orient.locClass (TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary
            (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L))) 8
          ((Work.Cohomology.hPairδ (TopCat.of (Work.PTGeometric.levelModel
              {x : M | w x = 0} hWclNew L))
            ((modelWithCornersEuclideanHalfSpace 9).boundary
              (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L)) 8).hom w₀) x
        = ε • Work.Orient.locClass (TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary
              (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L))) 8
            (∑ i : Fin m × ι,
              Work.ThomBordism.Transversality.OrientBridge.pushClass
                (Fam := fun a : Fin m × ι => Fam a.2) eBdry.symm i) x := by
    -- the brick-2 constant and the chapter constant `ε₃ : ℝ` as an integer
    obtain ⟨c₀, hc₀, hB2⟩ := Work.ThomBordism.relHmapOf_locClass_eq_chartTr
    refine ⟨ε₁ * (if ε₃ = 1 then (1 : ℤ) else -1) * c₂ * c₀, ?_, ?_⟩
    · rcases hε₁ with h | h <;> rcases hε₃ with h3 | h3 <;> rcases hc₂ with h2 | h2 <;>
        rcases hc₀ with h0 | h0 <;> rw [h, h3, h2, h0] <;> norm_num
    · intro x
      obtain ⟨⟨a, y⟩, hyx⟩ : ∃ p : (Σ a : Fin m × ι, (Fam a.2).pt), eBdry.symm p = x :=
        ⟨eBdry x, eBdry.symm_apply_apply x⟩
      subst hyx
      -- the boundary point of the level set (the elimination of `x` by `subst` has replaced it,
      -- so we name the substituted term)
      set xb : ↥((modelWithCornersEuclideanHalfSpace 9).boundary
          (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L)) := eBdry.symm ⟨a, y⟩ with hxbdef
      obtain ⟨i, hyi⟩ :=
        Work.Thom.chartCover_spec (H := Work.ThomBordism.PontryaginThom.Euc 8)
          (M := (Fam a.2).pt) y
      -- **S4**, the collar chart at the piece `a` and the chart `i`
      obtain ⟨δ, ψ, κ, g, hδpos, hψtgt, hψpin, hψbd, hκsrc, hκval, hgsrc, hgval, hglast⟩ :=
        hS4 a i
      -- **the collar chart at the boundary point `x`**: the pin in ambient coordinates, the
      -- membership of `x` in the chart source, and the openness radius of the chart target at
      -- `ψ x` (all stated before the collar parameter is chosen, since `hx₀ ∈ ψ.source` must hold
      -- within that radius)
      have hG5' : ∀ (a' : Fin m × ι) (z : (Fam a'.2).pt),
          (eBdry.symm ⟨a', z⟩ : ↥((modelWithCornersEuclideanHalfSpace 9).boundary
            (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L))).1.1.1.1
          = ((hZero.symm ⟨a', z⟩).1).1 :=
        fun a' z => congrArg (fun u : EuclideanHalfSpace ((8 + k) + 1) => u.1) (hG5 a' z)
      have hxgl : xb ∈ g.source := (hglast xb y hyi (hG5' a y)).1
      have hxg : g xb = (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y :=
        (hglast xb y hyi (hG5' a y)).2
      have hxψ : (xb : Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L) ∈ ψ.source :=
        (hgsrc xb).mp hxgl
      have hψx0 : (ψ xb).1 0 = 0 := (hψbd xb hxψ).mp xb.2
      have htailx : tail 8 (ψ xb).1 = (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y := by
        rw [← hgval xb hxgl, hxg]
      have hnhds : {w : EuclideanSpace ℝ (Fin 9) | w 0 < δ ∧ tail 8 w ∈
          (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.target} ∈ 𝓝 ((ψ xb).1) := by
        refine Filter.inter_mem ?_ ?_
        · have hcont : Continuous (fun w : EuclideanSpace ℝ (Fin 9) => w 0) :=
            (continuous_apply 0).comp
              (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 9 => ℝ)).continuous
          exact (hcont.isOpen_preimage _ isOpen_Iio).mem_nhds (by
            show (ψ xb).1 0 < δ
            rw [hψx0]
            exact hδpos)
        · have hc2 : Continuous (fun w : EuclideanSpace ℝ (Fin 9) => tail 8 w) :=
            Work.PTGeometric.continuous_tail 8
          exact (hc2.isOpen_preimage _
            (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.open_target).mem_nhds (by
              show tail 8 (ψ xb).1 ∈
                (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.target
              rw [htailx]
              exact (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.map_source hyi)
      obtain ⟨ρ, hρpos, hρball⟩ := Metric.mem_nhds_iff.mp hnhds
      -- **S3**, the tube determinant, at `(a, i, y)`
      obtain ⟨δ', hδ'pos, hS3z⟩ := hS3 a i y hyi
      -- the collar parameter (also small enough that `ψ x₀` lies within `ρ / 2` of `ψ x`)
      obtain ⟨t, ht0, htd, htd', hte, htq, htρ⟩ :
          ∃ t : ℝ, 0 < t ∧ t < δ ∧ t < δ' ∧ t < εcl ∧ t ≤ 1 / 4 ∧ t < ρ / 2 := by
        have hS : 0 < min (min (min δ δ') (min εcl (1 / 4))) (ρ / 2) :=
          lt_min (lt_min (lt_min hδpos hδ'pos) (lt_min hεcl_pos (by norm_num))) (by linarith)
        have hlt : min (min (min δ δ') (min εcl (1 / 4))) (ρ / 2) / 2
            < min (min (min δ δ') (min εcl (1 / 4))) (ρ / 2) := by linarith
        refine ⟨min (min (min δ δ') (min εcl (1 / 4))) (ρ / 2) / 2, by linarith, ?_, ?_, ?_, ?_, ?_⟩
        · exact lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le hlt (min_le_left _ _))
            (min_le_left _ _)) (min_le_left _ _)
        · exact lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le hlt (min_le_left _ _))
            (min_le_left _ _)) (min_le_right _ _)
        · exact lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le hlt (min_le_left _ _))
            (min_le_right _ _)) (min_le_left _ _)
        · exact le_of_lt (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le hlt
            (min_le_left _ _)) (min_le_right _ _)) (min_le_right _ _))
        · exact lt_of_lt_of_le hlt (min_le_right _ _)
      -- the collar point of the tube chart
      set z : Work.ThomBordism.CofAtlas.E9 :=
        Work.ThomBordism.LeadChapter.euCons t
          ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y) with hzdef
      have hz0 : z 0 = t := by
        rw [hzdef]; exact Work.ThomBordism.LeadChapter.euCons_zero t _
      have hztail : tail 8 z = (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y := by
        rw [hzdef]; exact Work.ThomBordism.LeadChapter.tail_euCons t _
      have hz0nn : 0 ≤ z 0 := (hz0 ▸ ht0).le
      have hzmem : (⟨z, hz0nn⟩ : EuclideanHalfSpace 9) ∈ ψ.target := by
        rw [hψtgt]
        exact ⟨(hz0 ▸ htd), by rw [hztail]; exact (Work.ThomBordism.FrameSigns.chartOf
          (Fam a.2) i).1.map_source hyi⟩
      -- the interior point of the level set at the piece
      set x₀ := ψ.symm ⟨z, hz0nn⟩ with hx0def
      have hψx₀ : ψ x₀ = ⟨z, hz0nn⟩ := ψ.right_inv hzmem
      have hx₀src : x₀ ∈ ψ.source := ψ.map_target hzmem
      have hx₀pin : x₀.1.1.1
          = Work.ThomBordism.LeadChapter.collarPiece G m hpow hZero a i z := by
        simpa [hx0def] using hψpin ⟨z, hz0nn⟩ hzmem
      have hx₀κ : x₀ ∈ κ.source := by
        rw [hκsrc]
        exact ⟨hx₀src, by simpa [hψx₀, hz0] using ht0⟩
      have hκx₀ : κ x₀ = z := by
        rw [hκval x₀ hx₀κ, hψx₀]
      have hx₀int : x₀ ∉ (modelWithCornersEuclideanHalfSpace 9).boundary
          (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L) := by
        intro hb
        have h1 := (hψbd x₀ hx₀src).mp hb
        exact absurd (by simpa [hψx₀, hz0] using h1) (ne_of_gt ht0)
      -- the ambient coordinate of `x₀`
      have hx₀coord : x₀.1.1.1 0 = t := by
        rw [hx₀pin, Work.ThomBordism.LeadChapter.collarPiece]
        rw [Work.PTGeometric.consVec_apply_zero, Work.PTGeometric.tailVec_apply_zero, add_zero,
          hz0]
      have hx₀ε : x₀.1.1.1 0 < εcl := by rw [hx₀coord]; exact hte
      have hx₀w : w x₀.1 = 0 :=
        Set.mem_setOf_eq.mp
          (Work.ThomBordism.levelModel_coe_mem {x : M | w x = 0} hWclNew L x₀)
      have hx₀bdM : x₀.1 ∉ (𝓡∂ (8 + k + 1)).boundary M := by
        intro hbM
        have hbLvl : x₀ ∈ (modelWithCornersEuclideanHalfSpace 9).boundary
            (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L) :=
          (Work.PTGeometric.Lvl.Setup.mem_boundary_iff
            (Work.PTGeometric.levelSetup {x : M | w x = 0} hWclNew L) x₀).mpr hbM
        exact hx₀int hbLvl
      -- the integer frame sign of the piece chart
      set fz : ℤ := if 0 < Work.ThomBordism.FrameSigns.pairVal (Fam a.2) i y hyi then (1 : ℤ)
        else -1 with hfzdef
      have hfz : fz = 1 ∨ fz = -1 := by
        rw [hfzdef]; split_ifs <;> [exact Or.inl rfl; exact Or.inr rfl]
      have hfs : Work.ThomBordism.FrameSigns.frameSign (Fam a.2) i y = (fz : ℝ) := by
        rw [Work.ThomBordism.FrameSigns.frameSign_of_mem (Fam a.2) i y hyi, hfzdef]
        split_ifs <;> norm_num
      -- **S3**: the tube determinant at the collar point `z`
      obtain ⟨B, hBd, hne, hS3sign⟩ := hS3z z (by rw [hz0]; exact ht0)
        (by rw [hz0]; exact htd') (by rw [hztail])
      have hcollar : Work.ThomBordism.LeadChapter.collarPiece G m hpow hZero a i z = x₀.1.1.1 :=
        hx₀pin.symm
      -- the Gauss argument of S3, against the site's `G.gauss ∘ Hf`
      have hHfeq : ∀ u : EuclideanSpace ℝ (Fin ((8 + k) + 1)),
          Hf u = Work.ThomBordism.LeadChapter.srcHf G m hpow u := fun u => rfl
      have hcollar' : (⟨Hf x₀.1.1.1, hne' x₀.1⟩ : {y : D.T // y ≠ D.t₀})
          = ⟨Work.ThomBordism.LeadChapter.srcHf G m hpow
              (Work.ThomBordism.LeadChapter.collarPiece G m hpow hZero a i z), hne⟩ := by
        apply Subtype.ext
        show Hf x₀.1.1.1 = Work.ThomBordism.LeadChapter.srcHf G m hpow
          (Work.ThomBordism.LeadChapter.collarPiece G m hpow hZero a i z)
        rw [hcollar, hHfeq]
      have hgauss : G.gauss ⟨Hf x₀.1.1.1, hne' x₀.1⟩
          = G.gauss ⟨Work.ThomBordism.LeadChapter.srcHf G m hpow
              (Work.ThomBordism.LeadChapter.collarPiece G m hpow hZero a i z), hne⟩ :=
        congrArg G.gauss hcollar'
      -- **G4** at `x₀` and the normal frame `N` of **G3**
      have hG4 := hG4deriv x₀.1 hx₀ε hx₀bdM
      obtain ⟨N, hNcomp⟩ := hN x₀.1 hx₀ε hx₀bdM hx₀w
      have hLvS3 : HasFDerivAt (Work.ThomBordism.LeadChapter.vSrc G m hpow)
          (fderiv ℝ (Work.ThomBordism.LeadChapter.vSrc G m hpow) x₀.1.1.1)
          (Work.ThomBordism.LeadChapter.collarPiece G m hpow hZero a i z) := by
        rw [hcollar]
        exact hG4.2.2.congr_fderiv hG4.1
      have hcompS3 : (fderiv ℝ (Work.ThomBordism.LeadChapter.vSrc G m hpow) x₀.1.1.1).comp N
          = Work.ThomBordism.LeadChapter.ogFrameCLM
              (G.gauss ⟨Work.ThomBordism.LeadChapter.srcHf G m hpow
                (Work.ThomBordism.LeadChapter.collarPiece G m hpow hZero a i z), hne⟩) := by
        rw [← hgauss]
        exact hNcomp
      have hS3pos := hS3sign _ hLvS3 N hcompS3
      -- the sign of the block determinant
      have hsgnB : Work.ThomBordism.LeadChapter.sgnZ
            (Work.ThomBordism.LeadChapter.blockDet k B N)
          = (if ε₃ = 1 then (1 : ℤ) else -1) * fz := by
        have hpos := hS3pos
        rw [hfs] at hpos
        rcases hε₃ with h3 | h3 <;> rcases hfz with hf | hf
        · have hbd : 0 < Work.ThomBordism.LeadChapter.blockDet k B N := by
            simpa [h3, hf] using hpos
          rw [Work.ThomBordism.LeadChapter.sgnZ, if_pos hbd]
          simp [h3, hf]
        · have hbd : Work.ThomBordism.LeadChapter.blockDet k B N < 0 := by
            have h1 : ε₃ * (fz : ℝ) * Work.ThomBordism.LeadChapter.blockDet k B N
                = - Work.ThomBordism.LeadChapter.blockDet k B N := by
              rw [h3, hf]; norm_num
            rw [h1] at hpos; linarith
          rw [Work.ThomBordism.LeadChapter.sgnZ, if_neg (not_lt.mpr hbd.le), h3, hf]
          norm_num
        · have hbd : Work.ThomBordism.LeadChapter.blockDet k B N < 0 := by
            have h1 : ε₃ * (fz : ℝ) * Work.ThomBordism.LeadChapter.blockDet k B N
                = - Work.ThomBordism.LeadChapter.blockDet k B N := by
              rw [h3, hf]; norm_num
            rw [h1] at hpos; linarith
          rw [Work.ThomBordism.LeadChapter.sgnZ, if_neg (not_lt.mpr hbd.le), h3, hf]
          norm_num
        · have hbd : 0 < Work.ThomBordism.LeadChapter.blockDet k B N := by
            simpa [h3, hf] using hpos
          rw [Work.ThomBordism.LeadChapter.sgnZ, if_pos hbd, h3, hf]
          norm_num
      -- **G2**: the coframing reading is positively oriented
      obtain ⟨j, hj⟩ := hcfUcov x₀.1 hx₀w
      obtain ⟨iG, hUG, hℓG, _⟩ := _hcfname j
      have hG2 : 0 < LinearMap.det (((cfℓ j).comp
          (Work.ThomBordism.LeadChapter.ogFrameCLM (Γ₂ x₀.1))).toLinearMap) := by
        rw [hℓG]
        exact Work.ThomBordism.det_ellOf_ogFrameCLM_pos
          (Γ := Γ₂) (i := iG) (y := x₀.1) (hUG ▸ hj)
      -- `Lv ∘ N = ogFrameCLM (Γ₂ x₀.1)` against the site's coorientation `Γ₂`
      have hΓ₂x₀ : Γ₂ x₀.1 = G.gauss ⟨Hf x₀.1.1.1, hne' x₀.1⟩ :=
        hΓ₂eqS0 x₀.1 (hS0le x₀.1 (le_of_lt hx₀ε))
      have hcompG2 : (fderiv ℝ (Work.ThomBordism.LeadChapter.vSrc G m hpow) x₀.1.1.1).comp N
          = Work.ThomBordism.LeadChapter.ogFrameCLM (Γ₂ x₀.1) := by
        rw [hcompS3, ← hgauss, hΓ₂x₀]
      have hdetpos : 0 < LinearMap.det (((cfℓ j).comp
          ((fderiv ℝ (Work.ThomBordism.LeadChapter.vSrc G m hpow) x₀.1.1.1).comp N)).toLinearMap) := by
        rw [hcompG2]
        exact hG2
      have hsgnD : Work.ThomBordism.LeadChapter.sgnZ (LinearMap.det (((cfℓ j).comp
            ((fderiv ℝ (Work.ThomBordism.LeadChapter.vSrc G m hpow) x₀.1.1.1).comp N)).toLinearMap))
          = 1 := by
        rw [Work.ThomBordism.LeadChapter.sgnZ, if_pos hdetpos]
      -- **S1** at `x₀`: the coframing orientation of the level set, read in the collar chart.
      -- The hypothesis `hA` (the derivative of the chart reading of `κ.symm` in the ambient chart at
      -- `x₀`, which is the identity there) is supplied below from the pin; `Lv`/`N` are the ones of
      -- S3/G3, so that `sgnZ (det (cfℓ j ∘ Lv ∘ N)) = 1` (G2, `hsgnD`).
      have hS1x := hS1 (M := M) (D := Dcf) (x := x₀)
      -- **the pin, eventually** (PROVED): on `κ.target` the collar chart inverts to `collarPiece`
      have hHev : (fun u : Work.ThomBordism.CofAtlas.E9 => (κ.symm u).1.1.1)
          =ᶠ[𝓝 (κ x₀)]
            (fun u => Work.ThomBordism.LeadChapter.collarPiece G m hpow hZero a i u) := by
        filter_upwards [κ.open_target.mem_nhds (κ.map_source hx₀κ)] with u hu
        have hq : κ.symm u ∈ κ.source := κ.map_target hu
        have hqψ : κ.symm u ∈ ψ.source := (hκsrc ▸ hq).1
        have hqκ : κ (κ.symm u) = (ψ (κ.symm u)).1 := hκval (κ.symm u) hq
        have hψ1 : (ψ (κ.symm u)).1 = u := by
          rw [← hqκ]; exact κ.right_inv hu
        have h1 := hψpin (ψ (κ.symm u)) (ψ.map_source hqψ)
        rw [ψ.left_inv hqψ, hψ1] at h1
        exact h1
      have hApin : HasFDerivAt (fun u : Work.ThomBordism.CofAtlas.E9 => (κ.symm u).1.1.1)
          B (κ x₀) := by
        have hBd' : HasFDerivAt (Work.ThomBordism.LeadChapter.collarPiece G m hpow hZero a i)
            B (κ x₀) := by rw [hκx₀]; exact hBd
        exact hBd'.congr_of_eventuallyEq hHev
      have hS1res := hS1x hx₀int κ hx₀κ B (by
          -- **S1's `hA`**: the chart reading of the level set, in the ambient chart at `x₀`
          -- (which is the identity there), has derivative `B`.  We compare with `hApin`; the
          -- pointwise identification is made with `rw` (never by rebuilding the coerced term).
          refine hApin.congr_of_eventuallyEq ?_
          -- the two ingredients: the pin (`hHev`, PROVED) and the eventual membership of the
          -- point in the chart source, stated with the **subtype literal**
          have hsrc : (∀ᶠ u in 𝓝 (κ x₀), (⟨(κ.symm u).1.1, (κ.symm u).1.2⟩ : M) ∈
              (extChartAt (𝓡∂ (8 + k + 1)) x₀.1).source) := by
            haveI : IsManifold (𝓡∂ (8 + k + 1)) 1 M := IsManifold.of_le (n := ∞) (by simp)
            have hopen : IsOpen ((extChartAt (𝓡∂ (8 + k + 1)) x₀.1).source : Set M) :=
              isOpen_extChartAt_source (I := 𝓡∂ (8 + k + 1)) x₀.1
            have hmem : (⟨(κ.symm (κ x₀)).1.1, (κ.symm (κ x₀)).1.2⟩ : M) ∈
                (extChartAt (𝓡∂ (8 + k + 1)) x₀.1).source := by
              rw [κ.left_inv hx₀κ]
              exact mem_extChartAt_source (I := 𝓡∂ (8 + k + 1)) x₀.1
            have h0 : ContinuousAt (fun u : Work.ThomBordism.CofAtlas.E9 => κ.symm u) (κ x₀) :=
              (κ.continuousOn_invFun.continuousWithinAt (κ.map_source hx₀κ)).continuousAt
                (κ.open_target.mem_nhds (κ.map_source hx₀κ))
            have h1 : ContinuousAt (fun u : Work.ThomBordism.CofAtlas.E9 => (κ.symm u).1) (κ x₀) :=
              continuous_subtype_val.continuousAt.comp h0
            exact h1.preimage_mem_nhds (hopen.mem_nhds hmem)
          filter_upwards [hHev, hsrc] with u _hpin hu
          rw [hchartVal x₀.1 hx₀bdM ⟨(κ.symm u).1.1, (κ.symm u).1.2⟩ hu])
        (fderiv ℝ (Work.ThomBordism.LeadChapter.vSrc G m hpow) x₀.1.1.1) (by
          have hDcfv : Dcf.v = w := rfl
          rw [hDcfv, hchartVal x₀.1 hx₀bdM x₀.1 (mem_extChartAt_source (I := 𝓡∂ (8 + k + 1)) x₀.1)]
          exact hG4.2.1)
        j hj N (by
          intro h0
          rw [h0, mul_zero] at hS3pos
          exact absurd hS3pos (lt_irrefl 0))
      -- the interior local class of `w₀` at `x₀`
      have hInt : (HomologicalComplex.homologyMap
            (Work.Orient.relPunct (TopCat.of (Work.PTGeometric.levelModel {x : M | w x = 0}
                hWclNew L)) ((modelWithCornersEuclideanHalfSpace 9).boundary
                (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L))
              x₀ hx₀int) 9).hom w₀
          = (ε₁ * (if ε₃ = 1 then (1 : ℤ) else -1) * fz) •
            Work.PTGeometric.HOF.chartTr (W := TopCat.of (Work.PTGeometric.levelModel
                {x : M | w x = 0} hWclNew L)) κ x₀ hx₀κ
              (Work.PTGeometric.HOF.eucFam 9 (by norm_num) (κ x₀)) := by
        rw [hw₀loc x₀ hx₀int, hγval x₀ hx₀int, hS1res, hsgnB, hsgnD, mul_one]
        exact congrArg (fun c : ℤ => c • Work.PTGeometric.HOF.chartTr
          (W := TopCat.of (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L))
          κ x₀ hx₀κ (Work.PTGeometric.HOF.eucFam 9 (by norm_num) (κ x₀))) (by ring)
      -- ================= the sign of the interior class of `w₀` =================
      set ssign : ℤ := ε₁ * (if ε₃ = 1 then (1 : ℤ) else -1) * fz with hssdef
      have hs1 : ssign = 1 ∨ ssign = -1 := by
        rw [hssdef]
        rcases hε₁ with h1 | h1 <;> rcases hε₃ with h3 | h3 <;> rcases hfz with hf | hf <;>
          rw [h1, h3, hf] <;> norm_num
      have hc0sq : c₀ * c₀ = 1 := by rcases hc₀ with h | h <;> rw [h] <;> norm_num
      have hIntS : (HomologicalComplex.homologyMap
            (Work.Orient.relPunct (TopCat.of (Work.PTGeometric.levelModel {x : M | w x = 0}
                hWclNew L)) ((modelWithCornersEuclideanHalfSpace 9).boundary
                (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L))
              x₀ hx₀int) 9).hom w₀
          = ssign • Work.PTGeometric.HOF.chartTr (W := TopCat.of (Work.PTGeometric.levelModel
                {x : M | w x = 0} hWclNew L)) κ x₀ hx₀κ
              (Work.PTGeometric.HOF.eucFam 9 (by norm_num) (κ x₀)) := by
        rw [hInt, hssdef]
      have hInt' : (HomologicalComplex.homologyMap
            (Work.Orient.relPunct (TopCat.of (Work.PTGeometric.levelModel {x : M | w x = 0}
                hWclNew L)) ((modelWithCornersEuclideanHalfSpace 9).boundary
                (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L))
              x₀ hx₀int) 9).hom (ssign • w₀)
          = Work.PTGeometric.HOF.chartTr (W := TopCat.of (Work.PTGeometric.levelModel
                {x : M | w x = 0} hWclNew L)) κ x₀ hx₀κ
              (Work.PTGeometric.HOF.eucFam 9 (by norm_num) (κ x₀)) := by
        rw [map_zsmul, hIntS]
        rcases hs1 with h | h <;> rw [h] <;> simp
      -- ================= the distance of the collar point `x₀` from `xb` =================
      have hdist : dist (ψ x₀).1 (ψ xb).1 = t := by
        have hzval : (ψ x₀).1
            = Work.ThomBordism.LeadChapter.euCons t
              ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y) := by
          rw [hψx₀]
        have hxval : (ψ xb).1
            = Work.ThomBordism.LeadChapter.euCons 0
              ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y) := by
          conv_lhs => rw [← Work.ThomBordism.LeadChapter.euCons_tail_self ((ψ xb).1)]
          rw [htailx, hψx0]
        have hk1 : ∀ (s : ℝ) (v : EuclideanSpace ℝ (Fin 8)) (k : Fin 8),
            (Work.ThomBordism.LeadChapter.euCons s v) k.succ = v k := by
          intro s v k
          rw [← Work.PTGeometric.tail_apply 8 (Work.ThomBordism.LeadChapter.euCons s v) k,
            Work.ThomBordism.LeadChapter.tail_euCons]
        have hn0 : ‖(Work.ThomBordism.LeadChapter.euCons t
              ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y)
              - Work.ThomBordism.LeadChapter.euCons 0
                ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y)) 0‖ ^ 2 = t ^ 2 := by
          rw [PiLp.sub_apply, Work.ThomBordism.LeadChapter.euCons_zero,
            Work.ThomBordism.LeadChapter.euCons_zero, sub_zero, Real.norm_eq_abs,
            abs_of_pos ht0]
        have hnz : (∑ k : Fin 8, ‖(Work.ThomBordism.LeadChapter.euCons t
              ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y)
              - Work.ThomBordism.LeadChapter.euCons 0
                ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y)) k.succ‖ ^ 2) = 0 :=
          Finset.sum_eq_zero (fun k _ => by
            rw [PiLp.sub_apply, hk1, hk1, sub_self]
            simp)
        have hnorm : ‖Work.ThomBordism.LeadChapter.euCons t
              ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y)
              - Work.ThomBordism.LeadChapter.euCons 0
                ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y)‖ = t := by
          rw [EuclideanSpace.norm_eq, Fin.sum_univ_succ, hn0, hnz, add_zero,
            Real.sqrt_sq (le_of_lt ht0)]
        rw [dist_eq_norm, hzval, hxval, hnorm]
      -- ================= the boundary sign (S2) =================
      have hballS2 : ∀ z : EuclideanHalfSpace 9, dist z.1 (ψ xb).1 ≤ ρ / 2 → z ∈ ψ.target := by
        intro z hz
        have hmem : z.1 ∈ Metric.ball ((ψ xb).1) ρ := by
          rw [Metric.mem_ball]
          linarith
        obtain ⟨hz0, hzt⟩ := hρball hmem
        rw [hψtgt]
        exact ⟨hz0, hzt⟩
      have hS2res : Work.Orient.locClass (TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary
            (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L))) 8
          ((Work.Cohomology.hPairδ (TopCat.of (Work.PTGeometric.levelModel {x : M | w x = 0}
            hWclNew L)) ((modelWithCornersEuclideanHalfSpace 9).boundary
            (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L)) 8).hom (ssign • w₀)) xb
          = c₂ • Work.PTGeometric.HOF.chartTr (W := TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary
              (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L))) g xb hxgl
              (Work.PTGeometric.HOF.eucFam 8 (by norm_num) (g xb)) :=
        hS2 (W := TopCat.of (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L))
          (ψ := ψ) (hbd := hψbd) (y := xb) (hy := xb.2) (hyψ := hxψ)
          (r := ρ / 2) (hr := by linarith) (hball := hballS2)
          (x₀ := x₀) (hx₀ψ := hx₀src) (hx₀r := by rw [hdist]; exact htρ) (hx₀int := hx₀int)
          (κ := κ) (hx₀κ := hx₀κ)
          (hκ := fun q hq => ⟨by rw [hκsrc] at hq; exact hq.1, hκval q hq⟩)
          (g := g) (hyg := hxgl) (hg := fun q hq => ⟨(hgsrc q).mp hq, hgval q hq⟩)
          (w := ssign • w₀) (hw := hInt')
      have hzsmul : Work.Orient.locClass (TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary
            (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L))) 8
          ((Work.Cohomology.hPairδ (TopCat.of (Work.PTGeometric.levelModel {x : M | w x = 0}
            hWclNew L)) ((modelWithCornersEuclideanHalfSpace 9).boundary
            (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L)) 8).hom (ssign • w₀)) xb
          = ssign • Work.Orient.locClass (TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary
              (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L))) 8
              ((Work.Cohomology.hPairδ (TopCat.of (Work.PTGeometric.levelModel
                {x : M | w x = 0} hWclNew L)) ((modelWithCornersEuclideanHalfSpace 9).boundary
                (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L)) 8).hom w₀) xb := by
        rw [map_zsmul, Work.Orient.locClass_zsmul]
      have hb1 : Work.Orient.locClass (TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary
            (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L))) 8
          ((Work.Cohomology.hPairδ (TopCat.of (Work.PTGeometric.levelModel {x : M | w x = 0}
            hWclNew L)) ((modelWithCornersEuclideanHalfSpace 9).boundary
            (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L)) 8).hom w₀) xb
          = (ssign * c₂) • Work.PTGeometric.HOF.chartTr (W := TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary
              (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L))) g xb hxgl
              (Work.PTGeometric.HOF.eucFam 8 (by norm_num) (g xb)) := by
        have h := hS2res
        rw [hzsmul] at h
        have h2 := congrArg (fun t => ssign • t) h
        rcases hs1 with hh | hh
        · rw [hh] at h2 ⊢
          simpa using h2
        · rw [hh] at h2 ⊢
          simpa using h2
      -- ================= the pieces' class (G1 + brick 2) =================
      have hgs : ∀ z, z ∈ (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.source →
          eBdry.symm ⟨a, z⟩ ∈ g.source := fun z hz =>
        (hglast (eBdry.symm ⟨a, z⟩) z hz (hG5' a z)).1
      have hgc : ∀ z, z ∈ (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.source →
          g (eBdry.symm ⟨a, z⟩) = (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 z :=
        fun z hz => (hglast (eBdry.symm ⟨a, z⟩) z hz (hG5' a z)).2
      set hFs : C((Fam a.2).pt, TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary
          (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L))) :=
        ⟨fun z => eBdry.symm ⟨a, z⟩, eBdry.symm.continuous.comp continuous_sigmaMk⟩ with hFsdef
      have hinjM : ∀ z : (Fam a.2).pt, z ∉ ({y} : Set (Fam a.2).pt) →
          (CategoryTheory.ConcreteCategory.hom (TopCat.ofHom hFs)) z ∉
            ({xb} : Set ↥((modelWithCornersEuclideanHalfSpace 9).boundary
              (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L))) := by
        intro z hz hzy
        exact hz (by
          have h3 : (CategoryTheory.ConcreteCategory.hom (TopCat.ofHom hFs)) z
              = eBdry.symm ⟨a, z⟩ := rfl
          rw [h3] at hzy
          have h : (⟨a, z⟩ : Σ b : Fin m × ι, (Fam b.2).pt) = ⟨a, y⟩ :=
            eBdry.symm.injective (by rw [hzy, hxbdef])
          exact eq_of_heq (Sigma.mk.inj_iff.mp h).2)
      have hkey0 := hB2 (V := Fam a.2) (i := i) (x := y) (hx := hyi)
        (Y := TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary
          (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L)))
        (f := hFs) (g := g) (y := xb) (hy := hxgl)
        (hf := rfl) (hgs := hgs) (hgc := hgc) (hinj := hinjM)
      rw [← hfzdef] at hkey0
      have hG1b := hG1 a y
      have hg7 : Work.Orient.locClass (TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary
            (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L))) 8
          (∑ i : Fin m × ι, Work.ThomBordism.Transversality.OrientBridge.pushClass
            (Fam := fun a : Fin m × ι => Fam a.2) eBdry.symm i) xb
          = (c₀ * fz) • Work.PTGeometric.HOF.chartTr (W := TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary
              (Work.PTGeometric.levelModel {x : M | w x = 0} hWclNew L))) g xb hxgl
              (Work.PTGeometric.HOF.eucFam 8 (by norm_num) (g xb)) :=
        hG1b.trans hkey0
      -- ================= the cancellation =================
      have hcoef : ssign * c₂
          = (ε₁ * (if ε₃ = 1 then (1 : ℤ) else -1) * c₂ * c₀) * (c₀ * fz) := by
        rw [hssdef]
        rcases hc₀ with h | h <;> rw [h] <;> ring
      rw [hb1, hg7, ← mul_smul, ← hcoef]

  obtain ⟨ε, hε, hpt⟩ := hsign
  exact Work.ThomBordism.sourceBoundaryCoord_of_assemblyData (hk := hk) (G := G) (m := m)
    (hm := hm) (hpow := hpow) (D0 := D0') (hWcl := hWclNew) (L := L)
    ⟨eBdry, heBdry, ε, hε, w₀, hpt⟩

/-- **THE REMAINING INPUT OF THE LAST MILE**, now a *standalone* statement about the *named* datum
`Work.ThomBordism.sourceRawBundle …`: the pieces bound the level set of the perturbed ambient field
with the given orientations (`NOTE_SIGN_S6.md` §5-§8, `NOTE_nullhomologous_interface.md`), to be
proved from the tube data of `G` (`GenuineTubeGeometry.localDegree`,
`Work.PTGeometric.proj_relCapPair_pulledThom_collapse`, TEL, `G.tie`) and the transversal-preimage
structure of the level set.  See `NOTE_SESSION48.md` §8/§9b/§9c. -/
theorem sourceBoundaryCoord_sourceRaw
  {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
  {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]
  (hk : 11 ≤ k) (hne : ∀ i, Nonempty (Fam i).pt)
  (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam)
  (m : ℕ) (hm : 0 < m)
  (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
  (hwk : Work.PTGeometric.RegionManifoldTheoremOfIsCompactWeak k)
  (hphi : Work.PTGeometric.SourceRegionPhiInteriorSign k
    (Work.PTGeometric.sourceZeroSet G m hpow)
    {x : EuclideanHalfSpace ((8 + k) + 1) |
      Work.PTGeometric.flatSourceHomotopy8 (k := k)
        (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
        (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ x.1 = D.t₀})
  : Work.ThomBordism.SourceBoundaryCoord
      (Work.ThomBordism.sourceRawBundle hk hne G m hm hpow hwk hphi).datum :=
  (sourceRawBundle hk hne G m hm hpow hwk hphi).coord

/-- **The source construction, with the pin, the boundary coordination, and the collar and
orientation family of its level set** (reassembled from `Work.ThomBordism.sourceRawBundle` and the
standalone coordination statement). -/
theorem sourceRawAmbientData_tied_collar
  {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
  {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]
  (hk : 11 ≤ k) (hne : ∀ i, Nonempty (Fam i).pt)
  (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam)
  (m : ℕ) (hm : 0 < m)
  (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
  (hwk : Work.PTGeometric.RegionManifoldTheoremOfIsCompactWeak k)
  (hphi : Work.PTGeometric.SourceRegionPhiInteriorSign k
    (Work.PTGeometric.sourceZeroSet G m hpow)
    {x : EuclideanHalfSpace ((8 + k) + 1) |
      Work.PTGeometric.flatSourceHomotopy8 (k := k)
        (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
        (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ x.1 = D.t₀})
  : ∃ D0 : Work.PTGeometric.RawAmbientData (k + G.mU) k (Fin m × ι) (fun a => Fam a.2),
    (∀ j : Fin D0.mE, ∃ (i : ι) (w0 : (Fam i).pt)
      (j' : Work.ThomBordism.PontryaginThom.CoverIdx (Fam i) k)
      (hb : w0 ∈ (Work.ThomBordism.tiedND G i).D.baseSet j'),
      D0.ellE j =
        (Work.Tubular.readCLM (G.emb i) (Work.ThomBordism.tiedND G i) j' w0).comp
          (Work.PTGeometric.projEuc k G.mU G.hmU)) ∧
    Work.ThomBordism.SourceBoundaryCoord D0 ∧
    (∃ (hWcl : IsClosed {x : D0.M | D0.v x = 0})
      (L : Work.PTGeometric.LocalLevelData k D0.M {x : D0.M | D0.v x = 0}),
      Work.ThomBordism.SourceOrientHyp D0 hWcl L) :=
  ⟨(sourceRawBundle hk hne G m hm hpow hwk hphi).datum,
   (sourceRawBundle hk hne G m hm hpow hwk hphi).tied,
   sourceBoundaryCoord_sourceRaw hk hne G m hm hpow hwk hphi,
   (sourceRawBundle hk hne G m hm hpow hwk hphi).hWcl,
   (sourceRawBundle hk hne G m hm hpow hwk hphi).L,
   (sourceRawBundle hk hne G m hm hpow hwk hphi).orient⟩

end Work.ThomBordism
