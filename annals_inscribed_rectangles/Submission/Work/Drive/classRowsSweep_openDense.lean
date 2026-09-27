import Mathlib
import Submission.Work.Drive.classRowVocab
import Submission.Work.Drive.hendL012Row
import Submission.Work.Drive.endTripleRegUnrestricted
import Submission.Work.Drive.pairRegRows
import Submission.Work.Drive.sweepGenericityGeneral
import Submission.Work.Drive.exists_meet3Hyp_and_cond_near_of_openDense
import Submission.Work.Drive.classRowRebasing
import Submission.Work.Drive.classRowsSweepVocab
import Submission.Work.Drive.rowsOpen
import Submission.Work.Drive.pairReg_of_loopBoxData
import Submission.Work.Drive.unrestrictedFromBox
import Submission.Work.Drive.blockVocabulary
import Submission.Work.Drive.chartPertRebase
import Submission.Work.Drive.classRowDesignData
import Submission.Work.Drive.classProjectionBricks
import Submission.Work.Drive.exists_loopBoxData_of_small_shift_fam

namespace Work.Drive

open Manifold Set Filter
open scoped Manifold ContDiff Topology BigOperators

set_option maxHeartbeats 2000000

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace
attribute [local instance] Work.Drive.projCharted
local instance instIsManifoldProjChartCRS :
    IsManifold (𝓡 3) Work.Drive.Ctop
      (Projectivization ℝ (Work.Drive.Eucl 3)) :=
  Work.Drive.isManifold_projCharted 3

noncomputable section






/-! ## 0. Two smoothness glues -/

/-- The class projection of the capping space is `C^∞` (the global form of
`Work.Drive.contMDiffAt_cls'`). -/
theorem contMDiff_cls_crs : ContMDiff (𝓡 4) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
    (cls : CappingSpace → Projectivization ℝ (Eucl 3)) :=
  fun p => contMDiffAt_cls' p

/-- **The class map of a jointly smooth family of plane presentations is jointly smooth.** -/
theorem contMDiff_planeClassMap_fam {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : P → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hA : IsSmoothFam₂ A) :
    ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 2))) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : P × EuclideanSpace ℝ (Fin 2) => planeClassMap (A q.1) q.2) := by
  have heq : (fun q : P × EuclideanSpace ℝ (Fin 2) => planeClassMap (A q.1) q.2)
      = fun q : P × EuclideanSpace ℝ (Fin 2) => cls (A q.1 q.2) := by
    funext q
    rfl
  rw [heq]
  exact contMDiff_cls_crs.comp hA

/-! ## 1. The box-restricted rows are open in the family parameter -/

/-- **The box pair regularity is an open condition on the family parameter** (the `(O)` brick of the
class-row lane, in the `IsOpen` form). -/
theorem isOpen_boxPairReg_family {m : ℕ}
    (P Q : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hP : SmoothPlaneFam P) (hQ : SmoothPlaneFam Q) :
    IsOpen {p : EuclideanSpace ℝ (Fin m) | BoxPairReg
      (planeClassMap (P p)) (planeClassMap (Q p))} := by
  rw [isOpen_iff_mem_nhds]
  intro p₀ hp₀
  have hshift : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) => (p₀ + q.1, q.2)) := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  have hAsm : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2)))
      (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) =>
        planeClassMap (P (p₀ + q.1)) q.2) := by
    have h := (contMDiff_planeClassMap_fam P hP).comp hshift
    simpa only [Function.comp_def] using h
  have hBsm : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2)))
      (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) =>
        planeClassMap (Q (p₀ + q.1)) q.2) := by
    have h := (contMDiff_planeClassMap_fam Q hQ).comp hshift
    simpa only [Function.comp_def] using h
  have h0 : BoxPairRegG (planeClassMap (P (p₀ + 0))) (planeClassMap (Q (p₀ + 0))) := by
    rw [boxPairRegG_iff]
    simpa using hp₀
  have hmain := eventually_boxPairRegG_at
    (fun s : EuclideanSpace ℝ (Fin m) => planeClassMap (P (p₀ + s)))
    (fun s : EuclideanSpace ℝ (Fin m) => planeClassMap (Q (p₀ + s))) hAsm hBsm h0
  have htend : Tendsto (fun p : EuclideanSpace ℝ (Fin m) => p - p₀) (𝓝 p₀) (𝓝 0) := by
    simpa using (continuous_sub_right p₀).tendsto p₀
  have hfinal : ∀ᶠ p in 𝓝 p₀, BoxPairReg (planeClassMap (P p)) (planeClassMap (Q p)) := by
    refine (htend.eventually hmain).mono fun p hp => ?_
    rw [← boxPairRegG_iff]
    have hpp : p₀ + (p - p₀) = p := by abel
    simpa only [hpp] using hp
  exact hfinal

/-- **The box end-triple regularity is an open condition on the family parameter.** -/
theorem isOpen_boxEndTripleReg_family {m : ℕ}
    (F P Q : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hF : SmoothPlaneFam F) (hP : SmoothPlaneFam P) (hQ : SmoothPlaneFam Q) :
    IsOpen {p : EuclideanSpace ℝ (Fin m) | BoxEndTripleReg
      (planeClassMap (F p)) (planeClassMap (P p)) (planeClassMap (Q p))} := by
  rw [isOpen_iff_mem_nhds]
  intro p₀ hp₀
  have hshift : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) => (p₀ + q.1, q.2)) := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  have hFsm : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2)))
      (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) =>
        planeClassMap (F (p₀ + q.1)) q.2) := by
    have h := (contMDiff_planeClassMap_fam F hF).comp hshift
    simpa only [Function.comp_def] using h
  have hPsm : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2)))
      (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) =>
        planeClassMap (P (p₀ + q.1)) q.2) := by
    have h := (contMDiff_planeClassMap_fam P hP).comp hshift
    simpa only [Function.comp_def] using h
  have hQsm : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2)))
      (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) =>
        planeClassMap (Q (p₀ + q.1)) q.2) := by
    have h := (contMDiff_planeClassMap_fam Q hQ).comp hshift
    simpa only [Function.comp_def] using h
  have h0 : BoxEndTripleRegG (planeClassMap (F (p₀ + 0))) (planeClassMap (P (p₀ + 0)))
      (planeClassMap (Q (p₀ + 0))) := by
    rw [boxEndTripleRegG_iff]
    simpa using hp₀
  have hmain := eventually_boxEndTripleRegG_at
    (fun s : EuclideanSpace ℝ (Fin m) => planeClassMap (F (p₀ + s)))
    (fun s : EuclideanSpace ℝ (Fin m) => planeClassMap (P (p₀ + s)))
    (fun s : EuclideanSpace ℝ (Fin m) => planeClassMap (Q (p₀ + s))) hFsm hPsm hQsm h0
  have htend : Tendsto (fun p : EuclideanSpace ℝ (Fin m) => p - p₀) (𝓝 p₀) (𝓝 0) := by
    simpa using (continuous_sub_right p₀).tendsto p₀
  have hfinal : ∀ᶠ p in 𝓝 p₀, BoxEndTripleReg (planeClassMap (F p)) (planeClassMap (P p))
      (planeClassMap (Q p)) := by
    refine (htend.eventually hmain).mono fun p hp => ?_
    rw [← boxEndTripleRegG_iff]
    have hpp : p₀ + (p - p₀) = p := by abel
    simpa only [hpp] using hp
  exact hfinal



/-- **The per-parameter smoothness of a jointly smooth family of plane presentations.** -/
theorem smoothPlane_of_fam {m : ℕ} {P : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 2) →
    CappingSpace} (hP : SmoothPlaneFam P) (t : EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (P t) := by
  have h1 : ContMDiff (𝓡 2) (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2)))
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin 2) => (t, y)) := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  have h2 := hP.comp h1
  simpa only [Function.comp_def, Prod.snd] using h2

/-- **The *unrestricted* pair row is open in the family parameter** for presentations invariant under
the affine symmetries of the parameter square. -/
theorem isOpen_pairReg_family_of_affRep {m : ℕ}
    (P Q : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hP : SmoothPlaneFam P) (hQ : SmoothPlaneFam Q)
    (hPinv : ∀ (t : EuclideanSpace ℝ (Fin m)) (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ),
      (∀ i : Fin 2, e i = 1 ∨ e i = -1) →
      ∀ y : EuclideanSpace ℝ (Fin 2), P t (affRep e mm y) = P t y)
    (hQinv : ∀ (t : EuclideanSpace ℝ (Fin m)) (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ),
      (∀ i : Fin 2, e i = 1 ∨ e i = -1) →
      ∀ y : EuclideanSpace ℝ (Fin 2), Q t (affRep e mm y) = Q t y) :
    IsOpen {t : EuclideanSpace ℝ (Fin m) | PairReg
      (planeClassMap (P t)) (planeClassMap (Q t))} := by
  have hbox := isOpen_boxPairReg_family P Q hP hQ
  have hset : {t : EuclideanSpace ℝ (Fin m) | PairReg
        (planeClassMap (P t)) (planeClassMap (Q t))}
      = {t : EuclideanSpace ℝ (Fin m) | BoxPairReg
        (planeClassMap (P t)) (planeClassMap (Q t))} := by
    ext t
    constructor
    · intro h y y' _ _ hyy
      exact h y y' hyy
    · intro h
      exact pairReg_of_boxPairReg_affRep (P t) (Q t) (smoothPlane_of_fam hP t)
        (smoothPlane_of_fam hQ t) (hPinv t) (hQinv t) h
  rw [hset]
  exact hbox

/-- **The *unrestricted* end-triple row is open in the family parameter** for a family of triples of
presentations invariant under the affine symmetries of the parameter square. -/
theorem isOpen_endTripleReg_family_of_affRep {m : ℕ}
    (P : EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hP : ∀ k : Fin 3, SmoothPlaneFam (fun t => P t k))
    (hPinv : ∀ (t : EuclideanSpace ℝ (Fin m)) (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ),
      (∀ i : Fin 2, e i = 1 ∨ e i = -1) →
      ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), P t k (affRep e mm y) = P t k y) :
    IsOpen {t : EuclideanSpace ℝ (Fin m) | EndTripleReg
      (planeClassMap (P t 0)) (planeClassMap (P t 1)) (planeClassMap (P t 2))} := by
  have hbox := isOpen_boxEndTripleReg_family (fun t => P t 0) (fun t => P t 1) (fun t => P t 2)
    (hP 0) (hP 1) (hP 2)
  have hset : {t : EuclideanSpace ℝ (Fin m) | EndTripleReg
        (planeClassMap (P t 0)) (planeClassMap (P t 1)) (planeClassMap (P t 2))}
      = {t : EuclideanSpace ℝ (Fin m) | BoxEndTripleReg
        (planeClassMap (P t 0)) (planeClassMap (P t 1)) (planeClassMap (P t 2))} := by
    ext t
    constructor
    · intro h y₀ y₁ y₂ _ h1 h2
      exact h y₀ y₁ y₂ h1 h2
    · intro h
      exact endTripleReg_of_boxEndTripleReg_affRep (fun k => P t k)
        (fun k => smoothPlane_of_fam (hP k) t) (fun e mm he k y => hPinv t e mm he k y) h
  rw [hset]
  exact hbox


/-! ## 3. The five presentations of the four sweep rows, and the exact re-basing -/

/-- The block index attached to the `j`-th slot of the quintuple of presentations: slots `0,1,2` are
the three design blocks, slots `3,4` the two transported linear models (attached to the blocks `0`
and `1`, whose parameters they carry). -/
def slotIdx : Fin 5 → Fin 3 := ![0, 1, 2, 0, 1]

/-- **The five *base* plane presentations** of the four sweep rows: the three rotated charts of `Q`
and the two linear disk models.  The design's presentations at the parameter `t` are the
`chartPert (blk (slotIdx j) t)`-perturbations of these. -/
def sweepRowsBase (Q : ℂ → CappingSpace) (a c' : UnitAddCircle)
    (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl) :
    Fin 5 → EuclideanSpace ℝ (Fin 2) → CappingSpace :=
  ![rotPresentation Q (designAngles a c' 0), rotPresentation Q (designAngles a c' 1),
    rotPresentation Q (designAngles a c' 2),
    diskPlane (linPlaneChart (Φ 0) cl hcl), diskPlane (linPlaneChart (Φ 1) cl hcl)]

/-- **The five plane presentations of the four sweep rows at the parameter `t`.** -/
def sweepRowsPresentations (Q : ℂ → CappingSpace) (a c' : UnitAddCircle)
    (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl)
    (t : EuclideanSpace ℝ (Fin 12)) : Fin 5 → EuclideanSpace ℝ (Fin 2) → CappingSpace :=
  fun j y => chartPert (blk (slotIdx j) t) (sweepRowsBase Q a c' Φ cl hcl j y)

@[simp] lemma sweepRowsPresentations_apply (Q : ℂ → CappingSpace) (a c' : UnitAddCircle)
    (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl)
    (t : EuclideanSpace ℝ (Fin 12)) (j : Fin 5) (y : EuclideanSpace ℝ (Fin 2)) :
    sweepRowsPresentations Q a c' Φ cl hcl t j y
      = chartPert (blk (slotIdx j) t) (sweepRowsBase Q a c' Φ cl hcl j y) := rfl

@[simp] lemma sweepRowsBase_zero (Q : ℂ → CappingSpace) (a c' : UnitAddCircle)
    (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl) :
    sweepRowsBase Q a c' Φ cl hcl 0 = rotPresentation Q (designAngles a c' 0) := rfl

@[simp] lemma sweepRowsBase_one (Q : ℂ → CappingSpace) (a c' : UnitAddCircle)
    (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl) :
    sweepRowsBase Q a c' Φ cl hcl 1 = rotPresentation Q (designAngles a c' 1) := rfl

@[simp] lemma sweepRowsBase_two (Q : ℂ → CappingSpace) (a c' : UnitAddCircle)
    (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl) :
    sweepRowsBase Q a c' Φ cl hcl 2 = rotPresentation Q (designAngles a c' 2) := rfl

@[simp] lemma sweepRowsBase_three (Q : ℂ → CappingSpace) (a c' : UnitAddCircle)
    (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl) :
    sweepRowsBase Q a c' Φ cl hcl 3 = diskPlane (linPlaneChart (Φ 0) cl hcl) := rfl

@[simp] lemma sweepRowsBase_four (Q : ℂ → CappingSpace) (a c' : UnitAddCircle)
    (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl) :
    sweepRowsBase Q a c' Φ cl hcl 4 = diskPlane (linPlaneChart (Φ 1) cl hcl) := rfl

@[simp] lemma slotIdx_zero : slotIdx 0 = 0 := rfl
@[simp] lemma slotIdx_one : slotIdx 1 = 1 := rfl
@[simp] lemma slotIdx_two : slotIdx 2 = 2 := rfl
@[simp] lemma slotIdx_three : slotIdx 3 = 0 := rfl
@[simp] lemma slotIdx_four : slotIdx 4 = 1 := rfl

@[simp] lemma sweepRowsPresentations_zero (Q : ℂ → CappingSpace) (a c' : UnitAddCircle)
    (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl)
    (t : EuclideanSpace ℝ (Fin 12)) :
    sweepRowsPresentations Q a c' Φ cl hcl t 0
      = fun y : EuclideanSpace ℝ (Fin 2) =>
          chartPert ((blk 0) t) (rotPresentation Q (designAngles a c' 0) y) := rfl

@[simp] lemma sweepRowsPresentations_one (Q : ℂ → CappingSpace) (a c' : UnitAddCircle)
    (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl)
    (t : EuclideanSpace ℝ (Fin 12)) :
    sweepRowsPresentations Q a c' Φ cl hcl t 1
      = fun y : EuclideanSpace ℝ (Fin 2) =>
          chartPert ((blk 1) t) (rotPresentation Q (designAngles a c' 1) y) := rfl

@[simp] lemma sweepRowsPresentations_two (Q : ℂ → CappingSpace) (a c' : UnitAddCircle)
    (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl)
    (t : EuclideanSpace ℝ (Fin 12)) :
    sweepRowsPresentations Q a c' Φ cl hcl t 2
      = fun y : EuclideanSpace ℝ (Fin 2) =>
          chartPert ((blk 2) t) (rotPresentation Q (designAngles a c' 2) y) := rfl

@[simp] lemma sweepRowsPresentations_three (Q : ℂ → CappingSpace) (a c' : UnitAddCircle)
    (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl)
    (t : EuclideanSpace ℝ (Fin 12)) :
    sweepRowsPresentations Q a c' Φ cl hcl t 3
      = fun y : EuclideanSpace ℝ (Fin 2) =>
          chartPert ((blk 0) t) (diskPlane (linPlaneChart (Φ 0) cl hcl) y) := rfl

@[simp] lemma sweepRowsPresentations_four (Q : ℂ → CappingSpace) (a c' : UnitAddCircle)
    (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl)
    (t : EuclideanSpace ℝ (Fin 12)) :
    sweepRowsPresentations Q a c' Φ cl hcl t 4
      = fun y : EuclideanSpace ℝ (Fin 2) =>
          chartPert ((blk 1) t) (diskPlane (linPlaneChart (Φ 1) cl hcl) y) := rfl

/-- **The pair row** (`PairReg P̂₁P̂₂`) as a property of the quintuple of presentations. -/
def PairRowFam (F : Fin 5 → EuclideanSpace ℝ (Fin 2) → CappingSpace) : Prop :=
  PairReg (planeClassMap (F 1)) (planeClassMap (F 2))

/-- **The three end-triple rows** as a property of the quintuple of presentations. -/
def TripleRowsFam (F : Fin 5 → EuclideanSpace ℝ (Fin 2) → CappingSpace) : Prop :=
  EndTripleReg (planeClassMap (F 0)) (planeClassMap (F 1)) (planeClassMap (F 2)) ∧
  EndTripleReg (planeClassMap (F 3)) (planeClassMap (F 1)) (planeClassMap (F 2)) ∧
  EndTripleReg (planeClassMap (F 4)) (planeClassMap (F 3)) (planeClassMap (F 2))

/-- **The four sweep rows** as a property of the quintuple of presentations. -/
def SweepRowsFam (F : Fin 5 → EuclideanSpace ℝ (Fin 2) → CappingSpace) : Prop :=
  PairRowFam F ∧ TripleRowsFam F

/-- **`DesignRowsSweepAt` is `SweepRowsFam` of the design's quintuple of presentations** (the two
transported linear models are the chart perturbations of the fixed linear disk presentations). -/
lemma designRowsSweepAt_iff (Q : ℂ → CappingSpace) (a c' : UnitAddCircle)
    (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl)
    (t : EuclideanSpace ℝ (Fin 12)) :
    DesignRowsSweepAt Q a c' Φ cl hcl t
      ↔ SweepRowsFam (sweepRowsPresentations Q a c' Φ cl hcl t) := by
  have h3 : linTransClass (Φ 0) ((blk 0) t) cl hcl
      = planeClassMap (sweepRowsPresentations Q a c' Φ cl hcl t 3) := by
    rw [sweepRowsPresentations_three]
    exact (planeClassMap_chartPert_diskPlane_linPlaneChart (Φ 0) cl hcl ((blk 0) t)).symm
  have h4 : linTransClass (Φ 1) ((blk 1) t) cl hcl
      = planeClassMap (sweepRowsPresentations Q a c' Φ cl hcl t 4) := by
    rw [sweepRowsPresentations_four]
    exact (planeClassMap_chartPert_diskPlane_linPlaneChart (Φ 1) cl hcl ((blk 1) t)).symm
  have hd0 : designPertPlane Q (designAngles a c' 0) t 0
      = fun y : EuclideanSpace ℝ (Fin 2) =>
          chartPert ((blk 0) t) (rotPresentation Q (designAngles a c' 0) y) := rfl
  have hd1 : designPertPlane Q (designAngles a c' 1) t 1
      = fun y : EuclideanSpace ℝ (Fin 2) =>
          chartPert ((blk 1) t) (rotPresentation Q (designAngles a c' 1) y) := rfl
  have hd2 : designPertPlane Q (designAngles a c' 2) t 2
      = fun y : EuclideanSpace ℝ (Fin 2) =>
          chartPert ((blk 2) t) (rotPresentation Q (designAngles a c' 2) y) := rfl
  simp only [DesignRowsSweepAt, SweepRowsFam, PairRowFam, TripleRowsFam,
    sweepRowsPresentations_zero, sweepRowsPresentations_one, sweepRowsPresentations_two,
    sweepRowsPresentations_three, sweepRowsPresentations_four, designPertClass,
    hd0, hd1, hd2, h3, h4]

/-- **The exact re-basing of the four rows**: replacing the parameter `qMul12 σ x` by the composite of
the two chart perturbations at `σ` and `x` does not change `PairRowFam`. -/
lemma pairRowFam_rebase (F : Fin 5 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (σ x : EuclideanSpace ℝ (Fin 12))
    (hnd : ∀ k : Fin 3, pureInner (blk k σ) (blk k x) ≠ 1) :
    PairRowFam (fun j y => chartPert (blk (slotIdx j) (qMul12 σ x)) (F j y))
      ↔ PairRowFam (fun j y =>
          chartPert (blk (slotIdx j) σ) (chartPert (blk (slotIdx j) x) (F j y))) := by
  have h : ∀ j : Fin 5, (fun y => chartPert (blk (slotIdx j) (qMul12 σ x)) (F j y))
      = fun y => chartPert (blk (slotIdx j) σ) (chartPert (blk (slotIdx j) x) (F j y)) := by
    intro j
    funext y
    rw [chartPert_rebase (σ := σ) (x := x) (t := qMul12 σ x) (k := slotIdx j)
      (blk_qMul12 (slotIdx j) σ x) (hnd (slotIdx j)), Function.comp_apply]
  simp only [PairRowFam, h]

/-- **The exact re-basing of the three end-triple rows.** -/
lemma tripleRowsFam_rebase (F : Fin 5 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (σ x : EuclideanSpace ℝ (Fin 12))
    (hnd : ∀ k : Fin 3, pureInner (blk k σ) (blk k x) ≠ 1) :
    TripleRowsFam (fun j y => chartPert (blk (slotIdx j) (qMul12 σ x)) (F j y))
      ↔ TripleRowsFam (fun j y =>
          chartPert (blk (slotIdx j) σ) (chartPert (blk (slotIdx j) x) (F j y))) := by
  have h : ∀ j : Fin 5, (fun y => chartPert (blk (slotIdx j) (qMul12 σ x)) (F j y))
      = fun y => chartPert (blk (slotIdx j) σ) (chartPert (blk (slotIdx j) x) (F j y)) := by
    intro j
    funext y
    rw [chartPert_rebase (σ := σ) (x := x) (t := qMul12 σ x) (k := slotIdx j)
      (blk_qMul12 (slotIdx j) σ x) (hnd (slotIdx j)), Function.comp_apply]
  simp only [TripleRowsFam, h]

/-- **THE DENSITY TRANSFER for the three end-triple rows**: if the rows hold for the *re-based*
quintuple at parameters `σ` arbitrarily close to `0`, then they hold for the quintuple at parameters
`t` arbitrarily close to the base point `x`. -/
theorem exists_tripleRowsFam_near_qMul (F : Fin 5 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    {x : EuclideanSpace ℝ (Fin 12)}
    (hbase : ∀ η : ℝ, 0 < η → ∃ σ : EuclideanSpace ℝ (Fin 12), ‖σ‖ < η ∧
      TripleRowsFam (fun j y => chartPert (blk (slotIdx j) σ)
        (chartPert (blk (slotIdx j) x) (F j y))))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ t : EuclideanSpace ℝ (Fin 12), ‖t - x‖ < δ ∧
      TripleRowsFam (fun j y => chartPert (blk (slotIdx j) t) (F j y)) := by
  obtain ⟨η₁, hη₁, hη₁sub⟩ := exists_norm_qMul12_sub_lt x (by linarith : (0 : ℝ) < δ / 2)
  have hcont : ∀ k : Fin 3, Continuous fun σ : EuclideanSpace ℝ (Fin 12) =>
      pureInner (blk k σ) (blk k x) :=
    fun k => (continuous_pureInner_right (blk k x)).comp (blk k).continuous
  have hev : ∀ᶠ σ : EuclideanSpace ℝ (Fin 12) in 𝓝 0,
      ∀ k : Fin 3, pureInner (blk k σ) (blk k x) ≠ 1 := by
    rw [Filter.eventually_all]
    intro k
    exact (hcont k).continuousAt.eventually_ne (by simp [map_zero, pureInner])
  have hmem : {σ : EuclideanSpace ℝ (Fin 12) | ∀ k : Fin 3, pureInner (blk k σ) (blk k x) ≠ 1}
      ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin 12)) := hev
  obtain ⟨η₂, hη₂, hη₂sub⟩ := Metric.mem_nhds_iff.mp hmem
  have hη₂' : ∀ σ : EuclideanSpace ℝ (Fin 12), ‖σ‖ < η₂ →
      ∀ k : Fin 3, pureInner (blk k σ) (blk k x) ≠ 1 := by
    intro σ hσ
    exact hη₂sub (by rwa [Metric.mem_ball, dist_zero_right])
  obtain ⟨σ, hσ, hrows⟩ := hbase (min η₁ η₂ / 2) (by positivity)
  have hσ₁ : ‖σ‖ < η₁ := lt_of_lt_of_le hσ (by have := min_le_left η₁ η₂; linarith)
  have hσ₂ : ‖σ‖ < η₂ := lt_of_lt_of_le hσ (by have := min_le_right η₁ η₂; linarith)
  exact ⟨qMul12 σ x, lt_of_lt_of_le (hη₁sub σ hσ₁) (by linarith),
    (tripleRowsFam_rebase F σ x (hη₂' σ hσ₂)).mpr hrows⟩

/-! ## 5. The level band of the re-based presentations -/

/-- The level of a rotated chart presentation on the plane is above the truncation level `c`. -/
lemma lt_levelOf_rotPresentation {Q : ℂ → CappingSpace} {c : ℝ}
    (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p) (u : UnitAddCircle)
    (y : EuclideanSpace ℝ (Fin 2)) :
    c < levelOf (rotPresentation Q u y) := by
  have hnorm : sqDisk (foldBox y) ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact norm_sqDisk_le_one (foldBox y) (foldBox_mem_unitBox y)
  have hmem : Q (sqDisk (foldBox y)) ∈ chartDisk Q := ⟨sqDisk (foldBox y), hnorm, rfl⟩
  have h := hcbot _ hmem
  have h2 : levelOf (rotPresentation Q u y) = levelOf (Q (sqDisk (foldBox y))) := by
    show levelOf (rotCapping u (Q (sqDisk (foldBox y)))) = levelOf (Q (sqDisk (foldBox y)))
    rw [levelOf_rotCapping]
  rwa [h2]

/-- The level of a perturbed *re-based* design presentation: the two chart perturbations multiply the
level by `exp ((blk k t) 0) * exp ((blk k x) 0) ≥ exp (-(1 + ‖x‖))` when `‖t‖ < 1`. -/
lemma lt_levelOf_rebased_block {Q : ℂ → CappingSpace} {c c0 : ℝ}
    (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p) (x : EuclideanSpace ℝ (Fin 12))
    (hc0 : c0 < c * Real.exp (-(1 + ‖x‖)))
    (u : Fin 3 → UnitAddCircle) {t : EuclideanSpace ℝ (Fin 12)} (ht : ‖t‖ < 1)
    (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)) :
    c0 < levelOf (chartPert ((blk k) t)
      (chartPert ((blk k) x) (rotPresentation Q (u k) y))) := by
  have h1 : levelOf (chartPert ((blk k) t) (chartPert ((blk k) x) (rotPresentation Q (u k) y)))
      = levelOf (rotPresentation Q (u k) y)
        * (Real.exp (((blk k) x).ofLp 0) * Real.exp (((blk k) t).ofLp 0)) := by
    rw [levelOf_chartPert_mul, levelOf_chartPert_mul]
    ring
  have hx0 : Real.exp (-‖x‖) ≤ Real.exp (((blk k) x).ofLp 0) := by
    refine Real.exp_le_exp.mpr ?_
    have h := abs_coord_blk_le k x
    have h' : -|((blk k) x).ofLp 0| ≤ ((blk k) x).ofLp 0 := neg_abs_le _
    linarith [abs_nonneg (((blk k) x).ofLp 0)]
  have ht0 : Real.exp (-(1 : ℝ)) ≤ Real.exp (((blk k) t).ofLp 0) :=
    Real.exp_le_exp.mpr (by
      have h := exp_coord_blk_ge k t
      have h2 : -‖t‖ ≤ ((blk k) t).ofLp 0 := Real.exp_le_exp.mp h
      linarith)
  have hprod : Real.exp (-(1 + ‖x‖))
      ≤ Real.exp (((blk k) x).ofLp 0) * Real.exp (((blk k) t).ofLp 0) := by
    have h2 : Real.exp (-‖x‖) * Real.exp (-(1 : ℝ))
        ≤ Real.exp (((blk k) x).ofLp 0) * Real.exp (((blk k) t).ofLp 0) :=
      mul_le_mul hx0 ht0 (Real.exp_pos _).le (Real.exp_pos _).le
    have h3 : Real.exp (-‖x‖) * Real.exp (-(1 : ℝ)) = Real.exp (-(1 + ‖x‖)) := by
      rw [← Real.exp_add]; ring_nf
    linarith [h3 ▸ h2]
  rw [h1]
  have hbase := lt_levelOf_rotPresentation hcbot (u k) y
  exact lt_of_lt_of_le hc0
    (mul_le_mul hbase.le hprod (Real.exp_pos _).le (levelOf_pos _).le)

/-- **The transported linear model as a class-map composite**: the transport of the functional by
`classEquiv χ` and the perturbation by `τ` is the double chart perturbation of the linear disk
presentation. -/
lemma linTransClass_trans (Φ : Eucl 3 ≃L[ℝ] Eucl 3) (τ χ : Eucl 3) (cl : ℝ) (hcl : 0 < cl) :
    linTransClass (Φ.trans (classEquiv χ)) τ cl hcl
      = planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) =>
          chartPert τ (chartPert χ (diskPlane (linPlaneChart Φ cl hcl) y))) := by
  rw [linTransClass]
  rw [planeClassMap_chartPert_comp_cr τ
    (fun y : EuclideanSpace ℝ (Fin 2) => chartPert χ (diskPlane (linPlaneChart Φ cl hcl) y))]
  rw [planeClassMap_chartPert_diskPlane_linPlaneChart Φ cl hcl χ]
  rw [← planeClassMap_chartPert_diskPlane_linPlaneChart (Φ.trans (classEquiv χ)) cl hcl τ]
  rw [planeClassMap_chartPert_comp_cr τ
    (diskPlane (linPlaneChart (Φ.trans (classEquiv χ)) cl hcl))]

/-- The base linear presentations of the four sweep rows are smooth. -/
lemma contMDiff_sweepRowsBase (Q : ℂ → CappingSpace) (hQsm : IsSmoothChart Q)
    (a c' : UnitAddCircle) (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl)
    (j : Fin 5) :
    ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (sweepRowsBase Q a c' Φ cl hcl j) := by
  fin_cases j
  · exact contMDiff_rotPresentation Q (designAngles a c' 0) (contMDiff_diskPlane hQsm)
  · exact contMDiff_rotPresentation Q (designAngles a c' 1) (contMDiff_diskPlane hQsm)
  · exact contMDiff_rotPresentation Q (designAngles a c' 2) (contMDiff_diskPlane hQsm)
  · exact contMDiff_diskPlane (linPlaneChart_contMDiff (Φ 0) cl hcl)
  · exact contMDiff_diskPlane (linPlaneChart_contMDiff (Φ 1) cl hcl)

/-- The base presentations of the four sweep rows are invariant under the affine symmetries of the
parameter square. -/
lemma sweepRowsBase_affRep (Q : ℂ → CappingSpace) (a c' : UnitAddCircle)
    (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl) (j : Fin 5)
    (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ) (he : ∀ i : Fin 2, e i = 1 ∨ e i = -1)
    (y : EuclideanSpace ℝ (Fin 2)) :
    sweepRowsBase Q a c' Φ cl hcl j (affRep e mm y) = sweepRowsBase Q a c' Φ cl hcl j y := by
  fin_cases j
  · exact rotPresentation_affRep he mm Q (designAngles a c' 0) y
  · exact rotPresentation_affRep he mm Q (designAngles a c' 1) y
  · exact rotPresentation_affRep he mm Q (designAngles a c' 2) y
  · show diskPlane (linPlaneChart (Φ 0) cl hcl) (affRep e mm y)
        = diskPlane (linPlaneChart (Φ 0) cl hcl) y
    exact diskPlane_affRep he mm _ y
  · show diskPlane (linPlaneChart (Φ 1) cl hcl) (affRep e mm y)
        = diskPlane (linPlaneChart (Φ 1) cl hcl) y
    exact diskPlane_affRep he mm _ y

/-- The block slots of `sweepRowsBase` are the rotated charts. -/
lemma sweepRowsBase_block (Q : ℂ → CappingSpace) (a c' : UnitAddCircle)
    (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl) (k : Fin 3) :
    sweepRowsBase Q a c' Φ cl hcl (Fin.castLE (by norm_num) k)
      = rotPresentation Q (designAngles a c' k) := by
  fin_cases k <;> rfl

/-- The level of a perturbed *linear* disk presentation. -/
lemma lt_levelOf_chartPert_lin (Φ : Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl)
    (x : EuclideanSpace ℝ (Fin 12)) {c0 : ℝ} (hc0 : c0 < cl * Real.exp (-(1 + ‖x‖)))
    {t : EuclideanSpace ℝ (Fin 12)} (ht : ‖t‖ < 1) (k : Fin 3)
    (y : EuclideanSpace ℝ (Fin 2)) :
    c0 < levelOf (chartPert ((blk k) t) (diskPlane (linPlaneChart Φ cl hcl) y)) := by
  have h1 : levelOf (chartPert ((blk k) t) (diskPlane (linPlaneChart Φ cl hcl) y))
      = cl * Real.exp (((blk k) t).ofLp 0) := by
    rw [levelOf_chartPert_mul]
    congr 1
    show ((cappingSpaceHomeoProj (diskPlane (linPlaneChart Φ cl hcl) y)).1 : ℝ) = cl
    rw [show diskPlane (linPlaneChart Φ cl hcl) y = linPlaneChart Φ cl hcl (sqDisk (foldBox y))
        from rfl, level_linPlaneChart]
  rw [h1]
  have ht0 : Real.exp (-(1 : ℝ)) ≤ Real.exp (((blk k) t).ofLp 0) :=
    Real.exp_le_exp.mpr (by
      have h := exp_coord_blk_ge k t
      have h2 : -‖t‖ ≤ ((blk k) t).ofLp 0 := Real.exp_le_exp.mp h
      linarith)
  have h2 : Real.exp (-(1 + ‖x‖)) ≤ Real.exp (-(1 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith [norm_nonneg x])
  calc c0 < cl * Real.exp (-(1 + ‖x‖)) := hc0
    _ ≤ cl * Real.exp (((blk k) t).ofLp 0) :=
        mul_le_mul_of_nonneg_left (le_trans h2 ht0) hcl.le

/-- **The three end-triple rows of the four sweep rows, at parameters arbitrarily close to `0`, for the
*re-based* presentations.**  This is the producer `Work.Drive.exists_classRows345_design` applied to the
re-based block presentations and to the functionals transported by `classEquiv (blk · x)`, converted
into `TripleRowsFam`. -/
theorem tripleRows_base_near_zero (Q : ℂ → CappingSpace) (hQsm : IsSmoothChart Q)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    {c : ℝ} (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (a c' : UnitAddCircle) (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl)
    (x : EuclideanSpace ℝ (Fin 12)) :
    ∀ η : ℝ, 0 < η → ∃ σ : EuclideanSpace ℝ (Fin 12), ‖σ‖ < η ∧
      TripleRowsFam (fun j y => chartPert (blk (slotIdx j) σ)
        (chartPert (blk (slotIdx j) x) (sweepRowsBase Q a c' Φ cl hcl j y))) := by
  intro η hη
  -- ## the sweep levels
  set d0 : ℝ := min c cl * Real.exp (-(1 + ‖x‖)) / 4 with hd0def
  have hd0pos : 0 < d0 := by rw [hd0def]; positivity
  have hd0lt : d0 < c * Real.exp (-(1 + ‖x‖)) := by
    rw [hd0def]
    have h1 : min c cl ≤ c := min_le_left _ _
    have h2 : (0 : ℝ) < Real.exp (-(1 + ‖x‖)) := Real.exp_pos _
    nlinarith
  have hd0lt' : d0 < cl * Real.exp (-(1 + ‖x‖)) := by
    rw [hd0def]
    have h1 : min c cl ≤ cl := min_le_right _ _
    have h2 : (0 : ℝ) < Real.exp (-(1 + ‖x‖)) := Real.exp_pos _
    nlinarith
  set d : Fin 3 → ℝ := ![d0, d0 / 2, d0 / 3] with hddef
  have hd0' : d 0 = d0 := by simp [hddef]
  have hd1' : d 1 = d0 / 2 := by simp [hddef]
  have hd2' : d 2 = d0 / 3 := by simp [hddef]
  have htriple : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  have hdcpos : ∀ k : Fin 3, 0 < d k := by
    intro k
    rcases htriple k with h | h | h <;> rw [h]
    · rw [hd0']; positivity
    · rw [hd1']; positivity
    · rw [hd2']; positivity
  have hcdist : ∀ k k' : Fin 3, d k = d k' → k = k' := by
    intro k k' h
    rcases htriple k with h1 | h1 | h1 <;> rcases htriple k' with h2 | h2 | h2
    · rw [h1, h2]
    · exfalso; rw [h1, h2] at h; rw [hd0', hd1'] at h; linarith
    · exfalso; rw [h1, h2] at h; rw [hd0', hd2'] at h; linarith
    · exfalso; rw [h1, h2] at h; rw [hd1', hd0'] at h; linarith
    · rw [h1, h2]
    · exfalso; rw [h1, h2] at h; rw [hd1', hd2'] at h; linarith
    · exfalso; rw [h1, h2] at h; rw [hd2', hd0'] at h; linarith
    · exfalso; rw [h1, h2] at h; rw [hd2', hd1'] at h; linarith
    · rw [h1, h2]
  have hc10 : d 1 < d 0 := by rw [hd0', hd1']; linarith
  have hc20 : d 2 < d 0 := by rw [hd0', hd2']; linarith
  have hdlt : d 0 < c * Real.exp (-(1 + ‖x‖)) := by rw [hd0']; exact hd0lt
  have hdlt' : d 0 < cl * Real.exp (-(1 + ‖x‖)) := by rw [hd0']; exact hd0lt'
  -- ## the transported functionals
  set Phi0t : Eucl 3 ≃L[ℝ] Eucl 3 := (Φ 0).trans (classEquiv ((blk 0) x)) with hPhi0t
  set Phi1t : Eucl 3 ≃L[ℝ] Eucl 3 := (Φ 1).trans (classEquiv ((blk 1) x)) with hPhi1t
  -- ## the re-based block presentations
  set Pcfg : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace :=
    fun k y => chartPert ((blk k) x) (rotPresentation Q (designAngles a c' k) y) with hPcfgdef
  have hPcfg_sm : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (Pcfg k) := by
    intro k
    have h := contMDiff_apply_of_chartPert (isChartPert_chartPert Q) ((blk k) x)
    rw [hPcfgdef]
    exact h.comp (contMDiff_rotPresentation Q (designAngles a c' k) (contMDiff_diskPlane hQsm))
  have hPcfg_seam : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      onSeam2 y → Pcfg k y = Pcfg k (seamInv2 y) := by
    intro k y hy
    rw [hPcfgdef]
    exact congrArg (chartPert ((blk k) x))
      (rotPresentation_seamInv Q hQseam (designAngles a c' k) y hy)
  have hPcfg_inv : ∀ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ), (∀ i : Fin 2, e i = 1 ∨ e i = -1) →
      ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), Pcfg k (affRep e mm y) = Pcfg k y := by
    intro e mm he k y
    rw [hPcfgdef]
    exact congrArg (chartPert ((blk k) x))
      (rotPresentation_affRep he mm Q (designAngles a c' k) y)
  -- ## the level hypothesis
  have hlevP : ∀ (t : EuclideanSpace ℝ (Fin 12)), ‖t‖ < min η 1 → ∀ (k : Fin 3)
      (y : EuclideanSpace ℝ (Fin 2)),
      d 0 < levelOf (chartPert ((blk k) t) (Pcfg k y)) := by
    intro t ht k y
    rw [hPcfgdef]
    exact lt_levelOf_rebased_block hcbot x hdlt (designAngles a c')
      (lt_of_lt_of_le ht (min_le_right _ _)) k y
  have hL0 : ∀ (t : EuclideanSpace ℝ (Fin 12)), ‖t‖ < min η 1 → ∀ (k : Fin 3)
      (y : EuclideanSpace ℝ (Fin 2)),
      d 0 < levelOf (chartPert ((blk k) t) (diskPlane (linPlaneChart Phi0t cl hcl) y)) :=
    fun t ht k y => lt_levelOf_chartPert_lin Phi0t cl hcl x hdlt'
      (lt_of_lt_of_le ht (min_le_right _ _)) k y
  have hL1 : ∀ (t : EuclideanSpace ℝ (Fin 12)), ‖t‖ < min η 1 → ∀ (k : Fin 3)
      (y : EuclideanSpace ℝ (Fin 2)),
      d 0 < levelOf (chartPert ((blk k) t) (diskPlane (linPlaneChart Phi1t cl hcl) y)) :=
    fun t ht k y => lt_levelOf_chartPert_lin Phi1t cl hcl x hdlt'
      (lt_of_lt_of_le ht (min_le_right _ _)) k y
  have hlevel : ∀ (t : EuclideanSpace ℝ (Fin 12)), ‖t‖ < min η 1 →
      ∀ (j k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
        d 0 < levelOf (chartPert ((blk k) t)
          ((![Pcfg, ![diskPlane (linPlaneChart Phi0t cl hcl), Pcfg 1, Pcfg 2],
              ![diskPlane (linPlaneChart Phi0t cl hcl),
                diskPlane (linPlaneChart Phi1t cl hcl), Pcfg 2]] :
              Fin 3 → Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) j k y)) := by
    intro t ht j k y
    fin_cases j <;> fin_cases k
    · show d 0 < levelOf (chartPert ((blk 0) t) (Pcfg 0 y)); exact hlevP t ht 0 y
    · show d 0 < levelOf (chartPert ((blk 1) t) (Pcfg 1 y)); exact hlevP t ht 1 y
    · show d 0 < levelOf (chartPert ((blk 2) t) (Pcfg 2 y)); exact hlevP t ht 2 y
    · show d 0 < levelOf (chartPert ((blk 0) t) (diskPlane (linPlaneChart Phi0t cl hcl) y))
      exact hL0 t ht 0 y
    · show d 0 < levelOf (chartPert ((blk 1) t) (Pcfg 1 y)); exact hlevP t ht 1 y
    · show d 0 < levelOf (chartPert ((blk 2) t) (Pcfg 2 y)); exact hlevP t ht 2 y
    · show d 0 < levelOf (chartPert ((blk 0) t) (diskPlane (linPlaneChart Phi0t cl hcl) y))
      exact hL0 t ht 0 y
    · show d 0 < levelOf (chartPert ((blk 1) t) (diskPlane (linPlaneChart Phi1t cl hcl) y))
      exact hL1 t ht 1 y
    · show d 0 < levelOf (chartPert ((blk 2) t) (Pcfg 2 y)); exact hlevP t ht 2 y
  -- ## the producer
  obtain ⟨σ, hσε, _, hrow1, hrow2, hrow3⟩ :=
    exists_classRows345_design (Q := Q) Phi0t Phi1t cl hcl Pcfg hPcfg_sm hPcfg_seam hPcfg_inv
      d hdcpos hcdist hc10 hc20 (Metric.ball (0 : EuclideanSpace ℝ (Fin 12)) η)
      Metric.isOpen_ball
      (fun δ hδ => ⟨0, by rw [Metric.mem_ball, dist_self]; exact hη, by simpa using hδ⟩)
      (min η 1) (by positivity) hlevel
  refine ⟨σ, lt_of_lt_of_le hσε (min_le_left _ _), ?_, ?_, ?_⟩
  · -- the design's own triple row
    simpa only [TripleRowsFam, hPcfgdef, sweepRowsBase_zero, sweepRowsBase_one, sweepRowsBase_two,
      slotIdx_zero, slotIdx_one, slotIdx_two] using hrow1
  · -- the `lin₀ P̂₁ P̂₂` row
    have h3 : planeClassMap (diskPlane (linPlaneChart
          (((Φ 0).trans (classEquiv ((blk 0) x))).trans (classEquiv ((blk 0) σ))) cl hcl))
        = planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) =>
            chartPert ((blk 0) σ) (chartPert ((blk 0) x)
              (diskPlane (linPlaneChart (Φ 0) cl hcl) y))) :=
      linTransClass_trans (Φ 0) ((blk 0) σ) ((blk 0) x) cl hcl
    rw [hPhi0t, h3] at hrow2
    simpa only [TripleRowsFam, hPcfgdef, sweepRowsBase_one, sweepRowsBase_two, sweepRowsBase_three,
      slotIdx_one, slotIdx_two, slotIdx_three] using hrow2
  · -- the `lin₁ lin₀ P̂₂` row
    have h3 : planeClassMap (diskPlane (linPlaneChart
          (((Φ 0).trans (classEquiv ((blk 0) x))).trans (classEquiv ((blk 0) σ))) cl hcl))
        = planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) =>
            chartPert ((blk 0) σ) (chartPert ((blk 0) x)
              (diskPlane (linPlaneChart (Φ 0) cl hcl) y))) :=
      linTransClass_trans (Φ 0) ((blk 0) σ) ((blk 0) x) cl hcl
    have h4 : planeClassMap (diskPlane (linPlaneChart
          (((Φ 1).trans (classEquiv ((blk 1) x))).trans (classEquiv ((blk 1) σ))) cl hcl))
        = planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) =>
            chartPert ((blk 1) σ) (chartPert ((blk 1) x)
              (diskPlane (linPlaneChart (Φ 1) cl hcl) y))) :=
      linTransClass_trans (Φ 1) ((blk 1) σ) ((blk 1) x) cl hcl
    rw [hPhi0t, hPhi1t, h3, h4] at hrow3
    simpa only [TripleRowsFam, hPcfgdef, sweepRowsBase_two, sweepRowsBase_three, sweepRowsBase_four,
      slotIdx_two, slotIdx_three, slotIdx_four] using hrow3

/-! ## 6. Joint smoothness and affine invariance of the design's presentation families -/

/-- **Joint smoothness** of a chart-perturbed plane presentation in the design parameter and the plane
parameter. -/
lemma smoothPlaneFam_chartPert_block (k : Fin 3) {P : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (hP : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P) :
    SmoothPlaneFam (fun t y => chartPert ((blk k) t) (P y)) := by
  have h1 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2)))
      (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2) => (blk k) q.1) :=
    contMDiff_iff_contDiff.mpr (by fun_prop)
  have h2 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2)))
      (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2) => P q.2) :=
    hP.comp (contMDiff_iff_contDiff.mpr (by fun_prop))
  have hmain := contMDiff_chartPert.comp (h1.prodMk h2)
  refine hmain.congr fun q => ?_
  simp only [Function.comp_apply, SmoothPlaneFam, IsSmoothFam₂]

/-- **Affine invariance** of a chart-perturbed plane presentation, from that of the presentation. -/
lemma affRep_chartPert_block (k : Fin 3) {P : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (hinv : ∀ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ), (∀ i : Fin 2, e i = 1 ∨ e i = -1) →
      ∀ y : EuclideanSpace ℝ (Fin 2), P (affRep e mm y) = P y)
    (t : EuclideanSpace ℝ (Fin 12)) (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ)
    (he : ∀ i : Fin 2, e i = 1 ∨ e i = -1) (y : EuclideanSpace ℝ (Fin 2)) :
    chartPert ((blk k) t) (P (affRep e mm y)) = chartPert ((blk k) t) (P y) :=
  congrArg (chartPert ((blk k) t)) (hinv e mm he y)

/-- The level band of a perturbed block presentation (`‖t‖ < 1`). -/
lemma lt_levelOf_blockPresentation {Q : ℂ → CappingSpace} {c c0 : ℝ}
    (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p) (x : EuclideanSpace ℝ (Fin 12))
    (hc0 : c0 < c * Real.exp (-(1 + ‖x‖))) (u : UnitAddCircle)
    {t : EuclideanSpace ℝ (Fin 12)} (ht : ‖t‖ < 1) (k : Fin 3)
    (y : EuclideanSpace ℝ (Fin 2)) :
    c0 < levelOf (chartPert ((blk k) t) (rotPresentation Q u y)) := by
  have h1 : levelOf (chartPert ((blk k) t) (rotPresentation Q u y))
      = levelOf (rotPresentation Q u y) * Real.exp (((blk k) t).ofLp 0) :=
    levelOf_chartPert_mul _ _
  have hbase := lt_levelOf_rotPresentation hcbot u y
  have ht0 : Real.exp (-(1 : ℝ)) ≤ Real.exp (((blk k) t).ofLp 0) :=
    Real.exp_le_exp.mpr (by
      have h := exp_coord_blk_ge k t
      have h2 : -‖t‖ ≤ ((blk k) t).ofLp 0 := Real.exp_le_exp.mp h
      linarith)
  have h2 : Real.exp (-(1 + ‖x‖)) ≤ Real.exp (((blk k) t).ofLp 0) :=
    le_trans (Real.exp_le_exp.mpr (by linarith [norm_nonneg x])) ht0
  rw [h1]
  exact lt_of_lt_of_le hc0 (mul_le_mul hbase.le h2 (Real.exp_pos _).le (levelOf_pos _).le)

/-! ## 7. The block bookkeeping of a move in one block -/

/-- A move concentrated in one block: adding `blkSpan i σ` changes the block `i` by `σ` and leaves the
other two blocks unchanged. -/
lemma blk_add_blkSpan_crs (t : EuclideanSpace ℝ (Fin 12)) (i j : Fin 3)
    (σ : EuclideanSpace ℝ (Fin 4)) :
    blk j (t + blkSpan i σ) = blk j t + (if j = i then σ else 0) := by
  rw [map_add]
  by_cases h : j = i
  · subst h; rw [blk_blkSpan, if_pos rfl]
  · rw [blk_blkSpan_of_ne h, if_neg h, add_zero]

/-! ## 8. The openness of the four sweep rows as a set of design parameters -/

/-- **The three end-triple rows of the design's quintuple are an open condition** on the design
parameter. -/
theorem isOpen_designTripleRows (Q : ℂ → CappingSpace) (hQsm : IsSmoothChart Q)
    (a c' : UnitAddCircle) (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl) :
    IsOpen {t : EuclideanSpace ℝ (Fin 12) |
      TripleRowsFam (sweepRowsPresentations Q a c' Φ cl hcl t)} := by
  -- the three families
  have hsmBase : ∀ j : Fin 5, SmoothPlaneFam (fun t : EuclideanSpace ℝ (Fin 12) =>
      sweepRowsPresentations Q a c' Φ cl hcl t j) := by
    intro j
    refine (smoothPlaneFam_chartPert_block (slotIdx j) ?_)
    fin_cases j
    · exact contMDiff_rotPresentation Q (designAngles a c' 0) (contMDiff_diskPlane hQsm)
    · exact contMDiff_rotPresentation Q (designAngles a c' 1) (contMDiff_diskPlane hQsm)
    · exact contMDiff_rotPresentation Q (designAngles a c' 2) (contMDiff_diskPlane hQsm)
    · exact contMDiff_diskPlane (linPlaneChart_contMDiff (Φ 0) cl hcl)
    · exact contMDiff_diskPlane (linPlaneChart_contMDiff (Φ 1) cl hcl)
  have hinvBase : ∀ (j : Fin 5) (t : EuclideanSpace ℝ (Fin 12)) (e : Fin 2 → ℝ)
      (mm : Fin 2 → ℤ), (∀ i : Fin 2, e i = 1 ∨ e i = -1) →
      ∀ y : EuclideanSpace ℝ (Fin 2),
        sweepRowsPresentations Q a c' Φ cl hcl t j (affRep e mm y)
          = sweepRowsPresentations Q a c' Φ cl hcl t j y := by
    intro j t e mm he y
    exact congrArg (chartPert (blk (slotIdx j) t))
      (sweepRowsBase_affRep Q a c' Φ cl hcl j e mm he y)
  -- the three rows
  have hA : IsOpen {t : EuclideanSpace ℝ (Fin 12) | EndTripleReg
      (planeClassMap (sweepRowsPresentations Q a c' Φ cl hcl t 0))
      (planeClassMap (sweepRowsPresentations Q a c' Φ cl hcl t 1))
      (planeClassMap (sweepRowsPresentations Q a c' Φ cl hcl t 2))} := by
    have h := isOpen_endTripleReg_family_of_affRep
      (fun t : EuclideanSpace ℝ (Fin 12) =>
        ![sweepRowsPresentations Q a c' Φ cl hcl t 0, sweepRowsPresentations Q a c' Φ cl hcl t 1,
          sweepRowsPresentations Q a c' Φ cl hcl t 2])
      (by intro k; fin_cases k <;> exact hsmBase _)
      (by intro t e mm he k y; fin_cases k <;> exact hinvBase _ t e mm he y)
    simpa only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] using h
  have hB : IsOpen {t : EuclideanSpace ℝ (Fin 12) | EndTripleReg
      (planeClassMap (sweepRowsPresentations Q a c' Φ cl hcl t 3))
      (planeClassMap (sweepRowsPresentations Q a c' Φ cl hcl t 1))
      (planeClassMap (sweepRowsPresentations Q a c' Φ cl hcl t 2))} := by
    have h := isOpen_endTripleReg_family_of_affRep
      (fun t : EuclideanSpace ℝ (Fin 12) =>
        ![sweepRowsPresentations Q a c' Φ cl hcl t 3, sweepRowsPresentations Q a c' Φ cl hcl t 1,
          sweepRowsPresentations Q a c' Φ cl hcl t 2])
      (by intro k; fin_cases k <;> exact hsmBase _)
      (by intro t e mm he k y; fin_cases k <;> exact hinvBase _ t e mm he y)
    simpa only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] using h
  have hC : IsOpen {t : EuclideanSpace ℝ (Fin 12) | EndTripleReg
      (planeClassMap (sweepRowsPresentations Q a c' Φ cl hcl t 4))
      (planeClassMap (sweepRowsPresentations Q a c' Φ cl hcl t 3))
      (planeClassMap (sweepRowsPresentations Q a c' Φ cl hcl t 2))} := by
    have h := isOpen_endTripleReg_family_of_affRep
      (fun t : EuclideanSpace ℝ (Fin 12) =>
        ![sweepRowsPresentations Q a c' Φ cl hcl t 4, sweepRowsPresentations Q a c' Φ cl hcl t 3,
          sweepRowsPresentations Q a c' Φ cl hcl t 2])
      (by intro k; fin_cases k <;> exact hsmBase _)
      (by intro t e mm he k y; fin_cases k <;> exact hinvBase _ t e mm he y)
    simpa only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] using h
  have hset : {t : EuclideanSpace ℝ (Fin 12) |
        TripleRowsFam (sweepRowsPresentations Q a c' Φ cl hcl t)}
      = {t : EuclideanSpace ℝ (Fin 12) | EndTripleReg
            (planeClassMap (sweepRowsPresentations Q a c' Φ cl hcl t 0))
            (planeClassMap (sweepRowsPresentations Q a c' Φ cl hcl t 1))
            (planeClassMap (sweepRowsPresentations Q a c' Φ cl hcl t 2))}
        ∩ {t : EuclideanSpace ℝ (Fin 12) | EndTripleReg
            (planeClassMap (sweepRowsPresentations Q a c' Φ cl hcl t 3))
            (planeClassMap (sweepRowsPresentations Q a c' Φ cl hcl t 1))
            (planeClassMap (sweepRowsPresentations Q a c' Φ cl hcl t 2))}
        ∩ {t : EuclideanSpace ℝ (Fin 12) | EndTripleReg
            (planeClassMap (sweepRowsPresentations Q a c' Φ cl hcl t 4))
            (planeClassMap (sweepRowsPresentations Q a c' Φ cl hcl t 3))
            (planeClassMap (sweepRowsPresentations Q a c' Φ cl hcl t 2))} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, TripleRowsFam]
    tauto
  rw [hset]
  exact (hA.inter hB).inter hC

/-- **The pair row of the design's quintuple is an open condition** on the design parameter. -/
theorem isOpen_designPairRow (Q : ℂ → CappingSpace) (hQsm : IsSmoothChart Q)
    (a c' : UnitAddCircle) (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl) :
    IsOpen {t : EuclideanSpace ℝ (Fin 12) |
      PairRowFam (sweepRowsPresentations Q a c' Φ cl hcl t)} := by
  have hsm : ∀ j : Fin 5, SmoothPlaneFam (fun t : EuclideanSpace ℝ (Fin 12) =>
      sweepRowsPresentations Q a c' Φ cl hcl t j) := by
    intro j
    refine (smoothPlaneFam_chartPert_block (slotIdx j) ?_)
    fin_cases j
    · exact contMDiff_rotPresentation Q (designAngles a c' 0) (contMDiff_diskPlane hQsm)
    · exact contMDiff_rotPresentation Q (designAngles a c' 1) (contMDiff_diskPlane hQsm)
    · exact contMDiff_rotPresentation Q (designAngles a c' 2) (contMDiff_diskPlane hQsm)
    · exact contMDiff_diskPlane (linPlaneChart_contMDiff (Φ 0) cl hcl)
    · exact contMDiff_diskPlane (linPlaneChart_contMDiff (Φ 1) cl hcl)
  have hinv : ∀ (j : Fin 5) (t : EuclideanSpace ℝ (Fin 12)) (e : Fin 2 → ℝ)
      (mm : Fin 2 → ℤ), (∀ i : Fin 2, e i = 1 ∨ e i = -1) →
      ∀ y : EuclideanSpace ℝ (Fin 2),
        sweepRowsPresentations Q a c' Φ cl hcl t j (affRep e mm y)
          = sweepRowsPresentations Q a c' Φ cl hcl t j y := by
    intro j t e mm he y
    exact congrArg (chartPert (blk (slotIdx j) t))
      (sweepRowsBase_affRep Q a c' Φ cl hcl j e mm he y)
  exact isOpen_pairReg_family_of_affRep _ _ (hsm 1) (hsm 2) (hinv 1) (hinv 2)

/-! ## 9. The level band with a prescribed bound -/

/-- The level band of a perturbed block presentation, with the bound `‖t‖ ≤ K` and the constant
`c * exp (-K)`. -/
lemma lt_levelOf_blockPresentation_K {Q : ℂ → CappingSpace} {c c0 K : ℝ}
    (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p) (hc0 : c0 < c * Real.exp (-K))
    (u : UnitAddCircle) {t : EuclideanSpace ℝ (Fin 12)} (ht : ‖t‖ ≤ K) (k : Fin 3)
    (y : EuclideanSpace ℝ (Fin 2)) :
    c0 < levelOf (chartPert ((blk k) t) (rotPresentation Q u y)) := by
  have h1 : levelOf (chartPert ((blk k) t) (rotPresentation Q u y))
      = levelOf (rotPresentation Q u y) * Real.exp (((blk k) t).ofLp 0) :=
    levelOf_chartPert_mul _ _
  have hbase := lt_levelOf_rotPresentation hcbot u y
  have h2 : Real.exp (-K) ≤ Real.exp (((blk k) t).ofLp 0) := by
    refine Real.exp_le_exp.mpr ?_
    have h := abs_coord_blk_le k t
    have h' : -|((blk k) t).ofLp 0| ≤ ((blk k) t).ofLp 0 := neg_abs_le _
    linarith [abs_nonneg (((blk k) t).ofLp 0)]
  rw [h1]
  exact lt_of_lt_of_le hc0 (mul_le_mul hbase.le h2 (Real.exp_pos _).le (levelOf_pos _).le)

/-! ## 10. The density of the four sweep rows -/

/-- **The four sweep rows hold at a parameter arbitrarily close to every point of the closed unit
ball.** -/
theorem exists_designRowsSweepAt_near (Q : ℂ → CappingSpace) (hQsm : IsSmoothChart Q)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    {c : ℝ} (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (a c' : UnitAddCircle) (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl) :
    ∀ x : EuclideanSpace ℝ (Fin 12), ‖x‖ ≤ 1 → ∀ δ : ℝ, 0 < δ →
      ∃ t : EuclideanSpace ℝ (Fin 12), ‖t - x‖ < δ ∧
        DesignRowsSweepAt Q a c' Φ cl hcl t := by
  intro x hx δ hδ
  -- ## the three end-triple rows at a parameter near `x`
  obtain ⟨t₁, ht₁, htri₁⟩ := exists_tripleRowsFam_near_qMul (F := sweepRowsBase Q a c' Φ cl hcl)
    (tripleRows_base_near_zero Q hQsm hQseam hc hcbot a c' Φ cl hcl x) (by linarith : 0 < δ / 4)
  -- ## the openness of the three rows at `t₁`
  have htriOpen := isOpen_designTripleRows Q hQsm a c' Φ cl hcl
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp (htriOpen.mem_nhds htri₁)
  -- ## the level data of the pair row
  set K : ℝ := ‖t₁‖ + 1 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  set lam : ℝ := c * Real.exp (-K) / 2 with hlamdef
  set c₂ : ℝ := c * Real.exp (-K) / 4 with hc₂def
  have hlampos : 0 < lam := by rw [hlamdef]; positivity
  have hc₂pos : 0 < c₂ := by rw [hc₂def]; positivity
  have hc₂lam : c₂ < lam := by rw [hc₂def, hlamdef]; linarith
  have hlamlt : lam < c * Real.exp (-K) := by rw [hlamdef]; linarith
  -- ## the loop
  set A₀ : EuclideanSpace ℝ (Fin 2) → CappingSpace :=
    fun y => shadow lam hlampos (chartPert ((blk 1) t₁)
      (rotPresentation Q (designAngles a c' 1) y)) with hA₀def
  have hA₀sm : SmoothPlane₂ A₀ := by
    rw [hA₀def]
    refine (contMDiff_shadow lam hlampos).comp ?_
    exact (contMDiff_apply_of_chartPert (isChartPert_chartPert Q) ((blk 1) t₁)).comp
      (contMDiff_rotPresentation Q (designAngles a c' 1) (contMDiff_diskPlane hQsm))
  have hA₀lev : ∀ u ∈ Submission.Drive.unitBox 1, c₂ < levelOf (A₀ u) := by
    intro u _
    rw [hA₀def]
    simp only [levelOf_shadow]
    exact hc₂lam
  -- ## the Sard for the pair row, centred at `t₁`
  set εp : ℝ := min (min (ρ / 2) (δ / 4)) (1 / 2) with hεpdef
  have hεppos : 0 < εp := by
    rw [hεpdef]; exact lt_min (lt_min (by linarith) (by linarith)) (by norm_num)
  have hεpρ : εp ≤ ρ / 2 := by rw [hεpdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hεpδ : εp ≤ δ / 4 := by rw [hεpdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hεp1 : εp ≤ 1 / 2 := by rw [hεpdef]; exact min_le_right _ _
  obtain ⟨p, hp, hbox⟩ := exists_loopBoxData_of_small_shift_fam (ι := Unit) (m := 4)
    (fun _ : Unit => A₀) (fun _ => hA₀sm) c₂ hc₂pos (fun _ u hu => hA₀lev u hu)
    (fun s p' => chartPert s p') Q (isChartPert_chartPert Q) hQsm
    (designAngles a c' 2) ((blk 2) t₁) εp hεppos
  have hbox₀ := hbox ()
  -- ## the parameter of the pair row
  set t₂ : EuclideanSpace ℝ (Fin 12) := t₁ + blkSpan 2 p with ht₂def
  have ht₂b1 : (blk 1) t₂ = (blk 1) t₁ := by
    rw [ht₂def, blk_add_blkSpan_crs]
    simp
  have ht₂b2 : (blk 2) t₂ = (blk 2) t₁ + p := by
    rw [ht₂def, blk_add_blkSpan_crs]
    simp
  have ht₂K : ‖t₂‖ ≤ K := by
    have h1 : ‖t₂ - t₁‖ = ‖p‖ := by rw [ht₂def, add_sub_cancel_left, norm_blkSpan]
    have h2 : ‖t₂ - t₁‖ ≤ εp := le_of_lt (by rw [h1]; exact hp)
    have h3 : ‖t₂‖ ≤ ‖t₂ - t₁‖ + ‖t₁‖ := by
      have h := norm_add_le (t₂ - t₁) t₁
      rwa [sub_add_cancel] at h
    rw [hKdef]
    linarith
  -- ## the pair row at `t₂`
  have hpair₂ : PairRowFam (sweepRowsPresentations Q a c' Φ cl hcl t₂) := by
    have hlevlam : ∀ y : EuclideanSpace ℝ (Fin 2),
        lam < levelOf (blockPlane (fun s p' => chartPert s p') Q (designAngles a c')
          (fun k => blk k t₂) 2 y) := by
      intro y
      exact lt_levelOf_blockPresentation_K hcbot hlamlt (designAngles a c' 2) ht₂K 2 y
    have hbox' : LoopBoxData
        (fun w => shadow lam hlampos (blockPlane (fun s p' => chartPert s p') Q (designAngles a c')
          (fun k => blk k t₂) 1 w))
        (clampedSweep c₂ (fun s : ℝ => 1 - s)
          (blockPlane (fun s p' => chartPert s p') Q (designAngles a c') (fun k => blk k t₂) 2)) := by
      have hloop : (fun y => shadow lam hlampos (chartPert ((blk 1) t₁)
            (rotPresentation Q (designAngles a c' 1) y)))
          = (fun w => shadow lam hlampos (blockPlane (fun s p' => chartPert s p') Q
              (designAngles a c') (fun k => blk k t₂) 1 w)) := by
        funext y
        simp only [blockPlane]
        rw [ht₂b1]
      have hpres : diskPlane (pertChart (fun s p' => chartPert s p')
            (fun z => rotCapping (designAngles a c' 2) (Q z)) ((blk 2) t₁ + p))
          = blockPlane (fun s p' => chartPert s p') Q (designAngles a c') (fun k => blk k t₂) 2 := by
        funext y
        simp only [blockPlane, diskPlane, pertChart, rotPresentation, Function.comp_apply]
        rw [ht₂b2]
      rw [hA₀def] at hbox₀
      rw [hloop, congrArg (fun P => clampedSweep c₂ (fun s : ℝ => 1 - s) P) hpres] at hbox₀
      exact hbox₀
    have h := pairReg_blockPlane_of_loopBoxData (fun s p' => chartPert s p') Q (designAngles a c')
      (fun k => blk k t₂) 1 2 (isChartPert_chartPert Q) hQsm c₂ hc₂pos lam hlampos hc₂lam hlevlam hbox'
    have hS1 : sweepRowsPresentations Q a c' Φ cl hcl t₂ 1
        = blockPlane (fun s p' => chartPert s p') Q (designAngles a c') (fun k => blk k t₂) 1 := rfl
    have hS2 : sweepRowsPresentations Q a c' Φ cl hcl t₂ 2
        = blockPlane (fun s p' => chartPert s p') Q (designAngles a c') (fun k => blk k t₂) 2 := rfl
    rw [PairRowFam, hS1, hS2]
    exact h
  -- ## conclusion
  refine ⟨t₂, ?_, ?_⟩
  · have h1 : ‖t₂ - t₁‖ ≤ εp := by
      rw [ht₂def, add_sub_cancel_left, norm_blkSpan]
      exact le_of_lt hp
    have h2 : ‖t₂ - x‖ < δ := by
      have h3 : ‖t₂ - x‖ ≤ ‖t₂ - t₁‖ + ‖t₁ - x‖ := by
        have h := norm_add_le (t₂ - t₁) (t₁ - x)
        rwa [sub_add_sub_cancel] at h
      linarith
    exact h2
  · exact (designRowsSweepAt_iff Q a c' Φ cl hcl t₂).mpr
      ⟨hpair₂, hρsub (by
        rw [Metric.mem_ball, dist_eq_norm]
        have h1 : ‖t₂ - t₁‖ ≤ εp := by
          rw [ht₂def, add_sub_cancel_left, norm_blkSpan]
          exact le_of_lt hp
        linarith)⟩

/-- **The four *sweep* rows of the ends clause at a parameter of an open dense-at-every-point set.**

For an injective curve `γ` with a plane chart `Q`, a level `c` above the chart's disk, any linear family
`Φ` and level `cl > 0`, there is an open set `R` of design parameters meeting every ball around every
point of the closed unit ball (`‖x‖ ≤ 1`) on which the four rows `Work.Drive.DesignRowsSweepAt` hold:
the pair row `PairReg P̂₁P̂₂`, the end-triple row `EndTripleReg P̂₀P̂₁P̂₂` of the design's own perturbed
triple, and the two end-triple rows in which one or two slots are the *transported* linear models
`Work.Drive.linTransClass`.

Route (`NOTES_LEAD_hodd_blockT6.md` §3, `HENDL012_ROW_STATUS.md`): each row is a `Meet3Hyp`-of-the-sweeps
statement converted by the bridge `Work.Drive.endTripleReg_of_meet3Hyp_sweeps_unrestricted`
(`Drive/endTripleRegUnrestricted.lean`) or by the `loopBoxData` pair bridges
(`Drive/pairRegRows.lean`):
* the two end-triple rows `{P̂₀P̂₁P̂₂}` and `{lin₀ P̂₁ P̂₂}` come from
  `Work.Drive.exists_classRows345_design` (`Drive/hendL012Row.lean`), with the linear model in the
  transported form `Φ.trans (classEquiv (blk 0 t))` — the form `Work.Drive.linTransClass` has;
* the third row `{lin₁ lin₀ P̂₂}` is the third conjunct of the same producer;
* the pair row `PairReg P̂₁ P̂₂` is `Work.Drive.pairReg_blockPlane_of_loopBoxData`.
The *density at every point* of the parameter is supplied by the re-basing mechanism of
`Drive/classRowRebasing.lean` (the class-level rows only see the class coordinates, and `classMap (a+b)`
agrees with `classMap a ∘ classMap b` up to `O (‖a‖‖b‖)`, so the row sets are open and re-centre at every
base point); the *openness* is the `eventually_*` machinery of the lane
(`Work.Drive.eventually_DiamFamRegBox`, `Work.Drive.eventually_good_meetBox`, …). -/
theorem classRowsSweep_openDense {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    (hγinj : Function.Injective γ)
    {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsPlaneChart γ hγne Q)
    {c : ℝ} (hc : 0 < c)
    (hcbot : ∀ p ∈ Work.Drive.chartDisk Q, c < Work.Drive.levelOf p)
    (hdisjZc : ∀ w : UnitAddCircle, w ∈ Work.Drive.Zc γ →
      Disjoint (Work.Drive.chartDisk Q) (Work.Drive.rotCapping w '' Work.Drive.chartDisk Q))
    (a c' : UnitAddCircle) (ha : a ∈ Work.Drive.Zc γ) (hc' : c' ∈ Work.Drive.Zc γ)
    (hac : a + c' ∈ Work.Drive.Zc γ)
    (Φ : Fin 3 → Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3) (cl : ℝ) (hcl : 0 < cl) :
    ∃ R : Set (EuclideanSpace ℝ (Fin 12)), IsOpen R ∧
      (∀ x : EuclideanSpace ℝ (Fin 12), ‖x‖ ≤ 1 → ∀ δ : ℝ, 0 < δ →
        ∃ y, y ∈ R ∧ ‖y - x‖ < δ) ∧
      (∀ t ∈ R, Work.Drive.DesignRowsSweepAt Q a c' Φ cl hcl t) := by
  have hQd : IsChartData Q := IsChartData_of_isPlaneChart hQ
  have hQsm : IsSmoothChart Q := hQd.1
  have hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z := hQd.2
  refine ⟨{t : EuclideanSpace ℝ (Fin 12) | DesignRowsSweepAt Q a c' Φ cl hcl t}, ?_, ?_,
    fun t ht => ht⟩
  · have hset : {t : EuclideanSpace ℝ (Fin 12) | DesignRowsSweepAt Q a c' Φ cl hcl t}
        = {t : EuclideanSpace ℝ (Fin 12) |
            SweepRowsFam (sweepRowsPresentations Q a c' Φ cl hcl t)} := by
      ext t
      exact designRowsSweepAt_iff Q a c' Φ cl hcl t
    rw [hset]
    have hset2 : {t : EuclideanSpace ℝ (Fin 12) |
          SweepRowsFam (sweepRowsPresentations Q a c' Φ cl hcl t)}
        = {t : EuclideanSpace ℝ (Fin 12) |
            PairRowFam (sweepRowsPresentations Q a c' Φ cl hcl t)}
          ∩ {t : EuclideanSpace ℝ (Fin 12) |
            TripleRowsFam (sweepRowsPresentations Q a c' Φ cl hcl t)} := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, SweepRowsFam]
    rw [hset2]
    exact (isOpen_designPairRow Q hQsm a c' Φ cl hcl).inter
      (isOpen_designTripleRows Q hQsm a c' Φ cl hcl)
  · intro x hx δ hδ
    obtain ⟨t, ht, hrows⟩ :=
      exists_designRowsSweepAt_near Q hQsm hQseam hc hcbot a c' Φ cl hcl x hx δ hδ
    exact ⟨t, hrows, ht⟩

end

end Work.Drive
