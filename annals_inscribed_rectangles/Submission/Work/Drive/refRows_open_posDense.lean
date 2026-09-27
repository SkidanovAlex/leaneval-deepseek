import Mathlib
import Submission.Work.Drive.refParityRows
import Submission.Work.Drive.refRowB_pairReg_openDense
import Submission.Work.Drive.rowCD_linTrans_generalPosition_openDense
import Submission.Work.Drive.classRowsSweep_openDense
import Submission.Work.Drive.rowsOpen
import Submission.Work.Drive.unrestrictedFromBox
import Submission.Work.Drive.pairReg_refPlane_perturb_dense
import Submission.Work.Drive.refTripleProducerDefs
import Submission.Work.Drive.classRowRebasing
import Submission.Work.Drive.chartPertGroup
import Submission.Work.Drive.endTripleRegUnrestricted
import Submission.Work.Drive.refTripleRows
import Submission.Work.Drive.hn2RefParityDefs
import Submission.Work.Drive.chartLevelBound
import Submission.Work.Drive.chartIsSmooth
import Submission.Work.Drive.analyticDensity

/-!
# The row set of the `hn2` reference triple is open and dense at the positive-block points

`Work.Drive.RefParityFamily` needs an open set `R` of parameters `t : ℝ¹²`, dense at every
positive-block point of the closed unit ball, on which the six class-level rows `Work.Drive.RefRows`
and the general-position clause `Work.Drive.RefGP` hold.  This module produces it.

**Level independence.**  Every row of `RefRows` is a condition on the *class maps* of the perturbed
reference triple, and the class map of the chart-perturbed reference plane is level-independent
(`planeClassMap_refPlanePres_eq`).  Hence the whole construction may be run at the canonical level
`lam₀ = max 1 (2c)`, where `c > 0` is a level lying strictly below the chart's disk
(`exists_level_lt_chartDisk`), and transported back to the prescribed positive level `lam`
(`refRows_transfer_lam`).

**The ingredients at the canonical level.**

* the pair row `lin₀lin₁` and the general position come from `refRowB_pairReg_openDense` and
  `rowCD_linTrans_generalPosition_openDense` (open, dense at the whole closed ball);
* the three end-triple rows `P̂₀P̂₁P̂₂`, `lin₀P̂₁P̂₂`, `lin₁lin₀P̂₂` come from the sweep Sard
  (`exists_classRows345_design`), transferred to a neighbourhood of an arbitrary base point by the
  re-basing mechanism (`exists_tripleRowsFam_near_qMul`): `rrTripleRows_dense_near`;
* the two pair rows `lin₀P̂₂` and `P̂₁P̂₂` come from the parametric Sard
  `exists_loopBoxData_of_small_shift_fam` applied to the *two* loops at once (the perturbed linear
  model of block `0` and the perturbed rotated chart of block `1`) against the radial sweep of the
  chart-perturbed reference plane: `rrPairRows_near`.

Every condition is open in the parameter (`isOpen_rrT`, `isOpen_rrS₂`, `isOpen_rrS₃`), so the
conditions are nested: the pair rows first (they move block `2` only), then the two dense-at-ball
conditions, then the three end-triple rows (whose producer works at an arbitrary base point).
-/

namespace Work.Drive

open Manifold Set Filter
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! ## 1. The level independence of the rows -/

/-- The class map of the chart-perturbed reference plane at the level `lam`. -/
def rrRefClass (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam) (τ : Eucl 3) :
    EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3) :=
  planeClassMap (fun y => chartPert τ (refPlanePres φ lam hlam y))

/-- **The class map of the perturbed reference plane is level-independent**: both are the class map of
the linear disk plane of `φ 2` at the level `1`. -/
lemma rrRefClass_eq (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) {lam lam' : ℝ} (h : 0 < lam)
    (h' : 0 < lam') (τ : Eucl 3) : rrRefClass φ lam h τ = rrRefClass φ lam' h' τ := by
  rw [rrRefClass, rrRefClass, planeClassMap_chartPert_comp_rb, planeClassMap_chartPert_comp_rb,
    planeClassMap_refPlanePres_eq φ lam h (c := 1) one_pos,
    planeClassMap_refPlanePres_eq φ lam' h' (c := 1) one_pos]

/-- The class map of the third block of the perturbed reference triple. -/
lemma rrRefBlock_two_eq (Q : ℂ → CappingSpace) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ)
    (hlam : 0 < lam) (u v : UnitAddCircle) (t : EuclideanSpace ℝ (Fin 12)) :
    planeClassMap (refPertBlock Q (refPlanePres φ lam hlam) u v t 2)
      = rrRefClass φ lam hlam (blk 2 t) := by
  unfold refPertBlock rrRefClass
  rw [show refTriple Q (refPlanePres φ lam hlam) u v 2 = refPlanePres φ lam hlam by
    simp [refTriple]]

/-- **`RefRows` only sees the level through the third block's class map**, hence is level-independent
for positive levels (the transfer is stated at the end of this section).
**The six rows of `RefRows` with the third block's class map as a parameter** (the only entry of
the triple whose class map depends on the reference plane's level). -/
def rrRowsC (Q : ℂ → CappingSpace) (u v : UnitAddCircle) (A : Eucl 3 ≃L[ℝ] Eucl 3)
    (C : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (t : EuclideanSpace ℝ (Fin 12)) : Prop :=
  PairReg (linRowModel A t 0) (linRowModel A t 1) ∧
  PairReg (linRowModel A t 0) C ∧
  PairReg (planeClassMap (fun y => chartPert (blk 1 t) (rotPresentation Q v y))) C ∧
  EndTripleReg (planeClassMap (fun y => chartPert (blk 0 t) (rotPresentation Q u y)))
    (planeClassMap (fun y => chartPert (blk 1 t) (rotPresentation Q v y))) C ∧
  EndTripleReg (linRowModel A t 0)
    (planeClassMap (fun y => chartPert (blk 1 t) (rotPresentation Q v y))) C ∧
  EndTripleReg (linRowModel A t 1) (linRowModel A t 0) C

/-- `RefRows` in the parametrised form. -/
lemma refRows_iff_rrRowsC (Q : ℂ → CappingSpace) (u v : UnitAddCircle)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (A : Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    (t : EuclideanSpace ℝ (Fin 12)) :
    RefRows Q u v φ lam hlam A t
      ↔ rrRowsC Q u v A
          (planeClassMap (refPertBlock Q (refPlanePres φ lam hlam) u v t 2)) t :=
  Iff.rfl

lemma refRows_transfer_lam (Q : ℂ → CappingSpace) (u v : UnitAddCircle)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (A : Eucl 3 ≃L[ℝ] Eucl 3) {lam lam' : ℝ}
    (hlam : 0 < lam) (hlam' : 0 < lam') (t : EuclideanSpace ℝ (Fin 12)) :
    RefRows Q u v φ lam hlam A t ↔ RefRows Q u v φ lam' hlam' A t := by
  have h : planeClassMap (refPertBlock Q (refPlanePres φ lam hlam) u v t 2)
      = planeClassMap (refPertBlock Q (refPlanePres φ lam' hlam') u v t 2) := by
    rw [rrRefBlock_two_eq, rrRefBlock_two_eq, rrRefClass_eq]
  rw [refRows_iff_rrRowsC Q u v φ A lam hlam t,
    refRows_iff_rrRowsC Q u v φ A lam' hlam' t, h]

/-! ## 2. The five base presentations of the reference-triple rows -/

/-- The five *base* presentations: the two rotated charts of `Q`, the reference plane, and the two
linear disk models of `A₁` (at level `1`). -/
def rrPBase (Q : ℂ → CappingSpace) (R : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (u v : UnitAddCircle) (A₁ : Eucl 3 ≃L[ℝ] Eucl 3) :
    Fin 5 → EuclideanSpace ℝ (Fin 2) → CappingSpace :=
  ![rotPresentation Q u, rotPresentation Q v, R,
    diskPlane (linPlaneChart (linBase A₁ 0) 1 one_pos),
    diskPlane (linPlaneChart (linBase A₁ 1) 1 one_pos)]

@[simp] lemma rrPBase_zero (Q : ℂ → CappingSpace) (R : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (u v : UnitAddCircle) (A₁ : Eucl 3 ≃L[ℝ] Eucl 3) :
    rrPBase Q R u v A₁ 0 = rotPresentation Q u := rfl

@[simp] lemma rrPBase_one (Q : ℂ → CappingSpace) (R : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (u v : UnitAddCircle) (A₁ : Eucl 3 ≃L[ℝ] Eucl 3) :
    rrPBase Q R u v A₁ 1 = rotPresentation Q v := rfl

@[simp] lemma rrPBase_two (Q : ℂ → CappingSpace) (R : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (u v : UnitAddCircle) (A₁ : Eucl 3 ≃L[ℝ] Eucl 3) :
    rrPBase Q R u v A₁ 2 = R := rfl

@[simp] lemma rrPBase_three (Q : ℂ → CappingSpace) (R : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (u v : UnitAddCircle) (A₁ : Eucl 3 ≃L[ℝ] Eucl 3) :
    rrPBase Q R u v A₁ 3 = diskPlane (linPlaneChart (linBase A₁ 0) 1 one_pos) := rfl

@[simp] lemma rrPBase_four (Q : ℂ → CappingSpace) (R : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (u v : UnitAddCircle) (A₁ : Eucl 3 ≃L[ℝ] Eucl 3) :
    rrPBase Q R u v A₁ 4 = diskPlane (linPlaneChart (linBase A₁ 1) 1 one_pos) := rfl

/-- The five presentations at the parameter `t`. -/
def rrPPres (Q : ℂ → CappingSpace) (R : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (u v : UnitAddCircle) (A₁ : Eucl 3 ≃L[ℝ] Eucl 3) (t : EuclideanSpace ℝ (Fin 12)) :
    Fin 5 → EuclideanSpace ℝ (Fin 2) → CappingSpace :=
  fun j y => chartPert (blk (slotIdx j) t) (rrPBase Q R u v A₁ j y)

/-- **The three end-triple rows** of the perturbed reference triple at a positive level. -/
def rrT (Q : ℂ → CappingSpace) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    (u v : UnitAddCircle) (A : Eucl 3 ≃L[ℝ] Eucl 3) : Set (EuclideanSpace ℝ (Fin 12)) :=
  {t | TripleRowsFam (rrPPres Q (refPlanePres φ lam hlam) u v A t)}

/-- **The pair row `lin₀ P̂₂`** of the perturbed reference triple at a positive level. -/
def rrS₂ (Q : ℂ → CappingSpace) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    (u v : UnitAddCircle) (A : Eucl 3 ≃L[ℝ] Eucl 3) : Set (EuclideanSpace ℝ (Fin 12)) :=
  {t | PairReg (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A t 3))
    (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A t 2))}

/-- **The pair row `P̂₁ P̂₂`** of the perturbed reference triple at a positive level. -/
def rrS₃ (Q : ℂ → CappingSpace) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    (u v : UnitAddCircle) (A : Eucl 3 ≃L[ℝ] Eucl 3) : Set (EuclideanSpace ℝ (Fin 12)) :=
  {t | PairRowFam (rrPPres Q (refPlanePres φ lam hlam) u v A t)}

/-! ## 3. The level band of the re-based reference blocks -/

/-- The level of a doubly chart-perturbed *linear disk* plane: the two chart perturbations multiply
the level by `exp ((blk k x) 0) * exp ((blk k t) 0) ≥ exp (-(1 + ‖x‖))` when `‖t‖ < 1`. -/
lemma rr_lt_levelOf_rebased_lin {Ψ : Eucl 3 ≃L[ℝ] Eucl 3} {c' : ℝ} (hc' : 0 < c')
    (x : EuclideanSpace ℝ (Fin 12)) {c0 : ℝ} (hc0 : c0 < c' * Real.exp (-(1 + ‖x‖)))
    {t : EuclideanSpace ℝ (Fin 12)} (ht : ‖t‖ < 1) (k : Fin 3)
    (y : EuclideanSpace ℝ (Fin 2)) :
    c0 < levelOf (chartPert ((blk k) t)
      (chartPert ((blk k) x) (diskPlane (linPlaneChart Ψ c' hc') y))) := by
  have hbase : levelOf (diskPlane (linPlaneChart Ψ c' hc') y) = c' := by
    show ((cappingSpaceHomeoProj (diskPlane (linPlaneChart Ψ c' hc') y)).1 : ℝ) = c'
    rw [show diskPlane (linPlaneChart Ψ c' hc') y
        = linPlaneChart Ψ c' hc' (sqDisk (foldBox y)) from rfl, level_linPlaneChart]
  have h1 : levelOf (chartPert ((blk k) t)
      (chartPert ((blk k) x) (diskPlane (linPlaneChart Ψ c' hc') y)))
      = c' * (Real.exp (((blk k) x).ofLp 0) * Real.exp (((blk k) t).ofLp 0)) := by
    rw [levelOf_chartPert_mul, levelOf_chartPert_mul, hbase]
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
  exact lt_of_lt_of_le hc0 (mul_le_mul_of_nonneg_left hprod hc'.le)

/-- The level of a re-based *rotated chart* of the curve's chart, for the vector family
`![u, v, v]`. -/
lemma rr_lt_levelOf_rebased_rot {Q : ℂ → CappingSpace} {c c0 : ℝ}
    (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p) (x : EuclideanSpace ℝ (Fin 12))
    (hc0 : c0 < c * Real.exp (-(1 + ‖x‖))) (u v : UnitAddCircle)
    {t : EuclideanSpace ℝ (Fin 12)} (ht : ‖t‖ < 1) (k : Fin 3)
    (y : EuclideanSpace ℝ (Fin 2)) :
    c0 < levelOf (chartPert ((blk k) t)
      (chartPert ((blk k) x) (rotPresentation Q ((![u, v, v] : Fin 3 → UnitAddCircle) k) y))) :=
  lt_levelOf_rebased_block hcbot x hc0 ![u, v, v] ht k y

/-! ## 4. The three end-triple rows at an arbitrary base point -/

/-- **The three end-triple rows of the reference triple at parameters arbitrarily close to `0` for the
*re-based* presentations** — `exists_classRows345_design` applied to the re-based reference triple,
with the functionals transported by `classEquiv (blk · x)`, converted into `TripleRowsFam`. -/
theorem rrTripleRows_base_near_zero {Q : ℂ → CappingSpace} (hQsm : IsSmoothChart Q)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    {c : ℝ} (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (u v : UnitAddCircle) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    (hclam : c < lam) (A₁ : Eucl 3 ≃L[ℝ] Eucl 3) (x : EuclideanSpace ℝ (Fin 12)) :
    ∀ η : ℝ, 0 < η → ∃ σ : EuclideanSpace ℝ (Fin 12), ‖σ‖ < η ∧
      TripleRowsFam (fun j y => chartPert (blk (slotIdx j) σ)
        (chartPert (blk (slotIdx j) x) (rrPBase Q (refPlanePres φ lam hlam) u v A₁ j y))) := by
  intro η hη
  -- ## the three levels
  set d0 : ℝ := min c 1 * Real.exp (-(1 + ‖x‖)) / 4 with hd0def
  have hd0pos : 0 < d0 := by rw [hd0def]; positivity
  have hexp : (0 : ℝ) < Real.exp (-(1 + ‖x‖)) := Real.exp_pos _
  have hmin : min c 1 < lam := lt_of_le_of_lt (min_le_left c 1) hclam
  have hd0lt : d0 < c * Real.exp (-(1 + ‖x‖)) := by
    rw [hd0def]; nlinarith [min_le_left c 1, Real.exp_pos (-(1 + ‖x‖))]
  have hd0lt1 : d0 < (1 : ℝ) * Real.exp (-(1 + ‖x‖)) := by
    rw [hd0def]; nlinarith [min_le_right c 1, Real.exp_pos (-(1 + ‖x‖))]
  have hd0ltR : d0 < lam * Real.exp (-(1 + ‖x‖)) := by
    rw [hd0def]; nlinarith [Real.exp_pos (-(1 + ‖x‖))]
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
  -- ## the transported functionals
  set Phi0t : Eucl 3 ≃L[ℝ] Eucl 3 := (linBase A₁ 0).trans (classEquiv ((blk 0) x)) with hPhi0t
  set Phi1t : Eucl 3 ≃L[ℝ] Eucl 3 := (linBase A₁ 1).trans (classEquiv ((blk 1) x)) with hPhi1t
  -- ## the re-based block presentations
  set Pcfg : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace :=
    fun k y => chartPert ((blk k) x)
      (rrPBase Q (refPlanePres φ lam hlam) u v A₁ (Fin.castLE (by norm_num) k) y)
    with hPcfgdef
  have hPcfg0 : Pcfg 0 = fun y => chartPert ((blk 0) x) (rotPresentation Q u y) := by
    funext y; simp [hPcfgdef]
  have hPcfg1 : Pcfg 1 = fun y => chartPert ((blk 1) x) (rotPresentation Q v y) := by
    funext y; simp [hPcfgdef]
  have hPcfg2 : Pcfg 2 = fun y => chartPert ((blk 2) x) (refPlanePres φ lam hlam y) := by
    funext y; simp [hPcfgdef]
  have hPcfg_sm : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (Pcfg k) := by
    intro k
    have hΞ' : ChartPert Q 4 (fun s p => chartPert s p) := isChartPert_chartPert Q
    have h := contMDiff_apply_of_chartPert hΞ' ((blk k) x)
    rw [hPcfgdef]
    refine h.comp ?_
    rcases htriple k with hk | hk | hk
    · rw [hk]; simpa using contMDiff_rotPresentation Q u (contMDiff_diskPlane hQsm)
    · rw [hk]; simpa using contMDiff_rotPresentation Q v (contMDiff_diskPlane hQsm)
    · rw [hk]; simpa using refPlanePres_contMDiff φ lam hlam
  have hPcfg_seam : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      onSeam2 y → Pcfg k y = Pcfg k (seamInv2 y) := by
    intro k y hy
    rw [hPcfgdef]
    refine congrArg (chartPert ((blk k) x)) ?_
    rcases htriple k with hk | hk | hk
    · rw [hk]; simpa using rotPresentation_seamInv Q hQseam u y hy
    · rw [hk]; simpa using rotPresentation_seamInv Q hQseam v y hy
    · rw [hk]; simpa using refPlanePres_seam φ lam hlam y hy
  have hPcfg_inv : ∀ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ), (∀ i : Fin 2, e i = 1 ∨ e i = -1) →
      ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), Pcfg k (affRep e mm y) = Pcfg k y := by
    intro e mm he k y
    rw [hPcfgdef]
    refine congrArg (chartPert ((blk k) x)) ?_
    rcases htriple k with hk | hk | hk
    · rw [hk]; simpa using rotPresentation_affRep he mm Q u y
    · rw [hk]; simpa using rotPresentation_affRep he mm Q v y
    · rw [hk]
      show refPlanePres φ lam hlam (affRep e mm y) = refPlanePres φ lam hlam y
      simp only [refPlanePres] at *
      exact diskPlane_affRep he mm _ y
  -- ## the level hypotheses
  have hlevP : ∀ (t : EuclideanSpace ℝ (Fin 12)), ‖t‖ < min η 1 → ∀ (k : Fin 3)
      (y : EuclideanSpace ℝ (Fin 2)),
      d 0 < levelOf (chartPert ((blk k) t) (Pcfg k y)) := by
    intro t ht k y
    have ht1 : ‖t‖ < 1 := lt_of_lt_of_le ht (min_le_right _ _)
    rw [hPcfgdef]
    rcases htriple k with hk | hk | hk
    · rw [hk]
      exact rr_lt_levelOf_rebased_rot hcbot x (by rw [hd0']; exact hd0lt) u v ht1 0 y
    · rw [hk]
      exact rr_lt_levelOf_rebased_rot hcbot x (by rw [hd0']; exact hd0lt) u v ht1 1 y
    · rw [hk]
      exact rr_lt_levelOf_rebased_lin hlam x (by rw [hd0']; exact hd0ltR) ht1 2 y
  have hL0 : ∀ (t : EuclideanSpace ℝ (Fin 12)), ‖t‖ < min η 1 → ∀ (k : Fin 3)
      (y : EuclideanSpace ℝ (Fin 2)),
      d 0 < levelOf (chartPert ((blk k) t) (diskPlane (linPlaneChart Phi0t 1 one_pos) y)) :=
    fun t ht k y => lt_levelOf_chartPert_lin Phi0t 1 one_pos x (by rw [hd0']; exact hd0lt1)
      (lt_of_lt_of_le ht (min_le_right _ _)) k y
  have hL1 : ∀ (t : EuclideanSpace ℝ (Fin 12)), ‖t‖ < min η 1 → ∀ (k : Fin 3)
      (y : EuclideanSpace ℝ (Fin 2)),
      d 0 < levelOf (chartPert ((blk k) t) (diskPlane (linPlaneChart Phi1t 1 one_pos) y)) :=
    fun t ht k y => lt_levelOf_chartPert_lin Phi1t 1 one_pos x (by rw [hd0']; exact hd0lt1)
      (lt_of_lt_of_le ht (min_le_right _ _)) k y
  have hlevel : ∀ (t : EuclideanSpace ℝ (Fin 12)), ‖t‖ < min η 1 →
      ∀ (j k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
        d 0 < levelOf (chartPert ((blk k) t)
          ((![Pcfg, ![diskPlane (linPlaneChart Phi0t 1 one_pos), Pcfg 1, Pcfg 2],
              ![diskPlane (linPlaneChart Phi0t 1 one_pos),
                diskPlane (linPlaneChart Phi1t 1 one_pos), Pcfg 2]] :
              Fin 3 → Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) j k y)) := by
    intro t ht j k y
    fin_cases j <;> fin_cases k
    · exact hlevP t ht 0 y
    · exact hlevP t ht 1 y
    · exact hlevP t ht 2 y
    · exact hL0 t ht 0 y
    · exact hlevP t ht 1 y
    · exact hlevP t ht 2 y
    · exact hL0 t ht 0 y
    · exact hL1 t ht 1 y
    · exact hlevP t ht 2 y
  -- ## the producer
  obtain ⟨σ, hσε, _hσA, hrow1, hrow2, hrow3⟩ :=
    exists_classRows345_design (Q := Q) Phi0t Phi1t 1 one_pos Pcfg hPcfg_sm hPcfg_seam hPcfg_inv
      d hdcpos hcdist hc10 hc20 (Metric.ball (0 : EuclideanSpace ℝ (Fin 12)) η)
      Metric.isOpen_ball
      (fun δ hδ => ⟨0, by rw [Metric.mem_ball, dist_self]; exact hη, by simpa using hδ⟩)
      (min η 1) (by positivity) hlevel
  refine ⟨σ, lt_of_lt_of_le hσε (min_le_left _ _), ?_, ?_, ?_⟩
  · -- the reference triple's own EndTripleReg row
    rw [hPcfg0, hPcfg1, hPcfg2] at hrow1
    simpa only [TripleRowsFam, rrPBase_zero, rrPBase_one, rrPBase_two,
      slotIdx_zero, slotIdx_one, slotIdx_two] using hrow1
  · -- the `lin₀ P̂₁ P̂₂` row
    have h3 : planeClassMap (diskPlane (linPlaneChart
          (((linBase A₁ 0).trans (classEquiv ((blk 0) x))).trans (classEquiv ((blk 0) σ)))
          1 one_pos))
        = planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) =>
            chartPert ((blk 0) σ) (chartPert ((blk 0) x)
              (diskPlane (linPlaneChart (linBase A₁ 0) 1 one_pos) y))) :=
      linTransClass_trans (linBase A₁ 0) ((blk 0) σ) ((blk 0) x) 1 one_pos
    rw [hPcfg1, hPcfg2, hPhi0t, h3] at hrow2
    simpa only [TripleRowsFam, rrPBase_one, rrPBase_two, rrPBase_three,
      slotIdx_one, slotIdx_two, slotIdx_three] using hrow2
  · -- the `lin₁ lin₀ P̂₂` row
    have h3 : planeClassMap (diskPlane (linPlaneChart
          (((linBase A₁ 0).trans (classEquiv ((blk 0) x))).trans (classEquiv ((blk 0) σ)))
          1 one_pos))
        = planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) =>
            chartPert ((blk 0) σ) (chartPert ((blk 0) x)
              (diskPlane (linPlaneChart (linBase A₁ 0) 1 one_pos) y))) :=
      linTransClass_trans (linBase A₁ 0) ((blk 0) σ) ((blk 0) x) 1 one_pos
    have h4 : planeClassMap (diskPlane (linPlaneChart
          (((linBase A₁ 1).trans (classEquiv ((blk 1) x))).trans (classEquiv ((blk 1) σ)))
          1 one_pos))
        = planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) =>
            chartPert ((blk 1) σ) (chartPert ((blk 1) x)
              (diskPlane (linPlaneChart (linBase A₁ 1) 1 one_pos) y))) :=
      linTransClass_trans (linBase A₁ 1) ((blk 1) σ) ((blk 1) x) 1 one_pos
    rw [hPcfg2, hPhi0t, hPhi1t, h3, h4] at hrow3
    simpa only [TripleRowsFam, rrPBase_two, rrPBase_three, rrPBase_four,
      slotIdx_two, slotIdx_three, slotIdx_four] using hrow3

/-! ## 5. The triple row set is dense at every point -/

/-- **The three end-triple rows hold at parameters arbitrarily close to any base point** — the
re-basing transfer `exists_tripleRowsFam_near_qMul` applied to `rrTripleRows_base_near_zero`. -/
lemma rrTripleRows_dense_near {Q : ℂ → CappingSpace} (hQsm : IsSmoothChart Q)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    {c : ℝ} (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (u v : UnitAddCircle) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    (hclam : c < lam) (A₁ : Eucl 3 ≃L[ℝ] Eucl 3) (x : EuclideanSpace ℝ (Fin 12))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ t, ‖t - x‖ < δ ∧ TripleRowsFam (rrPPres Q (refPlanePres φ lam hlam) u v A₁ t) :=
  exists_tripleRowsFam_near_qMul (F := rrPBase Q (refPlanePres φ lam hlam) u v A₁)
    (rrTripleRows_base_near_zero hQsm hQseam hc hcbot u v φ lam hlam hclam A₁ x) hδ

/-! ## 6. The pair rows by the parametric Sard in block `2` -/

/-- **The two pair rows of the reference triple at the same parameter**, from the parametric Sard
`exists_loopBoxData_of_small_shift_fam` applied to the *two* loops (the perturbed linear model of
block `0` and the perturbed rotated chart of block `1`) against the radial sweep of the
chart-perturbed reference plane. -/
theorem rrPairRows_sigma (Q : ℂ → CappingSpace) (hQsm : IsSmoothChart Q) (v : UnitAddCircle)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    (A₁ : Eucl 3 ≃L[ℝ] Eucl 3) (τ₀ τ₁ ρ : Eucl 3) (hρ : 0 < ρ 0)
    (c₂ : ℝ) (hc₂ : 0 < c₂) (hcl : c₂ < lam) (ε : ℝ) (hε : 0 < ε) :
    ∃ σ : Eucl 3, ‖σ‖ < ε ∧ 0 < (ρ + σ) 0 ∧
      PairReg (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => chartPert τ₀
          (diskPlane (linPlaneChart (linBase A₁ 0) 1 one_pos) y)))
        (planeClassMap (fun y => chartPert (ρ + σ) (refPlanePres φ lam hlam y))) ∧
      PairReg (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) =>
          chartPert τ₁ (rotPresentation Q v y)))
        (planeClassMap (fun y => chartPert (ρ + σ) (refPlanePres φ lam hlam y))) := by
  classical
  have hΞ : ChartPert (linPlaneChart (φ 2) lam hlam) 4 (fun s p => chartPert s p) :=
    isChartPert_chartPert _
  have hQ0 : IsSmoothChart (linPlaneChart (φ 2) lam hlam) :=
    linPlaneChart_contMDiff (φ 2) lam hlam
  let L : Fin 2 → EuclideanSpace ℝ (Fin 2) → CappingSpace :=
    ![(fun y => chartPert τ₀ (diskPlane (linPlaneChart (linBase A₁ 0) 1 one_pos) y)),
      (fun y => chartPert τ₁ (rotPresentation Q v y))]
  have hsm0 : SmoothPlane₂ (fun u : EuclideanSpace ℝ (Fin 2) =>
      chartPert τ₀ (diskPlane (linPlaneChart (linBase A₁ 0) 1 one_pos) u)) :=
    (contMDiff_apply_of_chartPert (isChartPert_chartPert Q) τ₀).comp
      (contMDiff_diskPlane (linPlaneChart_contMDiff (linBase A₁ 0) 1 one_pos))
  have hsm1 : SmoothPlane₂ (fun u : EuclideanSpace ℝ (Fin 2) =>
      chartPert τ₁ (rotPresentation Q v u)) :=
    (contMDiff_apply_of_chartPert (isChartPert_chartPert Q) τ₁).comp
      (contMDiff_rotPresentation Q v (contMDiff_diskPlane hQsm))
  have hLsm : ∀ i : Fin 2, SmoothPlane₂ (fun u => shadow lam hlam (L i u)) := by
    intro i
    fin_cases i
    · change SmoothPlane₂ (fun u => shadow lam hlam
        (chartPert τ₀ (diskPlane (linPlaneChart (linBase A₁ 0) 1 one_pos) u)))
      exact (contMDiff_shadow lam hlam).comp hsm0
    · change SmoothPlane₂ (fun u => shadow lam hlam (chartPert τ₁ (rotPresentation Q v u)))
      exact (contMDiff_shadow lam hlam).comp hsm1
  have hLlev : ∀ (i : Fin 2) (u : EuclideanSpace ℝ (Fin 2)), u ∈ Submission.Drive.unitBox 1 →
      c₂ < levelOf (shadow lam hlam (L i u)) := by
    intro i u _
    rw [levelOf_shadow]
    exact hcl
  obtain ⟨σ, hσ, hbox⟩ := exists_loopBoxData_of_small_shift_fam (m := 4) (ι := Fin 2)
    (fun i => fun u => shadow lam hlam (L i u)) hLsm c₂ hc₂ hLlev (fun s p => chartPert s p)
    (linPlaneChart (φ 2) lam hlam) hΞ hQ0 (0 : UnitAddCircle) ρ
    (min (ε / 2) (ρ 0 / 2)) (lt_min (by linarith) (by linarith))
  have hσlt : ‖σ‖ < ε := lt_of_lt_of_le hσ (le_trans (min_le_left _ _) (by linarith))
  have hσrho : ‖σ‖ < ρ 0 / 2 := lt_of_lt_of_le hσ (min_le_right _ _)
  have hpos : 0 < (ρ + σ) 0 := by
    have h1 : |σ 0| ≤ ‖σ‖ := by
      rw [← Real.norm_eq_abs]
      exact PiLp.norm_apply_le σ (0 : Fin 4)
    have h2 : (ρ + σ) 0 = ρ 0 + σ 0 := by simp
    rw [h2]
    linarith [neg_abs_le (σ 0)]
  -- the box data in the shape the pair bridge consumes
  have hbox' : ∀ i : Fin 2, LoopBoxData (fun u => shadow lam hlam (L i u))
      (clampedSweep c₂ (fun s : ℝ => 1 - s)
        (fun y : EuclideanSpace ℝ (Fin 2) =>
          chartPert (ρ + σ) (refPlanePres φ lam hlam y))) := by
    intro i
    have h := hbox i
    have hrot : (fun z : ℂ => rotCapping (0 : UnitAddCircle) ((linPlaneChart (φ 2) lam hlam) z))
        = fun z : ℂ => (linPlaneChart (φ 2) lam hlam) z := by
      funext z
      simp only [rotCapping_zero, id_eq]
    have hchart : pertChart (fun s p => chartPert s p)
          (fun z : ℂ => rotCapping (0 : UnitAddCircle) ((linPlaneChart (φ 2) lam hlam) z))
          (ρ + σ)
        = fun z : ℂ => chartPert (ρ + σ) ((linPlaneChart (φ 2) lam hlam) z) := by
      rw [hrot]
      rfl
    rw [hchart] at h
    have hdisk : diskPlane (fun z : ℂ => chartPert (ρ + σ)
          ((linPlaneChart (φ 2) lam hlam) z))
        = fun y : EuclideanSpace ℝ (Fin 2) =>
            chartPert (ρ + σ) (refPlanePres φ lam hlam y) := by
      funext y
      rfl
    rw [hdisk] at h
    exact h
  -- the level of the perturbed reference plane is above `lam`
  have hP : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin 2) => chartPert (ρ + σ) (refPlanePres φ lam hlam y)) :=
    (contMDiff_apply_of_chartPert hΞ (ρ + σ)).comp (refPlanePres_contMDiff φ lam hlam)
  have hPinv : ∀ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ), (∀ i, e i = 1 ∨ e i = -1) →
      ∀ y : EuclideanSpace ℝ (Fin 2),
        chartPert (ρ + σ) (refPlanePres φ lam hlam (affRep e mm y))
          = chartPert (ρ + σ) (refPlanePres φ lam hlam y) := by
    intro e mm he y
    refine congrArg (chartPert (ρ + σ)) ?_
    show diskPlane (linPlaneChart (φ 2) lam hlam) (affRep e mm y)
      = diskPlane (linPlaneChart (φ 2) lam hlam) y
    exact diskPlane_affRep he mm _ y
  have hlevlam : ∀ y : EuclideanSpace ℝ (Fin 2),
      lam < levelOf (chartPert (ρ + σ) (refPlanePres φ lam hlam y)) := by
    intro y
    rw [levelOf_chartPert_mul, refPlanePres_level]
    have hexp : 1 < Real.exp ((ρ + σ).ofLp 0) := by
      refine Real.one_lt_exp_iff.mpr ?_
      have h0 : (ρ + σ).ofLp 0 = (ρ + σ) 0 := rfl
      rw [h0]
      exact hpos
    calc lam = lam * 1 := (mul_one lam).symm
      _ < lam * Real.exp ((ρ + σ).ofLp 0) := mul_lt_mul_of_pos_left hexp hlam
  refine ⟨σ, hσlt, hpos, ?_, ?_⟩
  · -- the `lin₀ P̂₂` row
    refine pairReg_of_loopBoxData_affRep
      (fun y : EuclideanSpace ℝ (Fin 2) =>
        chartPert τ₀ (diskPlane (linPlaneChart (linBase A₁ 0) 1 one_pos) y))
      (fun y : EuclideanSpace ℝ (Fin 2) =>
        chartPert (ρ + σ) (refPlanePres φ lam hlam y))
      hsm0 hP ?_ hPinv c₂ hc₂ lam hlam hcl (fun s : ℝ => 1 - s)
      (by norm_num) (by norm_num) continuousOn_designCutoff strictAntiOn_designCutoff hlevlam ?_
    · intro e mm he y
      exact congrArg (chartPert τ₀)
        (diskPlane_affRep he mm (linPlaneChart (linBase A₁ 0) 1 one_pos) y)
    · exact hbox' 0
  · -- the `P̂₁ P̂₂` row
    refine pairReg_of_loopBoxData_affRep
      (fun y : EuclideanSpace ℝ (Fin 2) => chartPert τ₁ (rotPresentation Q v y))
      (fun y : EuclideanSpace ℝ (Fin 2) =>
        chartPert (ρ + σ) (refPlanePres φ lam hlam y))
      hsm1 hP ?_ hPinv c₂ hc₂ lam hlam hcl (fun s : ℝ => 1 - s)
      (by norm_num) (by norm_num) continuousOn_designCutoff strictAntiOn_designCutoff hlevlam ?_
    · intro e mm he y
      exact congrArg (chartPert τ₁) (rotPresentation_affRep he mm Q v y)
    · exact hbox' 1

/-- **The two pair rows hold at a parameter arbitrarily close to a base point with a positive level
coordinate in block `2`.** -/
theorem rrPairRows_near (Q : ℂ → CappingSpace) (hQsm : IsSmoothChart Q) (v : UnitAddCircle)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    (A₁ : Eucl 3 ≃L[ℝ] Eucl 3) (u : UnitAddCircle) (s : EuclideanSpace ℝ (Fin 12))
    (hs : 0 < (blk 2 s) 0) (c₂ : ℝ) (hc₂ : 0 < c₂) (hcl : c₂ < lam)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ t : EuclideanSpace ℝ (Fin 12), ‖t - s‖ < ε ∧
      rrS₂ Q φ lam hlam u v A₁ t ∧ rrS₃ Q φ lam hlam u v A₁ t := by
  obtain ⟨σ, hσ, _hσpos, hrow2, hrow3⟩ :=
    rrPairRows_sigma Q hQsm v φ lam hlam A₁ (blk 0 s) (blk 1 s) (blk 2 s) hs c₂ hc₂ hcl ε hε
  refine ⟨s + blkSpan 2 σ, ?_, ?_, ?_⟩
  · rw [add_sub_cancel_left, norm_blkSpan]
    exact hσ
  · change PairReg (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A₁
        (s + blkSpan 2 σ) 3))
      (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A₁ (s + blkSpan 2 σ) 2))
    have h0 : blk 0 (s + blkSpan 2 σ) = blk 0 s := by rw [blk_add_blkSpan_crs]; simp
    have h2 : blk 2 (s + blkSpan 2 σ) = blk 2 s + σ := by rw [blk_add_blkSpan_crs]; simp
    rw [show rrPPres Q (refPlanePres φ lam hlam) u v A₁ (s + blkSpan 2 σ) 3
        = fun y => chartPert (blk 0 s)
            (diskPlane (linPlaneChart (linBase A₁ 0) 1 one_pos) y) by
      funext y; simp only [rrPPres, rrPBase_three, slotIdx_three, h0]]
    rw [show rrPPres Q (refPlanePres φ lam hlam) u v A₁ (s + blkSpan 2 σ) 2
        = fun y => chartPert (blk 2 s + σ) (refPlanePres φ lam hlam y) by
      funext y; simp only [rrPPres, rrPBase_two, slotIdx_two, h2]]
    exact hrow2
  · change PairReg (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A₁
        (s + blkSpan 2 σ) 1))
      (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A₁ (s + blkSpan 2 σ) 2))
    have h1 : blk 1 (s + blkSpan 2 σ) = blk 1 s := by rw [blk_add_blkSpan_crs]; simp
    have h2 : blk 2 (s + blkSpan 2 σ) = blk 2 s + σ := by rw [blk_add_blkSpan_crs]; simp
    rw [show rrPPres Q (refPlanePres φ lam hlam) u v A₁ (s + blkSpan 2 σ) 1
        = fun y => chartPert (blk 1 s) (rotPresentation Q v y) by
      funext y; simp only [rrPPres, rrPBase_one, slotIdx_one, h1]]
    rw [show rrPPres Q (refPlanePres φ lam hlam) u v A₁ (s + blkSpan 2 σ) 2
        = fun y => chartPert (blk 2 s + σ) (refPlanePres φ lam hlam y) by
      funext y; simp only [rrPPres, rrPBase_two, slotIdx_two, h2]]
    exact hrow3

/-! ## 7. Openness of the row sets -/

/-- Smoothness of the base presentations of the reference-triple rows. -/
lemma contMDiff_rrPBase {Q : ℂ → CappingSpace} (hQsm : IsSmoothChart Q)
    (u v : UnitAddCircle) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    (A₁ : Eucl 3 ≃L[ℝ] Eucl 3) (j : Fin 5) :
    ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (rrPBase Q (refPlanePres φ lam hlam) u v A₁ j) := by
  fin_cases j
  · exact contMDiff_rotPresentation Q u (contMDiff_diskPlane hQsm)
  · exact contMDiff_rotPresentation Q v (contMDiff_diskPlane hQsm)
  · exact refPlanePres_contMDiff φ lam hlam
  · exact contMDiff_diskPlane (linPlaneChart_contMDiff (linBase A₁ 0) 1 one_pos)
  · exact contMDiff_diskPlane (linPlaneChart_contMDiff (linBase A₁ 1) 1 one_pos)

/-- Affine invariance of the base presentations of the reference-triple rows. -/
lemma affRep_rrPBase (Q : ℂ → CappingSpace) (u v : UnitAddCircle)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    (A₁ : Eucl 3 ≃L[ℝ] Eucl 3) (j : Fin 5)
    (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ) (he : ∀ i : Fin 2, e i = 1 ∨ e i = -1)
    (y : EuclideanSpace ℝ (Fin 2)) :
    rrPBase Q (refPlanePres φ lam hlam) u v A₁ j (affRep e mm y)
      = rrPBase Q (refPlanePres φ lam hlam) u v A₁ j y := by
  fin_cases j
  · exact rotPresentation_affRep he mm Q u y
  · exact rotPresentation_affRep he mm Q v y
  · show diskPlane (linPlaneChart (φ 2) lam hlam) (affRep e mm y)
      = diskPlane (linPlaneChart (φ 2) lam hlam) y
    exact diskPlane_affRep he mm _ y
  · show diskPlane (linPlaneChart (linBase A₁ 0) 1 one_pos) (affRep e mm y)
      = diskPlane (linPlaneChart (linBase A₁ 0) 1 one_pos) y
    exact diskPlane_affRep he mm _ y
  · show diskPlane (linPlaneChart (linBase A₁ 1) 1 one_pos) (affRep e mm y)
      = diskPlane (linPlaneChart (linBase A₁ 1) 1 one_pos) y
    exact diskPlane_affRep he mm _ y

/-- **The triple-row set is open.** -/
lemma isOpen_rrT {Q : ℂ → CappingSpace} (hQsm : IsSmoothChart Q) (u v : UnitAddCircle)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    (A₁ : Eucl 3 ≃L[ℝ] Eucl 3) : IsOpen (rrT Q φ lam hlam u v A₁) := by
  have hsm : ∀ j : Fin 5, SmoothPlaneFam
      (fun t : EuclideanSpace ℝ (Fin 12) =>
        rrPPres Q (refPlanePres φ lam hlam) u v A₁ t j) :=
    fun j => smoothPlaneFam_chartPert_block (slotIdx j)
      (contMDiff_rrPBase hQsm u v φ lam hlam A₁ j)
  have hinv : ∀ (j : Fin 5) (t : EuclideanSpace ℝ (Fin 12)) (e : Fin 2 → ℝ)
      (mm : Fin 2 → ℤ), (∀ i : Fin 2, e i = 1 ∨ e i = -1) →
      ∀ y : EuclideanSpace ℝ (Fin 2),
        rrPPres Q (refPlanePres φ lam hlam) u v A₁ t j (affRep e mm y)
          = rrPPres Q (refPlanePres φ lam hlam) u v A₁ t j y :=
    fun j t e mm he y => affRep_chartPert_block (slotIdx j)
      (fun e mm he y => affRep_rrPBase Q u v φ lam hlam A₁ j e mm he y) t e mm he y
  have hA : IsOpen {t : EuclideanSpace ℝ (Fin 12) | EndTripleReg
      (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A₁ t 0))
      (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A₁ t 1))
      (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A₁ t 2))} := by
    have h := isOpen_endTripleReg_family_of_affRep
      (fun t : EuclideanSpace ℝ (Fin 12) =>
        ![(rrPPres Q (refPlanePres φ lam hlam) u v A₁ t 0),
          (rrPPres Q (refPlanePres φ lam hlam) u v A₁ t 1),
          (rrPPres Q (refPlanePres φ lam hlam) u v A₁ t 2)])
      (by intro k; fin_cases k <;> exact hsm _)
      (by intro t e mm he k y; fin_cases k <;> exact hinv _ t e mm he y)
    simpa only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] using h
  have hB : IsOpen {t : EuclideanSpace ℝ (Fin 12) | EndTripleReg
      (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A₁ t 3))
      (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A₁ t 1))
      (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A₁ t 2))} := by
    have h := isOpen_endTripleReg_family_of_affRep
      (fun t : EuclideanSpace ℝ (Fin 12) =>
        ![(rrPPres Q (refPlanePres φ lam hlam) u v A₁ t 3),
          (rrPPres Q (refPlanePres φ lam hlam) u v A₁ t 1),
          (rrPPres Q (refPlanePres φ lam hlam) u v A₁ t 2)])
      (by intro k; fin_cases k <;> exact hsm _)
      (by intro t e mm he k y; fin_cases k <;> exact hinv _ t e mm he y)
    simpa only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] using h
  have hC : IsOpen {t : EuclideanSpace ℝ (Fin 12) | EndTripleReg
      (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A₁ t 4))
      (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A₁ t 3))
      (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A₁ t 2))} := by
    have h := isOpen_endTripleReg_family_of_affRep
      (fun t : EuclideanSpace ℝ (Fin 12) =>
        ![(rrPPres Q (refPlanePres φ lam hlam) u v A₁ t 4),
          (rrPPres Q (refPlanePres φ lam hlam) u v A₁ t 3),
          (rrPPres Q (refPlanePres φ lam hlam) u v A₁ t 2)])
      (by intro k; fin_cases k <;> exact hsm _)
      (by intro t e mm he k y; fin_cases k <;> exact hinv _ t e mm he y)
    simpa only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] using h
  have hset : rrT Q φ lam hlam u v A₁
      = {t : EuclideanSpace ℝ (Fin 12) | EndTripleReg
            (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A₁ t 0))
            (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A₁ t 1))
            (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A₁ t 2))}
        ∩ {t : EuclideanSpace ℝ (Fin 12) | EndTripleReg
            (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A₁ t 3))
            (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A₁ t 1))
            (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A₁ t 2))}
        ∩ {t : EuclideanSpace ℝ (Fin 12) | EndTripleReg
            (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A₁ t 4))
            (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A₁ t 3))
            (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A₁ t 2))} := by
    ext t
    simp only [rrT, Set.mem_ofPred_eq, Set.mem_inter_iff, TripleRowsFam]
    tauto
  rw [hset]
  exact (hA.inter hB).inter hC

/-- **The pair-row set `P̂₁P̂₂` is open.** -/
lemma isOpen_rrS₃ {Q : ℂ → CappingSpace} (hQsm : IsSmoothChart Q) (u v : UnitAddCircle)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    (A₁ : Eucl 3 ≃L[ℝ] Eucl 3) : IsOpen (rrS₃ Q φ lam hlam u v A₁) :=
  isOpen_pairReg_family_of_affRep _ _
    (smoothPlaneFam_chartPert_block 1
      (contMDiff_rrPBase hQsm u v φ lam hlam A₁ 1))
    (smoothPlaneFam_chartPert_block 2
      (contMDiff_rrPBase hQsm u v φ lam hlam A₁ 2))
    (fun t e mm he y => affRep_chartPert_block 1
      (fun e mm he y => affRep_rrPBase Q u v φ lam hlam A₁ 1 e mm he y) t e mm he y)
    (fun t e mm he y => affRep_chartPert_block 2
      (fun e mm he y => affRep_rrPBase Q u v φ lam hlam A₁ 2 e mm he y) t e mm he y)

/-- **The pair-row set `lin₀P̂₂` is open.** -/
lemma isOpen_rrS₂ {Q : ℂ → CappingSpace} (hQsm : IsSmoothChart Q) (u v : UnitAddCircle)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    (A₁ : Eucl 3 ≃L[ℝ] Eucl 3) : IsOpen (rrS₂ Q φ lam hlam u v A₁) :=
  isOpen_pairReg_family_of_affRep _ _
    (smoothPlaneFam_chartPert_block (slotIdx 3)
      (contMDiff_rrPBase hQsm u v φ lam hlam A₁ 3))
    (smoothPlaneFam_chartPert_block (slotIdx 2)
      (contMDiff_rrPBase hQsm u v φ lam hlam A₁ 2))
    (fun t e mm he y => affRep_chartPert_block (slotIdx 3)
      (fun e mm he y => affRep_rrPBase Q u v φ lam hlam A₁ 3 e mm he y) t e mm he y)
    (fun t e mm he y => affRep_chartPert_block (slotIdx 2)
      (fun e mm he y => affRep_rrPBase Q u v φ lam hlam A₁ 2 e mm he y) t e mm he y)

/-! ## 8. The rows of `RefRows` from the four sets -/

lemma rrPres_class_zero (Q : ℂ → CappingSpace) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ)
    (hlam : 0 < lam) (u v : UnitAddCircle) (A : Eucl 3 ≃L[ℝ] Eucl 3)
    (t : EuclideanSpace ℝ (Fin 12)) :
    planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A t 0)
      = planeClassMap (refPertBlock Q (refPlanePres φ lam hlam) u v t 0) := rfl

lemma rrPres_class_one (Q : ℂ → CappingSpace) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ)
    (hlam : 0 < lam) (u v : UnitAddCircle) (A : Eucl 3 ≃L[ℝ] Eucl 3)
    (t : EuclideanSpace ℝ (Fin 12)) :
    planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A t 1)
      = planeClassMap (refPertBlock Q (refPlanePres φ lam hlam) u v t 1) := rfl

lemma rrPres_class_two (Q : ℂ → CappingSpace) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ)
    (hlam : 0 < lam) (u v : UnitAddCircle) (A : Eucl 3 ≃L[ℝ] Eucl 3)
    (t : EuclideanSpace ℝ (Fin 12)) :
    planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A t 2)
      = planeClassMap (refPertBlock Q (refPlanePres φ lam hlam) u v t 2) := rfl

lemma rrPres_class_three (Q : ℂ → CappingSpace) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ)
    (hlam : 0 < lam) (u v : UnitAddCircle) (A : Eucl 3 ≃L[ℝ] Eucl 3)
    (t : EuclideanSpace ℝ (Fin 12)) :
    planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A t 3) = linRowModel A t 0 :=
  planeClassMap_chartPert_diskPlane_linPlaneChart (linBase A 0) 1 one_pos (blk 0 t)

lemma rrPres_class_four (Q : ℂ → CappingSpace) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ)
    (hlam : 0 < lam) (u v : UnitAddCircle) (A : Eucl 3 ≃L[ℝ] Eucl 3)
    (t : EuclideanSpace ℝ (Fin 12)) :
    planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A t 4) = linRowModel A t 1 :=
  planeClassMap_chartPert_diskPlane_linPlaneChart (linBase A 1) 1 one_pos (blk 1 t)

/-- **The six rows of `RefRows` from the four sets of the assembly.** -/
lemma refRows_of_components {Q : ℂ → CappingSpace} {φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3} {lam : ℝ}
    {hlam : 0 < lam} {u v : UnitAddCircle} {A : Eucl 3 ≃L[ℝ] Eucl 3}
    {t : EuclideanSpace ℝ (Fin 12)}
    (hlinear : PairReg (linRowModel A t 0) (linRowModel A t 1))
    (hT : TripleRowsFam (rrPPres Q (refPlanePres φ lam hlam) u v A t))
    (hS₃ : PairRowFam (rrPPres Q (refPlanePres φ lam hlam) u v A t))
    (hS₂ : PairReg (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A t 3))
      (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A t 2))) :
    RefRows Q u v φ lam hlam A t := by
  have hT' : EndTripleReg (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A t 0))
        (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A t 1))
        (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A t 2)) ∧
      EndTripleReg (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A t 3))
        (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A t 1))
        (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A t 2)) ∧
      EndTripleReg (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A t 4))
        (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A t 3))
        (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A t 2)) := hT
  obtain ⟨hT0, hT1, hT2⟩ := hT'
  have hS₃' : PairReg (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A t 1))
      (planeClassMap (rrPPres Q (refPlanePres φ lam hlam) u v A t 2)) := hS₃
  refine ⟨hlinear, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← rrPres_class_three Q φ lam hlam u v A t, ← rrPres_class_two Q φ lam hlam u v A t]
    exact hS₂
  · rw [← rrPres_class_one Q φ lam hlam u v A t, ← rrPres_class_two Q φ lam hlam u v A t]
    exact hS₃
  · rw [← rrPres_class_zero Q φ lam hlam u v A t, ← rrPres_class_one Q φ lam hlam u v A t,
      ← rrPres_class_two Q φ lam hlam u v A t]
    exact hT0
  · rw [← rrPres_class_three Q φ lam hlam u v A t, ← rrPres_class_one Q φ lam hlam u v A t,
      ← rrPres_class_two Q φ lam hlam u v A t]
    exact hT1
  · rw [← rrPres_class_four Q φ lam hlam u v A t, ← rrPres_class_three Q φ lam hlam u v A t,
      ← rrPres_class_two Q φ lam hlam u v A t]
    exact hT2

/-! ## 9. The assembly -/

theorem refRows_open_posDense {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsPlaneChart γ hγne Q)
    (u v : UnitAddCircle) (φ : Fin 3 → Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    (A : Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3) :
    ∃ R : Set (EuclideanSpace ℝ (Fin 12)), IsOpen R ∧
      (∀ s : EuclideanSpace ℝ (Fin 12), ‖s‖ ≤ 1 → Work.Drive.PosBlocks s →
        ∀ δ : ℝ, 0 < δ → ∃ t ∈ R, ‖t - s‖ < δ) ∧
      ∀ t ∈ R, Work.Drive.RefRows Q u v φ lam hlam A t ∧ Work.Drive.RefGP A t := by
  classical
  -- ## 0. the chart data and the level bound below the chart's disk
  have hQd : IsChartData Q := IsChartData_of_isPlaneChart hQ
  have hQsm : IsSmoothChart Q := hQd.1
  have hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z := hQd.2
  obtain ⟨c, hcpos, hcbot⟩ := exists_level_lt_chartDisk hQd.1.continuous
  -- ## 1. the canonical level
  set lam₀ : ℝ := max 1 (2 * c) with hlam₀def
  have hclam₀ : c < lam₀ := by
    rw [hlam₀def]
    rcases lt_or_ge c 1 with h | h
    · exact lt_of_lt_of_le h (le_max_left 1 (2 * c))
    · exact lt_of_lt_of_le (by linarith) (le_max_right 1 (2 * c))
  have hlam₀pos : 0 < lam₀ := lt_trans hcpos hclam₀
  -- ## 2. the four row sets at the canonical level, and the two dense-at-ball sets
  have hTopen : IsOpen (rrT Q φ lam₀ hlam₀pos u v A) :=
    isOpen_rrT hQsm u v φ lam₀ hlam₀pos A
  have hS₃open : IsOpen (rrS₃ Q φ lam₀ hlam₀pos u v A) :=
    isOpen_rrS₃ hQsm u v φ lam₀ hlam₀pos A
  have hS₂open : IsOpen (rrS₂ Q φ lam₀ hlam₀pos u v A) :=
    isOpen_rrS₂ hQsm u v φ lam₀ hlam₀pos A
  obtain ⟨R₁, hR₁open, hR₁dense, hR₁row⟩ := refRowB_pairReg_openDense A 1 one_pos
  obtain ⟨Rg, hGopen, hGdense, hGrow⟩ := rowCD_linTrans_generalPosition_openDense A 1 one_pos
  refine ⟨R₁ ∩ Rg ∩ rrS₂ Q φ lam₀ hlam₀pos u v A ∩ rrS₃ Q φ lam₀ hlam₀pos u v A
      ∩ rrT Q φ lam₀ hlam₀pos u v A, ?_, ?_, ?_⟩
  · -- ## openness
    exact (((hR₁open.inter hGopen).inter hS₂open).inter hS₃open).inter hTopen
  · -- ## density at every positive-block point of the closed unit ball
    intro s hs1 hpos δ hδ
    -- ### (0) a base point strictly inside the ball, with positive blocks
    have hbase : ∃ s' : EuclideanSpace ℝ (Fin 12),
        ‖s'‖ < 1 ∧ PosBlocks s' ∧ ‖s' - s‖ < δ / 8 := by
      by_cases h : ‖s‖ < 1
      · exact ⟨s, h, hpos, by rw [sub_self, norm_zero]; linarith⟩
      · have h1 : ‖s‖ = 1 := le_antisymm hs1 (not_lt.mp h)
        set θ : ℝ := min (δ / 16) (1 / 2) with hθdef
        have hθpos : 0 < θ := lt_min (by linarith) (by norm_num)
        have hθ1 : θ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
        have hθδ : θ < δ / 8 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
        refine ⟨(1 - θ) • s, ?_, ?_, ?_⟩
        · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), h1, mul_one]
          linarith
        · intro k
          have hk : blk k ((1 - θ) • s) = (1 - θ) • blk k s := (blk k).map_smul (1 - θ) s
          have hcoord : (blk k ((1 - θ) • s)) 0 = (1 - θ) * (blk k s) 0 := by
            rw [hk]
            simp
          rw [hcoord]
          exact mul_pos (by linarith) (hpos k)
        · have hsub : (1 - θ) • s - s = (-θ) • s := by rw [sub_smul, one_smul]; module
          rw [hsub, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hθpos, h1, mul_one]
          exact hθδ
    obtain ⟨s', hs'1, hs'pos, hs'd⟩ := hbase
    have hblev : 0 < (blk 2 s') 0 := hs'pos 2
    -- ### (1) the two pair rows at a parameter close to `s'`, strictly inside the unit ball
    have hε₁pos : 0 < min (δ / 8) ((1 - ‖s'‖) / 4) := lt_min (by linarith) (by linarith)
    obtain ⟨t₁, ht₁d, ht₁S₂, ht₁S₃⟩ := rrPairRows_near Q hQsm v φ lam₀ hlam₀pos A u s' hblev
      c hcpos hclam₀ (min (δ / 8) ((1 - ‖s'‖) / 4)) hε₁pos
    have ht₁δ : ‖t₁ - s'‖ < δ / 8 := lt_of_lt_of_le ht₁d (min_le_left _ _)
    have ht₁κ : ‖t₁ - s'‖ < (1 - ‖s'‖) / 4 := lt_of_lt_of_le ht₁d (min_le_right _ _)
    have ht₁norm : ‖t₁‖ < 1 := by
      have hup : ‖t₁‖ ≤ ‖t₁ - s'‖ + ‖s'‖ := by
        have hh := norm_add_le (t₁ - s') s'
        rwa [sub_add_cancel] at hh
      linarith
    -- ### (2) openness of `S₂ ∩ S₃` at `t₁`, and the two dense-at-ball conditions
    obtain ⟨r₁, hr₁pos, hr₁sub⟩ := Metric.isOpen_iff.mp (hS₂open.inter hS₃open) t₁
      ⟨ht₁S₂, ht₁S₃⟩
    have hε₂pos : 0 < min r₁ (δ / 8) := lt_min hr₁pos (by linarith)
    obtain ⟨t₂, ht₂d, ht₂R⟩ :=
      exists_mem_iInter_near_of_denseAtBall (ι := Fin 2)
        (R := fun i : Fin 2 => if i = 0 then R₁ else Rg)
        (by intro i; fin_cases i <;> simp [hR₁open, hGopen])
        (by intro i; fin_cases i <;> simp [hR₁dense, hGdense])
        ht₁norm (min r₁ (δ / 8)) hε₂pos
    have ht₂R₁ : t₂ ∈ R₁ := by simpa using ht₂R 0
    have ht₂Rg : t₂ ∈ Rg := by simpa using ht₂R 1
    have ht₂SS : t₂ ∈ rrS₂ Q φ lam₀ hlam₀pos u v A ∩ rrS₃ Q φ lam₀ hlam₀pos u v A :=
      hr₁sub (by rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_lt_of_le ht₂d (min_le_left _ _))
    have ht₂in : t₂ ∈ R₁ ∩ Rg ∩ rrS₂ Q φ lam₀ hlam₀pos u v A ∩ rrS₃ Q φ lam₀ hlam₀pos u v A :=
      ⟨⟨⟨ht₂R₁, ht₂Rg⟩, ht₂SS.1⟩, ht₂SS.2⟩
    have ht₂δ : ‖t₂ - t₁‖ < δ / 8 := lt_of_lt_of_le ht₂d (min_le_right _ _)
    -- ### (3) openness at `t₂`, and the three end-triple rows
    obtain ⟨r₂, hr₂pos, hr₂sub⟩ := Metric.isOpen_iff.mp
      (((hR₁open.inter hGopen).inter hS₂open).inter hS₃open) t₂ ht₂in
    have hε₃pos : 0 < min r₂ (δ / 8) := lt_min hr₂pos (by linarith)
    obtain ⟨t₃, ht₃d, ht₃T⟩ := rrTripleRows_dense_near hQsm hQseam hcpos hcbot u v φ lam₀
      hlam₀pos hclam₀ A t₂ (δ := min r₂ (δ / 8)) hε₃pos
    have ht₃in : t₃ ∈ R₁ ∩ Rg ∩ rrS₂ Q φ lam₀ hlam₀pos u v A ∩ rrS₃ Q φ lam₀ hlam₀pos u v A :=
      hr₂sub (by rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_lt_of_le ht₃d (min_le_left _ _))
    -- ### (4) the distance bookkeeping
    refine ⟨t₃, ⟨ht₃in, ht₃T⟩, ?_⟩
    have h₁ : ‖t₃ - t₂‖ < δ / 8 := lt_of_lt_of_le ht₃d (min_le_right _ _)
    have h₂ : ‖t₂ - t₁‖ < δ / 8 := ht₂δ
    have h₃ : ‖t₁ - s'‖ < δ / 8 := ht₁δ
    have h₄ : ‖s' - s‖ < δ / 8 := hs'd
    have hsum : ‖t₃ - s‖ ≤ ‖t₃ - t₂‖ + ‖t₂ - t₁‖ + ‖t₁ - s'‖ + ‖s' - s‖ := by
      have h12 : ‖t₃ - s‖ ≤ ‖t₃ - t₂‖ + ‖t₂ - s‖ := by
        have hh := norm_add_le (t₃ - t₂) (t₂ - s); rwa [sub_add_sub_cancel] at hh
      have h23 : ‖t₂ - s‖ ≤ ‖t₂ - t₁‖ + ‖t₁ - s‖ := by
        have hh := norm_add_le (t₂ - t₁) (t₁ - s); rwa [sub_add_sub_cancel] at hh
      have h34 : ‖t₁ - s‖ ≤ ‖t₁ - s'‖ + ‖s' - s‖ := by
        have hh := norm_add_le (t₁ - s') (s' - s); rwa [sub_add_sub_cancel] at hh
      linarith
    linarith
  · -- ## the rows and the general position
    intro t ht
    obtain ⟨⟨⟨⟨ht₁, htg⟩, ht₂⟩, ht₃⟩, htt⟩ := ht
    have hrows₀ : RefRows Q u v φ lam₀ hlam₀pos A t :=
      refRows_of_components (hlam := hlam₀pos)
        (by simpa only [linRowModel] using hR₁row t ht₁) htt ht₃ ht₂
    exact ⟨(refRows_transfer_lam Q u v φ A hlam₀pos hlam t).mp hrows₀,
      hGrow t htg⟩

end

end Work.Drive
