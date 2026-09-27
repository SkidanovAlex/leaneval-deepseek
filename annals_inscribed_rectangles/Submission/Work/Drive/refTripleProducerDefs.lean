import Mathlib
import Submission.Work.Drive.refTripleOneT
import Submission.Work.Drive.planeChartDefs
import Submission.Work.Drive.chartPert_linPlaneChart
import Submission.Work.Drive.refTripleLocal
import Submission.Work.Drive.refTripleLocalAssembly
import Submission.Work.Drive.exists_eps_levelOf_refTriple_chartPert
import Submission.Work.Drive.hsurjCentred
import Submission.Work.Drive.exists_linPlaneCharts_hgen
import Submission.Work.Drive.T6GenAtD
import Submission.Work.Drive.classTripleOdd
import Submission.Work.Drive.mixedFactorBox
import Submission.Work.Drive.blockFactorIdentification
import Submission.Work.Drive.guardedParity
import Submission.Work.Drive.refPlaneLevel
import Submission.Work.Drive.chartIsSmooth
import Submission.Work.Drive.chartShiftHsurj
import Submission.Work.Drive.topBdryMeet_clampedSweep_eq_empty_of_above
import Submission.Work.Drive.mixedFactorTransfer

/-!
# The producer of the one-parameter reference-triple data `RefTripleAt` (the `hn2` node)

`Work.Drive.RefTripleAt` (`Submission/Work/Drive/refTripleOneT.lean`) bundles the six clauses that the
`hn2` endpoint `Work.Drive.sideGerm_add_neg_eq_one_of_refTripleOneT_guarded` consumes at a **single**
perturbation parameter `t : 𝔼¹²`: the level bound, the sweeps' `Meet3Hyp`, the class-triple parity
`Odd (classTripleSet …)`, the two coupled `GoodAt`s and the block-factor data of the transport `T6`.

This module proves the *producer*: for a plane chart `Q` of `γ`, a truncation level `c` below the
chart's disk levels and the whole-plane disjointness `hdisjZc`, there is a **linear** reference plane
`R = diskPlane (linPlaneChart (φ 2) lam hlam)` above the whole configuration such that, for every
`ε > 0`, some parameter `t` of norm `< ε` realises all six clauses.

## The decomposition of the six clauses

| clause | producer | state |
| --- | --- | --- |
| 1. level bound | `exists_eps_levelOf_refTriple_chartPert` (the level of a perturbed point is the level of the point times `exp (τ 0)`) | **proved here** |
| 2. sweeps' `Meet3Hyp` | the parametrised Sard `Work.Drive.refTripleLocal` | **proved here** (`exists_sweepGenericity_one`) |
| 4./5. the two `GoodAt`s | same Sard call (the two *coupled* pair conditions) | **proved here** |
| 3. class-triple parity | the (A) half of the ends clause: the class-triple count of the *perturbed* reference triple | `refTripleAt_classOdd_at` |
| 6. block factors | the transport `T6` at the blocks `0`, `1` (with the mixed factors `(F1)`) plus the emptiness of the reference block's top meet | `refTripleAt_blockT6At` + `refTriple_topBdryMeet_two_eq_empty` |

The two remaining clauses are stated as separate lemmas of this file, each with the *design data* of the
route as hypotheses, so that the assembly `refTripleAt_of_pieces` below is complete; see §6–§8.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

noncomputable section

/-- The concrete chart perturbation is a `ChartPert`. -/
lemma isChartPert_chartPert (Q : ℂ → CappingSpace) :
    ChartPert Q 4 (fun s p => chartPert s p) :=
  ⟨chartPert_zero, contMDiff_chartPert, fun t p => surjective_mfderiv_chartPert p contMDiff_chartPert t⟩

/-! ## 1. The design's truncation levels -/

lemma dblk_pos {c : ℝ} (hc : 0 < c) :
    ∀ k : Fin 3, 0 < (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) k := by
  intro k; fin_cases k <;> simp <;> linarith

lemma dblk_distinct {c : ℝ} (hc : 0 < c) :
    ∀ k k' : Fin 3, (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) k
      = (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) k' → k = k' := by
  intro k k' h; revert h
  fin_cases k <;> fin_cases k' <;> intro h <;> simp at h <;> first | rfl | linarith

lemma dblk_lt_zero {c : ℝ} (hc : 0 < c) {k : Fin 3} (hk : k ≠ 0) :
    (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) k < (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 0 := by
  fin_cases k
  · exact absurd rfl hk
  · norm_num; linarith
  · norm_num; linarith

lemma dblk_apply (c : ℝ) (k : Fin 3) :
    (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) k = c / ((k : ℕ) + 2) := by
  fin_cases k <;> norm_num

/-! ## 3. The reference plane presentation and the reference triple -/

/-- The reference plane of the `hn2` design: the plane presentation of the linear plane chart
`linPlaneChart (φ 2) lam hlam`. -/
def refPlanePres (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam) :
    EuclideanSpace ℝ (Fin 2) → CappingSpace :=
  diskPlane (linPlaneChart (φ 2) lam hlam)

lemma refPlanePres_contMDiff (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam) :
    ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (refPlanePres φ lam hlam) :=
  contMDiff_diskPlane (linPlaneChart_contMDiff (φ 2) lam hlam)

lemma refPlanePres_seam (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam) :
    ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y →
      refPlanePres φ lam hlam y = refPlanePres φ lam hlam (seamInv2 y) :=
  fun y hy => (diskPlane_seamInv2 (Q := linPlaneChart (φ 2) lam hlam)
    (fun z hz => linPlaneChart_neg (φ 2) lam hlam hz) hy).symm

lemma refPlanePres_level (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam) :
    ∀ y : EuclideanSpace ℝ (Fin 2), levelOf (refPlanePres φ lam hlam y) = lam :=
  fun y => level_diskPlane_linPlaneChart (φ 2) lam hlam y

lemma refTriple_contMDiff (Q : ℂ → CappingSpace) (hQsm : IsSmoothChart Q)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam) (u v : UnitAddCircle) :
    ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (refTriple Q (refPlanePres φ lam hlam) u v k) := by
  have hRsm := refPlanePres_contMDiff φ lam hlam
  intro k
  fin_cases k
  · simpa [refTriple] using contMDiff_rotPresentation Q u (contMDiff_diskPlane (Q := Q) hQsm)
  · simpa [refTriple] using contMDiff_rotPresentation Q v (contMDiff_diskPlane (Q := Q) hQsm)
  · simpa [refTriple] using hRsm

lemma c_lt_lam {Q : ℂ → CappingSpace} {c lam : ℝ}
    (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (habove : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) < lam) : c < lam := by
  have h1 : c < levelOf (Q 0) := hcbot (Q 0) ⟨0, by simp [Metric.mem_closedBall], rfl⟩
  exact lt_trans h1 (habove 0 (by simp))

/-! ## 4. The perturbed block chains of the reference triple -/

/-- The `k`-th block chain of the perturbation family: the `k`-th plane of the reference triple,
perturbed by the `k`-th block of the parameter `t`. -/
def refBlock (Ξ : Eucl 3 → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace)
    (R : EuclideanSpace ℝ (Fin 2) → CappingSpace) (u v : UnitAddCircle)
    (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3) : EuclideanSpace ℝ (Fin 2) → CappingSpace :=
  fun y => Ξ (blk k t) (refTriple Q R u v k y)

/-- The sweep family of the reference triple is the clamped sweep of the block chains. -/
lemma sweepChartFam_eq_refBlock (Ξ : Eucl 3 → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (R : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (u v : UnitAddCircle) (cblk : Fin 3 → ℝ) (t : EuclideanSpace ℝ (Fin 12)) :
    sweepChartFam (refTriple Q R u v) Ξ cblk t
      = fun k => clampedSweep (cblk k) (fun r => 1 - r) (refBlock Ξ Q R u v t k) := rfl

/-- The perturbed level is the product of the unperturbed level with the exponential of the level
coordinate of the perturbation. -/
lemma levelOf_chartPert_mul (τ : Eucl 3) (p : CappingSpace) :
    levelOf (chartPert τ p) = levelOf p * Real.exp (τ.ofLp 0) := by
  rw [levelOf_chartPert, levelScale_apply, Real.exp_add, Real.exp_log (levelOf_pos p)]

lemma exp_coord_blk_le (k : Fin 3) (t : EuclideanSpace ℝ (Fin 12)) :
    Real.exp ((blk k t).ofLp 0) ≤ Real.exp ‖t‖ :=
  Real.exp_le_exp.mpr (le_trans (le_abs_self _) (abs_coord_blk_le k t))

lemma exp_coord_blk_ge (k : Fin 3) (t : EuclideanSpace ℝ (Fin 12)) :
    Real.exp (-‖t‖) ≤ Real.exp ((blk k t).ofLp 0) :=
  Real.exp_le_exp.mpr (by
    have h := abs_coord_blk_le k t
    linarith [neg_abs_le ((blk k t).ofLp 0)])

/-- **The upper level bound of the perturbed reference triple.**  On the two *configuration* blocks
(`k = 0, 1`) the level of the perturbed reference triple is at most `β · exp ‖t‖`, where `β` bounds the
chart's levels on the closed disk. -/
lemma refBlock_level_le {Q : ℂ → CappingSpace} {β : ℝ}
    (hβ : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≤ β) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ)
    (hlam : 0 < lam) (u v : UnitAddCircle) (t : EuclideanSpace ℝ (Fin 12)) {k : Fin 3} (hk : k ≠ 2)
    (y : EuclideanSpace ℝ (Fin 2)) :
    levelOf (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t k y)
      ≤ β * Real.exp ‖t‖ := by
  have hbound : levelOf (refTriple Q (refPlanePres φ lam hlam) u v k y) ≤ β := by
    fin_cases k
    · simpa [refTriple] using levelOf_rotPresentation_le Q hβ u y
    · simpa [refTriple] using levelOf_rotPresentation_le Q hβ v y
    · exact absurd rfl hk
  have hβnn : 0 ≤ β := le_trans (levelOf_pos (Q 0)).le (hβ 0 (by simp))
  rw [refBlock, levelOf_chartPert_mul]
  exact mul_le_mul hbound (exp_coord_blk_le k t) (Real.exp_pos _).le hβnn

/-- **The lower level bound of the perturbed reference block.**  On the *reference* block (`k = 2`)
the level of the perturbed reference plane is at least `lam · exp (-‖t‖)`. -/
lemma refBlock_level_ge (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    (Q : ℂ → CappingSpace) (u v : UnitAddCircle) (t : EuclideanSpace ℝ (Fin 12))
    (y : EuclideanSpace ℝ (Fin 2)) :
    lam * Real.exp (-‖t‖)
      ≤ levelOf (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2 y) := by
  rw [refBlock, levelOf_chartPert_mul, show refTriple Q (refPlanePres φ lam hlam) u v 2 y
    = refPlanePres φ lam hlam y from rfl, refPlanePres_level]
  exact mul_le_mul_of_nonneg_left (exp_coord_blk_ge 2 t) hlam.le

/-- **The strict level separation of the perturbed reference triple**: the two configuration blocks lie
strictly below the reference block, as soon as `2 ‖t‖ < log (lam / β)`. -/
lemma refBlock_level_lt_of_small {Q : ℂ → CappingSpace} {β : ℝ} (hβpos : 0 < β)
    (hβ : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≤ β) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ)
    (hlam : 0 < lam) (hβlam : β < lam) (u v : UnitAddCircle) {t : EuclideanSpace ℝ (Fin 12)}
    (ht : 2 * ‖t‖ < Real.log (lam / β)) {k : Fin 3} (hk : k ≠ 2)
    (y y' : EuclideanSpace ℝ (Fin 2)) :
    levelOf (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t k y)
      < levelOf (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2 y') := by
  have hlampos : 0 < lam := hlam
  refine lt_of_le_of_lt (refBlock_level_le hβ φ lam hlampos u v t hk y)
    (lt_of_lt_of_le ?_ (refBlock_level_ge φ lam hlampos Q u v t y'))
  -- `β * exp ‖t‖ < lam * exp (-‖t‖)`
  have hlog : Real.log β + ‖t‖ < Real.log lam - ‖t‖ := by
    have h := Real.log_lt_log hβpos hβlam
    rw [Real.log_div (ne_of_gt hlampos) (ne_of_gt hβpos)] at ht
    linarith
  calc β * Real.exp ‖t‖ = Real.exp (Real.log β + ‖t‖) := by
        rw [Real.exp_add, Real.exp_log hβpos]
    _ < Real.exp (Real.log lam - ‖t‖) := Real.exp_lt_exp.mpr hlog
    _ = lam * Real.exp (-‖t‖) := by
        rw [Real.exp_sub, Real.exp_log hlampos, Real.exp_neg, div_eq_mul_inv]

/-! ## 5. Clause 6, block `2`: the reference block's top boundary meet is empty -/

/-- **The reference block contributes nothing at the top**: for a perturbation parameter `t` with
`2 ‖t‖ < log (lam / β)` the block `2` of the reference triple has no top boundary triple meet. -/
theorem refTriple_topBdryMeet_two_eq_empty {Q : ℂ → CappingSpace} {β : ℝ} (hβpos : 0 < β)
    (hβ : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≤ β) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ)
    (hlam : 0 < lam) (hβlam : β < lam) (u v : UnitAddCircle) {cblk : Fin 3 → ℝ}
    (hc : ∀ k, 0 < cblk k) {t : EuclideanSpace ℝ (Fin 12)}
    (ht : 2 * ‖t‖ < Real.log (lam / β))
    (hlow : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      cblk k ≤ levelOf (refBlock (fun s p => chartPert s p) Q
        (refPlanePres φ lam hlam) u v t k y)) :
    topBdryMeet CappingSpace
      (sweepChartFam (refTriple Q (refPlanePres φ lam hlam) u v)
        (fun s p => chartPert s p) cblk t) 2 = ∅ := by
  have hlampos : 0 < lam := hlam
  rw [sweepChartFam_eq_refBlock]
  refine topBdryMeet_clampedSweep_eq_empty_of_above cblk
    (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t) 2
    hc ?_ ?_
  · intro j _ y _
    exact hlow j y
  · intro j hj y _ y' _
    exact refBlock_level_lt_of_small hβpos hβ φ lam hlam hβlam u v ht hj y y'



/-! ## 6. A level above the chart's disk levels together with the generic linear charts

`exists_refPlane_charts` produces the level `lam` of the reference plane *and* a level `β` of the chart
strictly below it — the two data the strict level separation of §5 needs. -/

theorem exists_refPlane_charts {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q) :
    ∃ (β lam : ℝ) (hβpos : 0 < β) (hlam : 0 < lam) (hβlam : β < lam)
      (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3),
      (∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≤ β) ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) < lam) ∧
      (∃ h : Module.finrank ℝ ↥(⨅ k : Fin 3, linSub (φ k)) = 1,
        ∀ (k : Fin 3) (z : ℂ), ‖z‖ = 1 →
          linPlaneChart (φ k) lam hlam z ≠ linCommonPt φ lam hlam h) := by
  obtain ⟨β, hβpos, hβ⟩ := exists_levelUpper_of_isPlaneChart γ hγne Q hQ
  have hlam : 0 < β + 1 := by linarith
  obtain ⟨φ, hrank, hgen⟩ := exists_linPlaneCharts_hgen (β + 1) hlam
  exact ⟨β, β + 1, hβpos, hlam, by linarith, φ, hβ, fun z hz => lt_of_le_of_lt (hβ z hz) (by linarith),
    hrank, hgen⟩

/-! ## 8bis. The factor identifications `(0,1)` and `(1,0)` of the reference triple -/

/-- **The block factors `(0,1)` and `(1,0)` of the reference triple are the germ counts.**  This is
`Work.Drive.coreSideCount_block_eq_CntAt_chartPert` at the angle vector `![u, v, v]` (the third entry
is irrelevant) and the block parameters `blk k t`. -/
theorem refTriple_blockIdent (Q : ℂ → CappingSpace)
    (R : EuclideanSpace ℝ (Fin 2) → CappingSpace) (u v : UnitAddCircle) (cblk : Fin 3 → ℝ)
    (t : EuclideanSpace ℝ (Fin 12)) :
    coreSideCount (fun z => chartPert (blk 0 t) (rotCapping u (Q z))) (cblk 1)
        (refBlock (fun s p => chartPert s p) Q R u v t 1)
      = CntAt (fun s p => chartPert s p) Q (cblk 1) (v - u) (blk 0 t, blk 1 t) ∧
    coreSideCount (fun z => chartPert (blk 1 t) (rotCapping v (Q z))) (cblk 0)
        (refBlock (fun s p => chartPert s p) Q R u v t 0)
      = CntAt (fun s p => chartPert s p) Q (cblk 0) (u - v) (blk 1 t, blk 0 t) := by
  constructor
  · rw [show refBlock (fun s p => chartPert s p) Q R u v t 1
        = (fun y => chartPert (blk 1 t) (rotPresentation Q v y)) from rfl]
    have h := coreSideCount_block_eq_CntAt_chartPert Q ![u, v, v] (fun k => blk k t) cblk 0 1
    simpa using h
  · rw [show refBlock (fun s p => chartPert s p) Q R u v t 0
        = (fun y => chartPert (blk 0 t) (rotPresentation Q u y)) from rfl]
    have h := coreSideCount_block_eq_CntAt_chartPert Q ![u, v, v] (fun k => blk k t) cblk 1 0
    simpa using h

/-! ## 8. Clause 6 from the transport data: the combinatorial assembly -/

/-- **Clause 6 of `RefTripleAt` from the transport data.**  Given

* the two `T6` parity equivalences at the configuration blocks `0` and `1` (whose charts are the
  perturbed rotated charts `chart₀`, `chart₁`),
* the emptiness of the reference block's top meet,
* the identification of the block factors `(0,1)`, `(1,0)` with the germ counts, and
* the oddness of the two *mixed* factors `(F1)`

the bundle of block data of `RefTripleAt` holds, with the witness

`g = !![0, f01, f02; f10, 0, f12; 0, 0, 0]`.

The entry `g 2 0 = g 2 1 = 0` is the *vanishing* of the reference block's two factors (the block-`2`
identity then reads `Odd ∅.ncard ↔ False`). -/
theorem exists_blockFactors_of_T6
    {Ξ : Eucl 3 → CappingSpace → CappingSpace} {Q : ℂ → CappingSpace}
    (R : EuclideanSpace ℝ (Fin 2) → CappingSpace) (u v : UnitAddCircle)
    (cblk : Fin 3 → ℝ) (t : EuclideanSpace ℝ (Fin 12))
    (chart₀ chart₁ : ℂ → CappingSpace)
    (hT6₀ : Odd (topBdryMeet CappingSpace (sweepChartFam (refTriple Q R u v) Ξ cblk t) 0).ncard ↔
      Odd (coreSideCount chart₀ (cblk 1) (refBlock Ξ Q R u v t 1)) ∧
      Odd (coreSideCount chart₀ (cblk 2) (refBlock Ξ Q R u v t 2)))
    (hT6₁ : Odd (topBdryMeet CappingSpace (sweepChartFam (refTriple Q R u v) Ξ cblk t) 1).ncard ↔
      Odd (coreSideCount chart₁ (cblk 0) (refBlock Ξ Q R u v t 0)) ∧
      Odd (coreSideCount chart₁ (cblk 2) (refBlock Ξ Q R u v t 2)))
    (hT2 : topBdryMeet CappingSpace (sweepChartFam (refTriple Q R u v) Ξ cblk t) 2 = ∅)
    (h01 : coreSideCount chart₀ (cblk 1) (refBlock Ξ Q R u v t 1)
      = CntAt Ξ Q (cblk 1) (v - u) (blk 0 t, blk 1 t))
    (h10 : coreSideCount chart₁ (cblk 0) (refBlock Ξ Q R u v t 0)
      = CntAt Ξ Q (cblk 0) (u - v) (blk 1 t, blk 0 t))
    (h02 : Odd (coreSideCount chart₀ (cblk 2) (refBlock Ξ Q R u v t 2)))
    (h12 : Odd (coreSideCount chart₁ (cblk 2) (refBlock Ξ Q R u v t 2))) :
    ∃ g : Fin 3 → Fin 3 → ℕ,
      g 0 1 = CntAt Ξ Q (cblk 1) (v - u) (blk 0 t, blk 1 t) ∧
      g 1 0 = CntAt Ξ Q (cblk 0) (u - v) (blk 1 t, blk 0 t) ∧
      (∀ k : Fin 3,
        Odd (topBdryMeet CappingSpace (sweepChartFam (refTriple Q R u v) Ξ cblk t) k).ncard ↔
          (Odd (g k (k + 1)) ∧ Odd (g k (k + 2)))) ∧
      Even (g 2 0) ∧ Even (g 2 1) ∧ Odd (g 0 2) ∧ Odd (g 1 2) := by
  obtain ⟨cA, hcA⟩ : ∃ cA : ℕ, cA = CntAt Ξ Q (cblk 1) (v - u) (blk 0 t, blk 1 t) := ⟨_, rfl⟩
  obtain ⟨cB, hcB⟩ : ∃ cB : ℕ, cB = CntAt Ξ Q (cblk 0) (u - v) (blk 1 t, blk 0 t) := ⟨_, rfl⟩
  refine ⟨![![0, cA, coreSideCount chart₀ (cblk 2) (refBlock Ξ Q R u v t 2)],
      ![cB, 0, coreSideCount chart₁ (cblk 2) (refBlock Ξ Q R u v t 2)], ![0, 0, 0]],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hcA
  · exact hcB
  · intro k
    fin_cases k
    · show Odd (topBdryMeet CappingSpace (sweepChartFam (refTriple Q R u v) Ξ cblk t) 0).ncard
        ↔ Odd (cA : ℕ) ∧ Odd (coreSideCount chart₀ (cblk 2) (refBlock Ξ Q R u v t 2))
      refine hT6₀.trans ?_
      have hcA' : cA = coreSideCount chart₀ (cblk 1) (refBlock Ξ Q R u v t 1) := hcA.trans h01.symm
      rw [hcA']
    · show Odd (topBdryMeet CappingSpace (sweepChartFam (refTriple Q R u v) Ξ cblk t) 1).ncard
        ↔ Odd (coreSideCount chart₁ (cblk 2) (refBlock Ξ Q R u v t 2)) ∧ Odd (cB : ℕ)
      have hcB' : cB = coreSideCount chart₁ (cblk 0) (refBlock Ξ Q R u v t 0) := hcB.trans h10.symm
      refine hT6₁.trans ?_
      rw [hcB']
      exact and_comm
    · show Odd (topBdryMeet CappingSpace (sweepChartFam (refTriple Q R u v) Ξ cblk t) 2).ncard
        ↔ Odd (0 : ℕ) ∧ Odd (0 : ℕ)
      rw [hT2, Set.ncard_empty]
      decide
  · show Even (0 : ℕ)
    decide
  · show Even (0 : ℕ)
    decide
  · show Odd (coreSideCount chart₀ (cblk 2) (refBlock Ξ Q R u v t 2))
    exact h02
  · show Odd (coreSideCount chart₁ (cblk 2) (refBlock Ξ Q R u v t 2))
    exact h12

/-! ## 9. Clauses 1, 2, 4, 5 at one parameter: the level bound and the sweeps' genericity -/

/-- **The level bound of the perturbed reference triple on a ball.** -/
lemma exists_levelBound_at_one {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (c : ℝ) (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (u v : UnitAddCircle) (lam : ℝ) (hlam : 0 < lam) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3)
    (habove : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) < lam) :
    ∃ εl : ℝ, 0 < εl ∧ ∀ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < εl →
      ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
        (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 0
          < levelOf (chartPert (blk k t)
              (refTriple Q (refPlanePres φ lam hlam) u v k y)) := by
  have hcl : c < lam := c_lt_lam hcbot habove
  refine exists_eps_levelOf_refTriple_chartPert (Q := Q) (R := refPlanePres φ lam hlam) u v
    (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) (by simpa using dblk_pos hc 0) hc
    (by show c / 2 < c; linarith) (by show c / 2 < lam; linarith)
    (fun z hz => le_of_lt (hcbot _ ⟨z, by rwa [Metric.mem_closedBall, dist_zero_right], rfl⟩))
    (fun y => le_of_eq (refPlanePres_level φ lam hlam y).symm)

/-- **Clauses 1, 2, 4 and 5 of `RefTripleAt` at one parameter.**  For every `ε > 0` there is a parameter
`t` of norm `< ε` at which the perturbed reference triple has its levels above `c / 2`, is a `Meet3Hyp`
triple of sweeps, and is `GoodAt` at the two ordered pairs `(0,1)` and `(1,0)` (the two *coupled* pair
conditions of the germ engine). -/
theorem exists_sweepGenericity_one {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (c : ℝ) (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (u v : UnitAddCircle) (lam : ℝ) (hlam : 0 < lam) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3)
    (habove : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) < lam) :
    ∀ ε : ℝ, 0 < ε → ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε ∧
      (∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
        (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 0
          < levelOf (chartPert (blk k t)
              (refTriple Q (refPlanePres φ lam hlam) u v k y))) ∧
      Meet3Hyp CappingSpace
        (sweepChartFam (refTriple Q (refPlanePres φ lam hlam) u v)
          (fun s p => chartPert s p) (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) t) ∧
      GoodAt (fun s p => chartPert s p) Q ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 1) (v - u)
        (blk 0 t, blk 1 t) ∧
      GoodAt (fun s p => chartPert s p) Q ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 0) (u - v)
        (blk 1 t, blk 0 t) := by
  intro ε hε
  obtain ⟨εl, hεl, hlvl⟩ := exists_levelBound_at_one hQ c hc hcbot u v lam hlam φ habove
  have hrich := richness_sweepChartFam (refTriple Q (refPlanePres φ lam hlam) u v)
    (fun s p => chartPert s p) (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) (isChartPert_chartPert Q)
    (dblk_pos hc) (dblk_distinct hc)
    (refTriple_contMDiff Q (IsSmoothChart_of_isPlaneChart hQ) φ lam hlam u v)
  obtain ⟨t, ht, hmeet, hg01, hg10⟩ :=
    refTripleLocal (IsChartData_of_isPlaneChart hQ) (fun s p => chartPert s p)
      (isChartPert_chartPert Q) (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) (dblk_pos hc)
      (dblk_distinct hc) u v (refPlanePres φ lam hlam) (refPlanePres_contMDiff φ lam hlam)
      (refPlanePres_seam φ lam hlam) hrich (min ε εl) (lt_min hε hεl)
  refine ⟨t, lt_of_lt_of_le ht (min_le_left _ _), hlvl t (lt_of_lt_of_le ht (min_le_right _ _)),
    hmeet, hg01, hg10⟩


/-! ## 10. The producer -/

end

end Work.Drive
