import Mathlib
import Submission.Work.Drive.dense_T6GenAtDBox_design
import Submission.Work.Drive.parityChainSmooth
import Submission.Work.Drive.T6GenAtD
import Submission.Work.Drive.perturbedTripleIdentity
import Submission.Work.Drive.SeamSweep
import Submission.Work.Drive.sideGermDefs

/-!
# The reference triple's `T6` density with an *independent* third plane

`Work.Drive.dense_T6GenAtDBox_design` proves the density of the transport bundle `T6GenAtDBox` at the
block `k` of the design's perturbed triple, in which **all three** blocks are built from the *same*
plane chart `Q` (`blockChart Ξ Q u τ k`, `blockPlane Ξ Q u τ (k+1)`, `blockPlane Ξ Q u τ (k+2)`).

The node `Work.Drive.dense_T6GenAtDBox_refTriple` asks for the **reference triple** of the `hn2`/`hdense`
route: block `0` and block `1` still come from `Q` (with the two angles `u`, `v`), but the third plane
is the *independent* chart `QR` of the route (`fun y => Ξ (blk 2 t) (diskPlane QR y)`), with its own
smoothness and level band.  The third block of the design enters the argument only through

* the smoothness of the swept plane (`sgGoodChain_of_small_shift_sweep`,
  `exists_loopBoxData_of_small_shift`, whose perturbation chart is a free argument), and
* the cut-avoidance clause (`exists_deltaC_shift`, whose chain is held fixed while the *chart* moves),

so the whole design proof transcribes with `Qw := QR` and the angle of the third block dropped.  This
file performs that transcription:

* `Work.Drive.refT_exists_loopBoxData_of_small_shift` — the `w = 0` (identity rotation) instance of the
  loop-box-data producer, so that the third block's chart is used without a manufactured rotation;
* `Work.Drive.CutAvoidsQR` + `Work.Drive.exists_cutAvoidsQR_near` + `Work.Drive.isOpen_cutAvoidsQR` —
  the third conjunct of `T6GenAt` for the split triple, together with its two design properties (open
  in `t`, dense near every `t`);
* `Work.Drive.dense_T6GenAtDBox_split` — the split form of `dense_T6GenAtDBox_design`;
* `Work.Drive.dense_T6GenAtDBox_refTriple` — the node, at `k = 0` and `u = ![u, v, v]`.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option maxHeartbeats 100000000
set_option linter.unusedVariables false

/-! ## 0. The index bookkeeping of three blocks -/

/-- Three is odd: the distinguished block does not meet its successor. -/
private lemma refT_fin3_add_one_ne (k : Fin 3) : (k + 1 : Fin 3) ≠ k := by fin_cases k <;> decide

/-- Three is odd: the distinguished block does not meet its successor's successor. -/
private lemma refT_fin3_add_two_ne (k : Fin 3) : (k + 2 : Fin 3) ≠ k := by fin_cases k <;> decide

/-- The diameter block is not the core-sweep block. -/
private lemma refT_fin3_add_two_ne_add_one (k : Fin 3) : (k + 2 : Fin 3) ≠ k + 1 := by
  fin_cases k <;> decide

/-! ## 1. The loop-box-data producer at the identity rotation -/

/-- **The loop-box-data producer for a freely chosen third chart.**  This is
`Work.Drive.exists_loopBoxData_of_small_shift` at the rotation `w = 0`: the perturbed chart is passed
directly, without the `rotCapping w` wrapper (the two agree by `Work.Drive.rotCapping_zero`). -/
theorem refT_exists_loopBoxData_of_small_shift {m : Nat} (Q : ℂ → CappingSpace) (hQ : IsSmoothChart Q)
    (theta c : ℝ) (hc : 0 < c) (hlevQ : ∀ z : ℂ, ‖z‖ ≤ 1 → c < levelOf (Q z))
    (Xi : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q0 : ℂ → CappingSpace) (hXi : ChartPert Q0 m Xi) (hQ0 : IsSmoothChart Q0)
    (s0 : EuclideanSpace ℝ (Fin m)) (e0 : ℝ) (he0 : 0 < e0) :
    ∃ p : EuclideanSpace ℝ (Fin m), ‖p‖ < e0 ∧
      LoopBoxData (diamFam Q theta)
        (clampedSweep c (fun s : ℝ => 1 - s) (diskPlane (pertChart Xi Q0 (s0 + p)))) ∧
      LoopBoxData (arcFam Q theta)
        (clampedSweep c (fun s : ℝ => 1 - s) (diskPlane (pertChart Xi Q0 (s0 + p)))) := by
  obtain ⟨p, hp, h1, h2⟩ :=
    exists_loopBoxData_of_small_shift Q hQ theta c hc hlevQ Xi Q0 hXi hQ0 0 s0 e0 he0
  refine ⟨p, hp, ?_, ?_⟩
  · simpa only [pertChart, rotCapping_zero, id_eq] using h1
  · simpa only [pertChart, rotCapping_zero, id_eq] using h2

/-! ## 2. The cut-avoidance clause of the split triple -/

/-- **The cut-avoidance clause of the split triple**: the third conjunct of `Work.Drive.T6GenAt` at the
block `k` of the split triple, whose third plane is the perturbation of the *independent* chart `QR`. -/
def CutAvoidsQR (Q : ℂ → CappingSpace) (u : Fin 3 → UnitAddCircle) (cblk : Fin 3 → ℝ)
    (k : Fin 3) (QR : ℂ → CappingSpace) (t : EuclideanSpace ℝ (Fin 12)) : Prop :=
  ∃ δc : ℝ, 0 < δc ∧ ∀ x : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ δc →
    x ∉ diskCut (blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k)
      (clampedSweep (cblk (k + 2)) (fun s => 1 - s)
        (fun y => chartPert (blk (k + 2) t) (diskPlane QR y)))

/-- **The cut-avoidance clause of the split triple holds at parameters arbitrarily close to any
parameter.**  The proof is that of `Work.Drive.exists_designCutAvoids_near`: the block `k+2` sweep is
held fixed (a `C^∞` map of `𝔼³` whose image over the box has empty interior by the weak-Sard chapter)
and the *chart* of the block `k` is moved. -/
theorem exists_cutAvoidsQR_near (Q : ℂ → CappingSpace) (hQ : IsChartData Q)
    (u : Fin 3 → UnitAddCircle) (cblk : Fin 3 → ℝ) (k : Fin 3) (QR : ℂ → CappingSpace)
    (hQR : IsSmoothChart QR) (t₀ : EuclideanSpace ℝ (Fin 12)) (ε : ℝ) (hε : 0 < ε) :
    ∃ t : EuclideanSpace ℝ (Fin 12), ‖t - t₀‖ < ε ∧ CutAvoidsQR Q u cblk k QR t := by
  have hΞ : ChartPert Q 4 (fun s p => chartPert s p) :=
    ⟨chartPert_zero, contMDiff_chartPert,
      fun t p => surjective_mfderiv_chartPert p contMDiff_chartPert t⟩
  -- the sweep of the third plane at the base parameter, held fixed
  have hWsmooth : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin 2) => chartPert (blk (k + 2) t₀) (diskPlane QR y)) :=
    (contMDiff_apply_of_chartPert (Q := Q) hΞ (blk (k + 2) t₀)).comp
      (contMDiff_diskPlane (Q := QR) hQR)
  have hWsm : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (clampedSweep (cblk (k + 2)) (fun s => 1 - s)
        (fun y : EuclideanSpace ℝ (Fin 2) => chartPert (blk (k + 2) t₀) (diskPlane QR y))) :=
    contMDiff_clampedSweep (cblk (k + 2)) (fun s => 1 - s)
      (fun y : EuclideanSpace ℝ (Fin 2) => chartPert (blk (k + 2) t₀) (diskPlane QR y))
      (by fun_prop) hWsmooth
  have hWint : interior ((clampedSweep (cblk (k + 2)) (fun s => 1 - s)
      (fun y : EuclideanSpace ℝ (Fin 2) => chartPert (blk (k + 2) t₀) (diskPlane QR y)))
      '' Submission.Drive.unitBox 2) = ∅ :=
    Sard.interior_image_eq_empty_of_contMDiff_of_lt (m := 3) (n := 4) (by norm_num) _ hWsm
      (Submission.Drive.unitBox 2)
  -- the move of the chart of the block `k`
  obtain ⟨σ, hσ, hδ⟩ := exists_deltaC_shift (Ξ := fun s p => chartPert s p)
    (Q' := fun z : ℂ => rotCapping (u k) (Q z))
    ((continuous_rotCapping (u k)).comp hQ.1.continuous) hΞ
    _ hWsm.continuous hWint (blk k t₀) ε hε
  refine ⟨t₀ + blkSpan k σ, ?_, ?_⟩
  · rw [add_sub_cancel_left, norm_blkSpan]
    exact hσ
  · refine ⟨hδ.choose, hδ.choose_spec.1, ?_⟩
    intro x hx
    have hchart : blockChart (fun s p => chartPert s p) Q u
          (fun j => blk j (t₀ + blkSpan k σ)) k
        = fun z : ℂ => chartPert (blk k t₀ + σ) (rotCapping (u k) (Q z)) := by
      unfold blockChart
      simp only [map_add, blk_blkSpan]
    have hW : (fun y : EuclideanSpace ℝ (Fin 2) =>
          chartPert (blk (k + 2) (t₀ + blkSpan k σ)) (diskPlane QR y))
        = fun y : EuclideanSpace ℝ (Fin 2) => chartPert (blk (k + 2) t₀) (diskPlane QR y) := by
      funext y
      rw [map_add, blk_blkSpan_of_ne (k := k) (j := k + 2) (refT_fin3_add_two_ne k), add_zero]
    have hsweep : clampedSweep (cblk (k + 2)) (fun s => 1 - s)
          (fun y : EuclideanSpace ℝ (Fin 2) =>
            chartPert (blk (k + 2) (t₀ + blkSpan k σ)) (diskPlane QR y))
        = clampedSweep (cblk (k + 2)) (fun s => 1 - s)
          (fun y : EuclideanSpace ℝ (Fin 2) => chartPert (blk (k + 2) t₀) (diskPlane QR y)) :=
      congrArg (fun W : EuclideanSpace ℝ (Fin 2) → CappingSpace =>
        clampedSweep (cblk (k + 2)) (fun s => 1 - s) W) hW
    rw [hchart, hsweep]
    exact hδ.choose_spec.2 x hx

/-- **The plane family of the third block is jointly `C^∞`.** -/
lemma contMDiff_refThirdPlaneFam (k : Fin 3) {QR : ℂ → CappingSpace}
    (hQR : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) QR) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2)))
      (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2) =>
        chartPert (blk (k + 2) q.1) (diskPlane QR q.2)) := by
  have h1 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2)))
      (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2) => blk (k + 2) q.1) :=
    contMDiff_iff_contDiff.mpr (by fun_prop)
  have h2 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2)))
      (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2) => diskPlane QR q.2) :=
    (contMDiff_diskPlane hQR).comp (contMDiff_iff_contDiff.mpr (by fun_prop))
  refine (contMDiff_chartPert.comp (h1.prodMk h2)).congr fun q => ?_
  simp only [Function.comp_apply]

/-- **The sweep family of the third block is jointly `C^∞`.** -/
lemma contMDiff_refThirdSweepFam (k : Fin 3) (c : ℝ) {QR : ℂ → CappingSpace}
    (hQR : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) QR) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3)))
      (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) =>
        clampedSweep c (fun s => 1 - s)
          (fun y : EuclideanSpace ℝ (Fin 2) => chartPert (blk (k + 2) q.1) (diskPlane QR y)) q.2) :=
  contMDiff_clampedSweep_family_gen (P := EuclideanSpace ℝ (Fin 12)) c (fun s => 1 - s)
    (by fun_prop) (fun (t : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 2)) =>
      chartPert (blk (k + 2) t) (diskPlane QR y)) (contMDiff_refThirdPlaneFam k hQR)

/-- **The cut-avoidance clause of the split triple is open.**  The proof is that of
`Work.Drive.isOpen_designCutAvoids`: the `δc` clause is the single-point avoidance
`chart 0 ∉ sweep '' unitBox 2`, which is open in `t` because `unitBox 2` is compact and the two
families are jointly continuous. -/
theorem isOpen_cutAvoidsQR (Q : ℂ → CappingSpace) (hQ : IsChartData Q)
    (u : Fin 3 → UnitAddCircle) (cblk : Fin 3 → ℝ) (k : Fin 3) (QR : ℂ → CappingSpace)
    (hQR : IsSmoothChart QR) :
    IsOpen {t : EuclideanSpace ℝ (Fin 12) | CutAvoidsQR Q u cblk k QR t} := by
  have hΞ : ChartPert Q 4 (fun s p => chartPert s p) :=
    ⟨chartPert_zero, contMDiff_chartPert,
      fun t p => surjective_mfderiv_chartPert p contMDiff_chartPert t⟩
  -- joint continuity of the sweep family
  have hSmoothFam := contMDiff_refThirdSweepFam k (cblk (k + 2)) hQR
  have hScont : Continuous (Function.uncurry (fun (t : EuclideanSpace ℝ (Fin 12))
      (x : EuclideanSpace ℝ (Fin 3)) =>
      clampedSweep (cblk (k + 2)) (fun s => 1 - s)
        (fun y : EuclideanSpace ℝ (Fin 2) => chartPert (blk (k + 2) t) (diskPlane QR y)) x)) := by
    have heq : Function.uncurry (fun (t : EuclideanSpace ℝ (Fin 12))
          (x : EuclideanSpace ℝ (Fin 3)) =>
          clampedSweep (cblk (k + 2)) (fun s => 1 - s)
            (fun y : EuclideanSpace ℝ (Fin 2) => chartPert (blk (k + 2) t) (diskPlane QR y)) x)
        = fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) =>
          clampedSweep (cblk (k + 2)) (fun s => 1 - s)
            (fun y : EuclideanSpace ℝ (Fin 2) => chartPert (blk (k + 2) q.1) (diskPlane QR y)) q.2 := by
      funext q
      rfl
    rw [heq]
    exact hSmoothFam.continuous
  -- continuity of the chart at the origin of the disk
  have hTcont : Continuous (fun t : EuclideanSpace ℝ (Fin 12) =>
      blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k 0) := by
    have hjoint := contMDiff_chartPert.continuous
    have h1 : Continuous fun t : EuclideanSpace ℝ (Fin 12) =>
        (((blk k t, rotCapping (u k) (Q 0))) :
          EuclideanSpace ℝ (Fin 4) × CappingSpace) :=
      ((blk k).continuous).prodMk continuous_const
    have h2 := hjoint.comp h1
    have heq : (fun q : EuclideanSpace ℝ (Fin 4) × CappingSpace => chartPert q.1 q.2) ∘
          (fun t : EuclideanSpace ℝ (Fin 12) =>
            (((blk k t, rotCapping (u k) (Q 0))) :
              EuclideanSpace ℝ (Fin 4) × CappingSpace))
        = fun t : EuclideanSpace ℝ (Fin 12) =>
          blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k 0 := by
      funext t
      show chartPert (blk k t) (rotCapping (u k) (Q 0))
        = chartPert ((fun j : Fin 3 => blk j t) k) (rotCapping (u k) (Q 0))
      rfl
    rw [heq] at h2
    exact h2
  -- the pointwise identification with the "no coincidence on the box" condition
  have hiff : ∀ t : EuclideanSpace ℝ (Fin 12), CutAvoidsQR Q u cblk k QR t ↔
      ∀ x ∈ Submission.Drive.unitBox 2,
        clampedSweep (cblk (k + 2)) (fun s => 1 - s)
          (fun y : EuclideanSpace ℝ (Fin 2) => chartPert (blk (k + 2) t) (diskPlane QR y)) x
          ≠ blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k 0 := by
    intro t
    rw [CutAvoidsQR]
    have hcont1 : Continuous (blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k) := by
      have hjoint := contMDiff_chartPert.continuous
      have hlin : Continuous fun z : ℂ =>
          ((blk k t, rotCapping (u k) (Q z)) : EuclideanSpace ℝ (Fin 4) × CappingSpace) :=
        continuous_const.prodMk ((continuous_rotCapping (u k)).comp hQ.1.continuous)
      have hfun : blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k
          = (fun q : EuclideanSpace ℝ (Fin 4) × CappingSpace => chartPert q.1 q.2) ∘
            (fun z : ℂ => (blk k t, rotCapping (u k) (Q z))) := by
        funext z
        simp only [blockChart, Function.comp_apply]
      rw [hfun]
      exact hjoint.comp hlin
    have hcont2 : Continuous (clampedSweep (cblk (k + 2)) (fun s => 1 - s)
        (fun y : EuclideanSpace ℝ (Fin 2) => chartPert (blk (k + 2) t) (diskPlane QR y))) := by
      have h : Continuous (fun x : EuclideanSpace ℝ (Fin 3) =>
          Function.uncurry (fun (t' : EuclideanSpace ℝ (Fin 12))
            (x' : EuclideanSpace ℝ (Fin 3)) =>
            clampedSweep (cblk (k + 2)) (fun s => 1 - s)
              (fun y : EuclideanSpace ℝ (Fin 2) => chartPert (blk (k + 2) t') (diskPlane QR y)) x')
            (t, x)) :=
        hScont.comp (continuous_const.prodMk continuous_id)
      simpa only [Function.uncurry] using h
    rw [exists_deltaC_iff_notMem _ _ hcont1 hcont2]
    constructor
    · intro h x hx heq
      exact h ⟨x, hx, heq⟩
    · rintro h ⟨x, hx, heq⟩
      exact h x hx heq
  rw [show {t : EuclideanSpace ℝ (Fin 12) | CutAvoidsQR Q u cblk k QR t}
      = {t : EuclideanSpace ℝ (Fin 12) | ∀ x ∈ Submission.Drive.unitBox 2,
          clampedSweep (cblk (k + 2)) (fun s => 1 - s)
            (fun y : EuclideanSpace ℝ (Fin 2) => chartPert (blk (k + 2) t) (diskPlane QR y)) x
            ≠ blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k 0}
      from Set.ext fun t => hiff t]
  exact isOpen_setOf_forall_ne_of_isCompact (isCompact_unitBox 2) hScont hTcont

theorem dense_T6GenAtDBox_split {Q : ℂ → Work.Drive.CappingSpace}
    (hQ : Work.Drive.IsChartData Q) (QR : ℂ → Work.Drive.CappingSpace)
    (hQR : Work.Drive.IsSmoothChart QR)
    (u : Fin 3 → UnitAddCircle) (cblk : Fin 3 → ℝ) (k : Fin 3)
    (hcpos : ∀ j : Fin 3, 0 < cblk j)
    (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → cblk (k + 2) < Work.Drive.levelOf (Q z)) :
    ∀ x : EuclideanSpace ℝ (Fin 12), ‖x‖ ≤ 1 → 0 ≤ (Work.Drive.blk k x) 0 →
      ∀ ε : ℝ, 0 < ε →
        ∃ t : EuclideanSpace ℝ (Fin 12), ‖t - x‖ < ε ∧
          Work.Drive.T6GenAtDBox
            (Work.Drive.blockChart (fun s p => Work.Drive.chartPert s p) Q u
              (fun j => Work.Drive.blk j t) k)
            (Work.Drive.blockPlane (fun s p => Work.Drive.chartPert s p) Q u
              (fun j => Work.Drive.blk j t) (k + 1))
            (fun y => Work.Drive.chartPert (Work.Drive.blk (k + 2) t)
              (Work.Drive.diskPlane QR y))
            (cblk (k + 1)) (cblk (k + 2)) := by
  intro x hxle hx0 ε hε
  -- ## 0. the chart perturbation and the chart's smoothness
  let Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace := fun s p => chartPert s p
  have hΞ : ChartPert Q 4 Ξ :=
    ⟨chartPert_zero, contMDiff_chartPert,
      fun t p => surjective_mfderiv_chartPert p contMDiff_chartPert t⟩
  have hQsm : IsSmoothChart Q := hQ.1
  -- ## 1. the budget
  let δ : ℝ := ε / 8
  have hδdef : δ = ε / 8 := rfl
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hδ4 : 0 < δ / 4 := by linarith
  -- ## 2. the first move: raise the level of the block `k` parameter
  let w₀ : EuclideanSpace ℝ (Fin 4) := δ • EuclideanSpace.single 0 (1 : ℝ)
  have hw₀0 : w₀ 0 = δ := by
    show (δ • EuclideanSpace.single 0 (1 : ℝ) : EuclideanSpace ℝ (Fin 4)) 0 = δ
    rw [PiLp.smul_apply, PiLp.single_apply, if_pos rfl, smul_eq_mul, mul_one]
  have hw₀norm : ‖w₀‖ = δ := by
    show ‖(δ • EuclideanSpace.single 0 (1 : ℝ) : EuclideanSpace ℝ (Fin 4))‖ = δ
    rw [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_eq_abs,
      abs_of_pos hδpos]
  let t₁ : EuclideanSpace ℝ (Fin 12) := x + blkSpan k w₀
  have ht₁x : ‖t₁ - x‖ = δ := by
    show ‖(x + blkSpan k w₀) - x‖ = δ
    rw [add_sub_cancel_left, norm_blkSpan, hw₀norm]
  have hblk₁ : blk k t₁ = blk k x + w₀ := by
    show blk k (x + blkSpan k w₀) = blk k x + w₀
    rw [denseT6_blk_add_blkSpan, if_pos rfl]
  have hlev₁ : δ ≤ (blk k t₁) 0 := by
    rw [hblk₁, PiLp.add_apply, hw₀0]
    linarith
  -- ## 3. the cut-avoidance move, which only moves the block `k` parameter
  obtain ⟨t₂, ht₂, hIII₂⟩ := exists_cutAvoidsQR_near Q hQ u cblk k QR hQR t₁ (δ / 4) hδ4
  have hlev₂ : 3 * δ / 4 ≤ (blk k t₂) 0 := by
    have hsplit : blk k t₂ = blk k t₁ + blk k (t₂ - t₁) := by rw [map_sub]; abel
    have hb : |(blk k (t₂ - t₁)) 0| ≤ ‖t₂ - t₁‖ := denseT6_coord_bound k _
    have hlow : -(δ / 4) < (blk k (t₂ - t₁)) 0 :=
      (abs_lt.mp (lt_of_le_of_lt hb ht₂)).1
    rw [hsplit, PiLp.add_apply]
    linarith
  -- ## 4. the openness radius of the cut avoidance at `t₂`
  have hEvIII : ∀ᶠ t in 𝓝 t₂, CutAvoidsQR Q u cblk k QR t :=
    (isOpen_cutAvoidsQR Q hQ u cblk k QR hQR).mem_nhds hIII₂
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp hEvIII
  have hρsub' : ∀ t : EuclideanSpace ℝ (Fin 12), ‖t - t₂‖ < ρ →
      CutAvoidsQR Q u cblk k QR t := by
    intro t ht
    have hb : t ∈ Metric.ball t₂ ρ := by rwa [Metric.mem_ball, dist_eq_norm]
    exact hρsub hb
  -- ## 5. the core clause: move the block `k` chart by a small perturbation
  let ε₁ : ℝ := min (ρ / 4) (δ / 4)
  have hε₁pos : 0 < ε₁ := lt_min (by linarith) hδ4
  have hε₁δ : ε₁ ≤ δ / 4 := min_le_right _ _
  have hε₁ρ : ε₁ ≤ ρ / 4 := min_le_left _ _
  obtain ⟨p₁, hp₁, hgp₁⟩ := sgGoodPair_of_small_shift (Ξ := Ξ) (Q := Q) (c := cblk (k + 1))
    hΞ hQsm (u (k + 1) - u k) (blk k t₂) (blk (k + 1) t₂) ε₁ hε₁pos
  let t₃ : EuclideanSpace ℝ (Fin 12) := t₂ + blkSpan k p₁
  let τ : Fin 3 → EuclideanSpace ℝ (Fin 4) := fun j => blk j t₃
  have hτk : τ k = blk k t₂ + p₁ := by
    show blk k (t₂ + blkSpan k p₁) = blk k t₂ + p₁
    rw [denseT6_blk_add_blkSpan, if_pos rfl]
  have hτk1 : τ (k + 1) = blk (k + 1) t₂ := by
    show blk (k + 1) (t₂ + blkSpan k p₁) = blk (k + 1) t₂
    rw [denseT6_blk_add_blkSpan, if_neg (refT_fin3_add_one_ne k), add_zero]
  have hτk0 : 0 < (τ k) 0 := by
    have hple : ‖p₁‖ ≤ δ / 4 := le_trans (le_of_lt hp₁) hε₁δ
    have hc : |p₁ 0| ≤ ‖p₁‖ := denseT6_coord_bound4 p₁
    have hlow : -(δ / 4) ≤ p₁ 0 := (abs_le.mp (le_trans hc hple)).1
    rw [hτk, PiLp.add_apply]
    linarith
  have hGoodAt : GoodAt Ξ Q (cblk (k + 1)) (u (k + 1) - u k) (τ k, τ (k + 1)) := by
    show GoodPair (pertChart Ξ Q (τ k))
      (fun p => rotCapping (u (k + 1) - u k) (pertChart Ξ Q (τ (k + 1)) p)) (cblk (k + 1))
    rw [hτk, hτk1]
    exact hgp₁
  have hcomm : ∀ (s : EuclideanSpace ℝ (Fin 4)) (w : UnitAddCircle) (p : CappingSpace),
      Ξ s (rotCapping w p) = rotCapping w (Ξ s p) := by
    intro s w p
    obtain ⟨v, hv⟩ : ∃ v : ℝ, ((v : ℝ) : UnitAddCircle) = w := ⟨Quotient.out w, Quotient.out_eq w⟩
    rw [← hv]
    exact chartPert_rotCapping_comm v s p
  have hI : GoodLoopChain (coreLoop (blockChart Ξ Q u τ k))
      (clampedSweep (cblk (k + 1)) (fun r => 1 - r) (blockPlane Ξ Q u τ (k + 1))) := by
    have hgp := goodPair_blockChart_of_goodAt Ξ hcomm Q u τ hGoodAt
    have h := goodLoopChain_of_goodPair hgp
    simpa only [blockPlane_eq_diskPlane_blockChart] using h
  have hSfin : (coreMeet (blockChart Ξ Q u τ k) (cblk (k + 1))
      (blockPlane Ξ Q u τ (k + 1))).Finite := hI.1
  -- ## 6. the loop, the level band and the diameter block's family
  let Qk : ℂ → CappingSpace := blockChart Ξ Q u τ k
  let P₁ : EuclideanSpace ℝ (Fin 2) → CappingSpace := blockPlane Ξ Q u τ (k + 1)
  let Qw : ℂ → CappingSpace := QR
  have hQksm : IsSmoothChart Qk := denseT6_isSmoothChart_blockChart u τ k hQsm
  have hQwsm : IsSmoothChart Qw := hQR
  have hlevQk : ∀ z : ℂ, ‖z‖ ≤ 1 → cblk (k + 2) < levelOf (Qk z) := by
    intro z hz
    have h1 : levelOf (Qk z) = levelOf (Q z) * Real.exp ((τ k) 0) := by
      show levelOf (blockChart Ξ Q u τ k z) = levelOf (Q z) * Real.exp ((τ k) 0)
      exact denseT6_levelOf_blockChart u τ k z
    rw [h1]
    have hexp : 1 ≤ Real.exp ((τ k) 0) := Real.one_le_exp (le_of_lt hτk0)
    calc cblk (k + 2) < levelOf (Q z) := hlev z hz
      _ = levelOf (Q z) * 1 := (mul_one _).symm
      _ ≤ levelOf (Q z) * Real.exp ((τ k) 0) :=
          mul_le_mul_of_nonneg_left hexp (le_of_lt (levelOf_pos _))
  have hlevLoop : ∀ (θ s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
      cblk (k + 2) < levelOf (diamLoop Qk θ s) := by
    intro θ s hs
    rw [diamLoop_eq]
    apply hlevQk
    rw [norm_polPt, abs_le]
    constructor <;> linarith [hs.1, hs.2]
  -- the family of swept planes in the shift of the diameter block's parameter
  let DP : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 2) → CappingSpace :=
    fun y => diskPlane (pertChart Ξ Qw (τ (k + 2) + y))
  have hDP : ∀ y : EuclideanSpace ℝ (Fin 4),
      DP y = fun z : EuclideanSpace ℝ (Fin 2) => Ξ (τ (k + 2) + y) (diskPlane QR z) := by
    intro y
    funext z
    rfl
  have hDP0 : ∀ y : EuclideanSpace ℝ (Fin 4),
      DP (y + 0) = DP y := by
    intro y
    congr 1
    abel
  -- ## 7. openness of the two conditions in the shift of the block `(k+2)` parameter
  have hopenA : ∀ q : ↥(coreMeet (blockChart Ξ Q u τ k) (cblk (k + 1))
        (blockPlane Ξ Q u τ (k + 1))),
      IsOpen {y : EuclideanSpace ℝ (Fin 4) |
        GoodLoopChain (diamLoop Qk q.1.1)
          (clampedSweep (cblk (k + 2)) (fun s => 1 - s) (DP y))} := by
    intro q
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hLsm : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 4) × ℝ)) (𝓡 4) Ctop
        (fun r : EuclideanSpace ℝ (Fin 4) × ℝ => diamLoop Qk q.1.1 r.2) := by
      have hproj : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 4) × ℝ)) (𝓘(ℝ, ℝ)) Ctop
          (fun r : EuclideanSpace ℝ (Fin 4) × ℝ => r.2) :=
        contMDiff_iff_contDiff.mpr (by fun_prop)
      exact (isSmoothLoop_diamLoop hQksm q.1.1).comp hproj
    have hDsm : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3)))
        (𝓡 4) Ctop
        (fun r : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3) =>
          clampedSweep (cblk (k + 2)) (fun s => 1 - s) (DP (y + r.1)) r.2) := by
      have h := contMDiff_sggSweepFam (m := 4) Ξ Qw (cblk (k + 2)) hΞ hQwsm (τ (k + 2) + y)
      simpa only [DP, add_assoc] using h
    have h0 : GoodLoopChain (diamLoop Qk q.1.1)
        (clampedSweep (cblk (k + 2)) (fun s => 1 - s) (DP (y + 0))) := by
      simpa only [Set.mem_ofPred_eq, add_zero] using hy
    have hEv := eventually_good_meetBox (P := EuclideanSpace ℝ (Fin 4))
      (L := fun _ : EuclideanSpace ℝ (Fin 4) => diamLoop Qk q.1.1)
      (D := fun y' => clampedSweep (cblk (k + 2)) (fun s => 1 - s) (DP (y + y')))
      hLsm hDsm h0.1 h0.2.1 h0.2.2
    have htend : Tendsto (fun y' : EuclideanSpace ℝ (Fin 4) => y' - y) (𝓝 y) (𝓝 0) := by
      have hc : Continuous (fun y' : EuclideanSpace ℝ (Fin 4) => y' - y) := by fun_prop
      simpa using hc.tendsto y
    filter_upwards [htend.eventually hEv] with y' hy'
    have harg : DP (y + (y' - y)) = DP y' := by congr 1; abel
    rw [harg] at hy'
    exact hy'
  have hopenB : ∀ q : ↥(coreMeet (blockChart Ξ Q u τ k) (cblk (k + 1))
        (blockPlane Ξ Q u τ (k + 1))),
      IsOpen {y : EuclideanSpace ℝ (Fin 4) |
        DiamFamReg Qk q.1.1 (cblk (k + 2)) (DP y)} := by
    intro q
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hDsm : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3)))
        (𝓡 4) Ctop
        (fun r : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3) =>
          clampedSweep (cblk (k + 2)) (fun s => 1 - s) (DP (y + r.1)) r.2) := by
      have h := contMDiff_sggSweepFam (m := 4) Ξ Qw (cblk (k + 2)) hΞ hQwsm (τ (k + 2) + y)
      simpa only [DP, add_assoc] using h
    have hAd : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 2)))
        (𝓡 4) Ctop (fun r : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 2) =>
          diamFam Qk q.1.1 r.2) :=
      (contMDiff_diamFam hQksm q.1.1).comp
        (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 4))
          (EuclideanSpace ℝ (Fin 2))).contMDiff
    have hAa : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 2)))
        (𝓡 4) Ctop (fun r : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 2) =>
          arcFam Qk q.1.1 r.2) :=
      (contMDiff_arcFam hQksm q.1.1).comp
        (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 4))
          (EuclideanSpace ℝ (Fin 2))).contMDiff
    have hyD : LoopBoxData (diamFam Qk q.1.1)
        (clampedSweep (cblk (k + 2)) (fun s => 1 - s) (DP (y + 0))) := by
      have h := ((denseT6_diamFamReg_iff Qk q.1.1 (cblk (k + 2)) (DP y)).mp
        (by simpa only [Set.mem_ofPred_eq] using hy)).1
      simpa only [add_zero] using h
    have hyA : LoopBoxData (arcFam Qk q.1.1)
        (clampedSweep (cblk (k + 2)) (fun s => 1 - s) (DP (y + 0))) := by
      have h := ((denseT6_diamFamReg_iff Qk q.1.1 (cblk (k + 2)) (DP y)).mp
        (by simpa only [Set.mem_ofPred_eq] using hy)).2
      simpa only [add_zero] using h
    have hEvD := loopBoxData_eventually (A := fun _ : EuclideanSpace ℝ (Fin 4) =>
        diamFam Qk q.1.1)
      (D := fun y' => clampedSweep (cblk (k + 2)) (fun s => 1 - s) (DP (y + y'))) hAd hDsm hyD
    have hEvA := loopBoxData_eventually (A := fun _ : EuclideanSpace ℝ (Fin 4) =>
        arcFam Qk q.1.1)
      (D := fun y' => clampedSweep (cblk (k + 2)) (fun s => 1 - s) (DP (y + y'))) hAa hDsm hyA
    have htend : Tendsto (fun y' : EuclideanSpace ℝ (Fin 4) => y' - y) (𝓝 y) (𝓝 0) := by
      have hc : Continuous (fun y' : EuclideanSpace ℝ (Fin 4) => y' - y) := by fun_prop
      simpa using hc.tendsto y
    filter_upwards [htend.eventually (hEvD.and hEvA)] with y' hy'
    have harg : DP (y + (y' - y)) = DP y' := by congr 1; abel
    rw [harg] at hy'
    exact (denseT6_diamFamReg_iff Qk q.1.1 (cblk (k + 2)) (DP y')).mpr hy'
  -- ## 8. the two conditions jointly, at one core meet
  have hndens : ∀ q : ↥(coreMeet (blockChart Ξ Q u τ k) (cblk (k + 1))
        (blockPlane Ξ Q u τ (k + 1))),
      ∀ y : EuclideanSpace ℝ (Fin 4), ‖y‖ ≤ 1 → ∀ γ : ℝ, 0 < γ →
        ∃ y' : EuclideanSpace ℝ (Fin 4),
          GoodLoopChain (diamLoop Qk q.1.1)
            (clampedSweep (cblk (k + 2)) (fun s => 1 - s) (DP y')) ∧
          DiamFamReg Qk q.1.1 (cblk (k + 2)) (DP y') ∧ ‖y' - y‖ < γ := by
    intro q y hy γ hγ
    refine denseT6_exists_both_of_open_dense
      (A := fun y' => GoodLoopChain (diamLoop Qk q.1.1)
        (clampedSweep (cblk (k + 2)) (fun s => 1 - s) (DP y')))
      (B := fun y' => DiamFamReg Qk q.1.1 (cblk (k + 2)) (DP y'))
      (fun y' hy' => (hopenA q).mem_nhds hy') (fun y' hy' => (hopenB q).mem_nhds hy')
      (fun y' γ' hγ' => ?_) (fun y' γ' hγ' => ?_) y γ hγ
    · obtain ⟨p, hp, hgood⟩ := sgGoodChain_of_small_shift_sweep (m := 4) (by norm_num)
        (diamLoop Qk q.1.1) (isSmoothLoop_diamLoop hQksm q.1.1) Ξ Qw (cblk (k + 2))
        (hcpos (k + 2)) hΞ hQwsm (fun s hs => hlevLoop q.1.1 s hs) (τ (k + 2) + y') γ' hγ'
      refine ⟨y' + p, ?_, ?_⟩
      · have h1 : GoodLoopChain (diamLoop Qk q.1.1)
            (clampedSweep (cblk (k + 2)) (fun s => 1 - s)
              (diskPlane (pertChart Ξ Qw ((τ (k + 2) + y') + p)))) := hgood
        simpa only [DP, add_assoc] using h1
      · rw [add_sub_cancel_left]
        exact hp
    · obtain ⟨p, hp, hLBD, hLBA⟩ := refT_exists_loopBoxData_of_small_shift (m := 4) Qk hQksm q.1.1
        (cblk (k + 2)) (hcpos (k + 2)) hlevQk Ξ QR hΞ hQR (τ (k + 2) + y') γ' hγ'
      refine ⟨y' + p, ?_, ?_⟩
      · have h1 : LoopBoxData (diamFam Qk q.1.1)
            (clampedSweep (cblk (k + 2)) (fun s => 1 - s)
              (diskPlane (pertChart Ξ Qw ((τ (k + 2) + y') + p)))) := hLBD
        have h2 : LoopBoxData (arcFam Qk q.1.1)
            (clampedSweep (cblk (k + 2)) (fun s => 1 - s)
              (diskPlane (pertChart Ξ Qw ((τ (k + 2) + y') + p)))) := hLBA
        have hassoc : (τ (k + 2) + y') + p = τ (k + 2) + (y' + p) := by abel
        rw [hassoc] at h1 h2
        exact (denseT6_diamFamReg_iff Qk q.1.1 (cblk (k + 2)) (DP (y' + p))).mpr
          (by simpa only [DP] using And.intro h1 h2)
      · rw [add_sub_cancel_left]
        exact hp
  -- ## 9. the finite intersection over the core meet set
  let ε₂ : ℝ := min (min (ρ / 4) (δ / 4)) (1 / 2)
  have hε₂pos : 0 < ε₂ := lt_min (lt_min (by linarith) hδ4) (by norm_num)
  have hε₂δ : ε₂ ≤ δ / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hε₂ρ : ε₂ ≤ ρ / 4 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hε₂1 : ε₂ ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  haveI : Fintype ↥(coreMeet (blockChart Ξ Q u τ k) (cblk (k + 1))
      (blockPlane Ξ Q u τ (k + 1))) := hSfin.fintype
  let e : ↥(coreMeet (blockChart Ξ Q u τ k) (cblk (k + 1)) (blockPlane Ξ Q u τ (k + 1))) ≃
      Fin (Fintype.card ↥(coreMeet (blockChart Ξ Q u τ k) (cblk (k + 1))
        (blockPlane Ξ Q u τ (k + 1)))) :=
    Fintype.equivFin _
  obtain ⟨p₂, hp₂, hp₂all⟩ := exists_mem_all_of_isOpen_dense (m := 4)
    (Fintype.card ↥(coreMeet (blockChart Ξ Q u τ k) (cblk (k + 1))
      (blockPlane Ξ Q u τ (k + 1))))
    (fun n => {y : EuclideanSpace ℝ (Fin 4) |
        GoodLoopChain (diamLoop Qk (e.symm n).1.1)
          (clampedSweep (cblk (k + 2)) (fun s => 1 - s) (DP y))} ∩
      {y : EuclideanSpace ℝ (Fin 4) |
        DiamFamReg Qk (e.symm n).1.1 (cblk (k + 2)) (DP y)})
    (fun n => (hopenA (e.symm n)).inter (hopenB (e.symm n)))
    (fun n y hy γ hγ => by
      obtain ⟨y', h1, h2, h3⟩ := hndens (e.symm n) y hy γ hγ
      exact ⟨y', ⟨h1, h2⟩, h3⟩)
    ε₂ hε₂pos hε₂1
  have hp₂mem : ∀ q ∈ coreMeet (blockChart Ξ Q u τ k) (cblk (k + 1))
      (blockPlane Ξ Q u τ (k + 1)),
      GoodLoopChain (diamLoop Qk q.1)
          (clampedSweep (cblk (k + 2)) (fun s => 1 - s) (DP p₂)) ∧
        DiamFamReg Qk q.1 (cblk (k + 2)) (DP p₂) := by
    intro q hq
    have hn := hp₂all (e ⟨q, hq⟩)
    simpa only [Equiv.symm_apply_apply, Set.mem_inter_iff, Set.mem_ofPred_eq] using hn
  -- ## 10. the final parameter and its block values
  let tfin : EuclideanSpace ℝ (Fin 12) := t₃ + blkSpan (k + 2) p₂
  have hbk2 : blk (k + 2) tfin = τ (k + 2) + p₂ := by
    show blk (k + 2) (t₃ + blkSpan (k + 2) p₂) = τ (k + 2) + p₂
    rw [denseT6_blk_add_blkSpan, if_pos rfl]
  have hbkk : blk k tfin = τ k := by
    show blk k (t₃ + blkSpan (k + 2) p₂) = τ k
    rw [denseT6_blk_add_blkSpan, if_neg (Ne.symm (refT_fin3_add_two_ne k)), add_zero]
  have hbkk1 : blk (k + 1) tfin = τ (k + 1) := by
    show blk (k + 1) (t₃ + blkSpan (k + 2) p₂) = τ (k + 1)
    rw [denseT6_blk_add_blkSpan, if_neg (Ne.symm (refT_fin3_add_two_ne_add_one k)), add_zero]
  have hQkfin : blockChart (fun s p => chartPert s p) Q u (fun j => blk j tfin) k = Qk := by
    funext z
    show (fun s p => chartPert s p) (blk k tfin) (rotCapping (u k) (Q z))
      = (fun s p => chartPert s p) (τ k) (rotCapping (u k) (Q z))
    rw [hbkk]
  have hP₁fin : blockPlane (fun s p => chartPert s p) Q u (fun j => blk j tfin) (k + 1) = P₁ := by
    funext y
    show (fun s p => chartPert s p) (blk (k + 1) tfin) (rotPresentation Q (u (k + 1)) y)
      = (fun s p => chartPert s p) (τ (k + 1)) (rotPresentation Q (u (k + 1)) y)
    rw [hbkk1]
  have hP₂fin : (fun y : EuclideanSpace ℝ (Fin 2) =>
        chartPert (blk (k + 2) tfin) (diskPlane QR y)) = DP p₂ := by
    rw [hDP p₂]
    funext y
    show (fun s p => chartPert s p) (blk (k + 2) tfin) (diskPlane QR y)
      = (fun s p => chartPert s p) (τ (k + 2) + p₂) (diskPlane QR y)
    rw [hbk2]
  refine ⟨tfin, ?_, ?_⟩
  -- ## 11. the distance bound
  · have hA : ‖tfin - t₃‖ = ‖p₂‖ := by
      show ‖(t₃ + blkSpan (k + 2) p₂) - t₃‖ = ‖p₂‖
      rw [add_sub_cancel_left, norm_blkSpan]
    have hB : ‖t₃ - t₂‖ = ‖p₁‖ := by
      show ‖(t₂ + blkSpan k p₁) - t₂‖ = ‖p₁‖
      rw [add_sub_cancel_left, norm_blkSpan]
    have hp₂b : ‖p₂‖ ≤ δ / 4 := le_trans (le_of_lt hp₂) hε₂δ
    have hp₁b : ‖p₁‖ ≤ δ / 4 := le_trans (le_of_lt hp₁) hε₁δ
    have hs1 : ‖tfin - x‖ ≤ ‖tfin - t₃‖ + ‖t₃ - x‖ := by
      rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
      exact dist_triangle _ _ _
    have hs2 : ‖t₃ - x‖ ≤ ‖t₃ - t₂‖ + ‖t₂ - x‖ := by
      rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
      exact dist_triangle _ _ _
    have hs3 : ‖t₂ - x‖ ≤ ‖t₂ - t₁‖ + ‖t₁ - x‖ := by
      rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
      exact dist_triangle _ _ _
    linarith [hs1, hs2, hs3, hA, hB, ht₂, ht₁x, hp₂b, hp₁b, hδdef]
  -- ## 12. the bundle
  · rw [hQkfin, hP₁fin, hP₂fin]
    refine ⟨⟨hI, ?_, ?_⟩, ?_⟩
    · intro q hq
      exact (hp₂mem q hq).1
    · -- the cut avoidance at the final parameter
      have hnorm : ‖tfin - t₂‖ < ρ := by
        have hs1 : ‖tfin - t₂‖ ≤ ‖tfin - t₃‖ + ‖t₃ - t₂‖ := by
          rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
          exact dist_triangle _ _ _
        have hA : ‖tfin - t₃‖ = ‖p₂‖ := by
          show ‖(t₃ + blkSpan (k + 2) p₂) - t₃‖ = ‖p₂‖
          rw [add_sub_cancel_left, norm_blkSpan]
        have hB : ‖t₃ - t₂‖ = ‖p₁‖ := by
          show ‖(t₂ + blkSpan k p₁) - t₂‖ = ‖p₁‖
          rw [add_sub_cancel_left, norm_blkSpan]
        have hp₂b : ‖p₂‖ ≤ ρ / 4 := le_trans (le_of_lt hp₂) hε₂ρ
        have hp₁b : ‖p₁‖ ≤ ρ / 4 := le_trans (le_of_lt hp₁) hε₁ρ
        linarith [hs1, hA, hB, hp₂b, hp₁b, hρpos]
      have hIII := hρsub' tfin hnorm
      rw [CutAvoidsQR] at hIII
      simpa only [← hQkfin, ← hP₂fin] using hIII
    · intro q hq
      exact (hp₂mem q hq).2

/-! ## 5. The node: the reference triple at `k = 0` and `u = ![u, v, v]` -/

theorem dense_T6GenAtDBox_refTriple {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsChartData Q) {QR : ℂ → Work.Drive.CappingSpace} (hQR : Work.Drive.IsSmoothChart QR) (hQRseam : ∀ z : ℂ, ‖z‖ = 1 → QR (-z) = QR z) (u v : UnitAddCircle) (cblk : Fin 3 → ℝ) (hcpos : ∀ k : Fin 3, 0 < cblk k) (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → Work.Drive.levelOf (Q z) > cblk 2) (hlevR : ∀ z : ℂ, ‖z‖ ≤ 1 → Work.Drive.levelOf (QR z) > cblk 2) : ∀ x : EuclideanSpace ℝ (Fin 12), ‖x‖ ≤ 1 → 0 ≤ (Work.Drive.blk 0 x) 0 → ∀ ε : ℝ, 0 < ε → ∃ t : EuclideanSpace ℝ (Fin 12), ‖t - x‖ < ε ∧ Work.Drive.T6GenAtDBox (Work.Drive.blockChart (fun s p => Work.Drive.chartPert s p) Q ![u, v, v] (fun j => Work.Drive.blk j t) 0) (Work.Drive.blockPlane (fun s p => Work.Drive.chartPert s p) Q ![u, v, v] (fun j => Work.Drive.blk j t) 1) (fun y => Work.Drive.chartPert (Work.Drive.blk 2 t) (Work.Drive.diskPlane QR y)) (cblk 1) (cblk 2) := by
  intro x hxle hx0 ε hε
  have hlev' : ∀ z : ℂ, ‖z‖ ≤ 1 → cblk ((0 : Fin 3) + 2) < levelOf (Q z) := by
    intro z hz
    rw [show (0 : Fin 3) + 2 = 2 from by decide]
    exact hlev z hz
  obtain ⟨t, ht, hT⟩ :=
    dense_T6GenAtDBox_split hQ QR hQR ![u, v, v] cblk 0 hcpos hlev' x hxle hx0 ε hε
  have e1 : (0 : Fin 3) + 1 = 1 := by decide
  have e2 : (0 : Fin 3) + 2 = 2 := by decide
  exact ⟨t, ht, by simpa only [e1, e2] using hT⟩

end

end Work.Drive
