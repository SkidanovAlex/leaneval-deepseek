import Mathlib
import Submission.Work.Drive.isOpen_T6GenAtDBox_design
import Submission.Work.Drive.T6GenAtD
import Submission.Work.Drive.perturbedTripleIdentity
import Submission.Work.Drive.SeamSweep
import Submission.Work.Drive.sideGermDefs

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace

noncomputable section

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# Openness of the reference triple's `T6GenAtDBox` bundle in the design parameter

`Work.Drive.isOpen_T6GenAtDBox_design` proves that the transport bundle `T6GenAtDBox` of the design's
triple is open in the design parameter `t`.  The *reference* triple of the `hn2`/`hdense` lanes
differs from the design's in its **third** slot: the plane presentation is the `chartPert`-perturbation
of the reference chart's disk presentation `diskPlane QR` (`QR` the reference plane's smooth chart)
rather than the perturbed *rotated* presentation `rotPresentation Q (u 2)` of the first chart.

Nothing new is needed: every clause of `T6GenAtDBox` is a neighbourhood property of the parameter for a
*jointly smooth* family of loops and chains — the engines
`Work.Drive.eventually_good_meetBox_at`, `Work.Drive.loopBoxData_eventually_at` and the compactness
cover `Work.Drive.eventually_forall_meetBox_of_eventually_smooth` are all generic in the family — and
the cut-avoidance clause is the closed-image argument
`Work.Drive.isOpen_setOf_forall_ne_of_isCompact`.  The work here is to write the three families of the
reference triple, to record that they are jointly smooth (the concrete `chartPert`, the linear `blk`,
the smooth `diskPlane QR`, and the design's own loop-family smoothnesses at block `0`), and to convert
`DiamFamReg` into the pair of `LoopBoxData` clauses that the open-property engine consumes.

The three clauses of `T6GenAtDBox` at the parameter `t` are then handled exactly as in the design:

* clause 1 (core loop vs. the sweep of `P₁`) and clause 2 (diameter loop vs. the sweep of `P₂`) are
  neighbourhood properties of `t` by the meet-box compactness engine;
* clause 3 (the cut avoids the sweep of `P₂`) is open by the closedness of the projection `X × K → X`;
* the `DiamFamReg` clause at every core meet is a neighbourhood property by the pointwise open
  condition `LoopBoxData` (`loopBoxData_eventually_at`).
-/

/-! ## Joint smoothness of the families of the reference triple -/

/-- **The first block's chart is jointly `C^∞`** in `(t, z)`. -/
lemma contMDiff_refChartJoint {Q : ℂ → CappingSpace}
    (hQ : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop Q) (u v : UnitAddCircle) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × ℂ)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin 12) × ℂ =>
        blockChart (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j q.1) 0 q.2) := by
  have h1 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × ℂ)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin 12) × ℂ => blk 0 q.1) :=
    contMDiff_iff_contDiff.mpr (by fun_prop)
  have h2 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × ℂ)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin 12) × ℂ => rotCapping (![u, v, v] 0) (Q q.2)) :=
    (contMDiff_rotCappingAngle (![u, v, v] 0)).comp
      (hQ.comp (contMDiff_iff_contDiff.mpr (by fun_prop)))
  refine (contMDiff_chartPert.comp (h1.prodMk h2)).congr fun q => ?_
  simp only [Function.comp_apply, blockChart]

/-- **The third block's plane family is jointly `C^∞`** in `(t, y)`. -/
lemma contMDiff_refThirdJoint {QR : ℂ → CappingSpace}
    (hQR : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop QR) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2) =>
        chartPert (blk 2 q.1) (diskPlane QR q.2)) := by
  have h1 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2) => blk 2 q.1) :=
    contMDiff_iff_contDiff.mpr (by fun_prop)
  have h2 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2) => diskPlane QR q.2) :=
    (contMDiff_diskPlane hQR).comp (contMDiff_iff_contDiff.mpr (by fun_prop))
  refine (contMDiff_chartPert.comp (h1.prodMk h2)).congr fun q => ?_
  simp only [Function.comp_apply]

/-- **The third block's plane family, as a family over `ℝ¹² × ℝ`** (the parameter space of the
pointwise step of the meet-box engine). -/
lemma contMDiff_refThirdFam {QR : ℂ → CappingSpace}
    (hQR : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop QR) :
    ContMDiff
      (𝓘(ℝ, (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop
      (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2) =>
        chartPert (blk 2 q.1.1) (diskPlane QR q.2)) := by
  have h1 : ContMDiff
      (𝓘(ℝ, (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop
      (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2) => blk 2 q.1.1) :=
    contMDiff_iff_contDiff.mpr (by fun_prop)
  have h2 : ContMDiff
      (𝓘(ℝ, (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop
      (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 2) => diskPlane QR q.2) :=
    (contMDiff_diskPlane hQR).comp (contMDiff_iff_contDiff.mpr (by fun_prop))
  refine (contMDiff_chartPert.comp (h1.prodMk h2)).congr fun q => ?_
  simp only [Function.comp_apply]

/-- **The sweep of the third block's plane is jointly `C^∞`** in `(t, x)`. -/
lemma contMDiff_sweep_refThird (c : ℝ) {QR : ℂ → CappingSpace}
    (hQR : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop QR) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) =>
        clampedSweep c (fun r => 1 - r)
          (fun y => chartPert (blk 2 q.1) (diskPlane QR y)) q.2) := by
  refine (contMDiff_clampedSweep_family_gen (P := EuclideanSpace ℝ (Fin 12)) c (fun r => 1 - r)
    (by fun_prop) (fun t y => chartPert (blk 2 t) (diskPlane QR y))
    (contMDiff_refThirdJoint hQR)).congr fun q => ?_
  rfl

/-- **The sweep of the third block's plane, as a family over `ℝ¹² × ℝ`** (the parameter space of the
pointwise step of the meet-box engine). -/
lemma contMDiff_sweep_refThird_fam (c : ℝ) {QR : ℂ → CappingSpace}
    (hQR : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop QR) :
    ContMDiff
      (𝓘(ℝ, (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
      (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 3) =>
        clampedSweep c (fun r => 1 - r)
          (fun y => chartPert (blk 2 q.1.1) (diskPlane QR y)) q.2) := by
  refine (contMDiff_clampedSweep_family_gen (P := EuclideanSpace ℝ (Fin 12) × ℝ) c (fun r => 1 - r)
    (by fun_prop) (fun p y => chartPert (blk 2 p.1) (diskPlane QR y))
    (contMDiff_refThirdFam hQR)).congr fun q => ?_
  rfl

/-- **`DiamFamReg` is the pair of `LoopBoxData` conditions** of the two deformation families: the four
conjuncts of `DiamFamReg` (in their box-restricted form) are the four conjuncts of the two
`LoopBoxData` bundles, in the same order. -/
lemma diamFamReg_iff_loopBoxData (Q : ℂ → CappingSpace) (θ c : ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) :
    DiamFamReg Q θ c P ↔
      (LoopBoxData (diamFam Q θ) (clampedSweep c (fun r => 1 - r) P) ∧
        LoopBoxData (arcFam Q θ) (clampedSweep c (fun r => 1 - r) P)) :=
  ⟨fun h => ⟨⟨h.1, h.2.1⟩, ⟨h.2.2.1, h.2.2.2⟩⟩, fun h => ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩⟩

/-! ## The openness theorem -/

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
theorem isOpen_T6GenAtDBox_refTriple {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsChartData Q) {QR : ℂ → Work.Drive.CappingSpace} (hQR : Work.Drive.IsSmoothChart QR) (hQRseam : ∀ z : ℂ, ‖z‖ = 1 → QR (-z) = QR z) (u v : UnitAddCircle) (cblk : Fin 3 → ℝ) (hcpos : ∀ k : Fin 3, 0 < cblk k) : IsOpen {t : EuclideanSpace ℝ (Fin 12) | Work.Drive.T6GenAtDBox (Work.Drive.blockChart (fun s p => Work.Drive.chartPert s p) Q ![u, v, v] (fun j => Work.Drive.blk j t) 0) (Work.Drive.blockPlane (fun s p => Work.Drive.chartPert s p) Q ![u, v, v] (fun j => Work.Drive.blk j t) 1) (fun y => Work.Drive.chartPert (Work.Drive.blk 2 t) (Work.Drive.diskPlane QR y)) (cblk 1) (cblk 2)} := by
  rw [isOpen_iff_mem_nhds]
  intro t₀ ht₀
  obtain ⟨⟨hcore, hdiam, hcut⟩, hreg⟩ := ht₀
  have hQm : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop Q := hQ.1
  have hQRm : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop QR := hQR
  -- ## clause 1: the core loop of the first chart against the sweep of the second plane
  have h1 : ∀ᶠ t in 𝓝 t₀, GoodLoopChain
      (coreLoop (blockChart (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j t) 0))
      (clampedSweep (cblk 1) (fun r => 1 - r)
        (blockPlane (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j t) 1)) := by
    refine eventually_good_meetBox_at (P := EuclideanSpace ℝ (Fin 12)) t₀
      (fun t => coreLoop (blockChart (fun s p => chartPert s p) Q ![u, v, v]
        (fun j => blk j t) 0))
      (fun t => clampedSweep (cblk 1) (fun r => 1 - r)
        (blockPlane (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j t) 1)) ?_ ?_ ?_
    · refine (contMDiff_designLoopFam 0 0 ![u, v, v] hQm).congr fun q => ?_
      simp only [coreLoop, blockChart, zero_add]
    · refine (contMDiff_designChainFam_blk 1 ![u, v, v] cblk hQm).congr fun q => ?_
      rfl
    · exact hcore
  -- ## clause 2: at every core meet, the diameter loop against the sweep of the third plane
  have h2 : ∀ᶠ t in 𝓝 t₀, ∀ q ∈ coreMeet
      (blockChart (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j t) 0) (cblk 1)
      (blockPlane (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j t) 1),
      GoodLoopChain
        (diamLoop (blockChart (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j t) 0) q.1)
        (clampedSweep (cblk 2) (fun r => 1 - r)
          (fun y => chartPert (blk 2 t) (diskPlane QR y))) := by
    classical
    set L : EuclideanSpace ℝ (Fin 12) → ℝ → CappingSpace := fun p θ =>
      coreLoop (blockChart (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j p) 0) θ with hL
    set D : EuclideanSpace ℝ (Fin 12) → EuclideanSpace ℝ (Fin 3) → CappingSpace := fun p x =>
      clampedSweep (cblk 1) (fun r => 1 - r)
        (blockPlane (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j p) 1) x with hD
    have hmeetEq : ∀ p : EuclideanSpace ℝ (Fin 12), meetBox (L p) (D p) =
        coreMeet (blockChart (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j p) 0)
          (cblk 1)
          (blockPlane (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j p) 1) :=
      fun p => rfl
    have hLfam : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × ℝ)) (𝓡 4) Ctop
        (fun q : EuclideanSpace ℝ (Fin 12) × ℝ => L q.1 q.2) := by
      refine (contMDiff_designLoopFam 0 0 ![u, v, v] hQm).congr fun q => ?_
      simp only [hL, coreLoop, blockChart, zero_add]
    have hDfam : ContMDiff
        (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
        (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) => D q.1 q.2) := by
      refine (contMDiff_designChainFam_blk 1 ![u, v, v] cblk hQm).congr fun q => ?_
      rfl
    have hprop : ∀ ξ ∈ meetBox (L t₀) (D t₀),
        ∀ᶠ z in 𝓝 ((t₀, ξ.1) : EuclideanSpace ℝ (Fin 12) × ℝ),
          GoodLoopChain
            (diamLoop (blockChart (fun s p => chartPert s p) Q ![u, v, v]
              (fun j => blk j z.1) 0) z.2)
            (clampedSweep (cblk 2) (fun r => 1 - r)
              (fun y => chartPert (blk 2 z.1) (diskPlane QR y))) := by
      intro ξ hξ
      have hbase : GoodLoopChain
          (diamLoop (blockChart (fun s p => chartPert s p) Q ![u, v, v]
            (fun j => blk j t₀) 0) ξ.1)
          (clampedSweep (cblk 2) (fun r => 1 - r)
            (fun y => chartPert (blk 2 t₀) (diskPlane QR y))) :=
        hdiam ξ (by rw [← hmeetEq t₀]; exact hξ)
      set L' : (EuclideanSpace ℝ (Fin 12) × ℝ) → ℝ → CappingSpace := fun p σ =>
        diamLoop (blockChart (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j p.1) 0) p.2
          σ with hL'
      set D' : (EuclideanSpace ℝ (Fin 12) × ℝ) → EuclideanSpace ℝ (Fin 3) → CappingSpace :=
        fun p x => clampedSweep (cblk 2) (fun r => 1 - r)
          (fun y => chartPert (blk 2 p.1) (diskPlane QR y)) x with hD'
      have hL'fam : ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin 12) × ℝ) × ℝ)) (𝓡 4) Ctop
          (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × ℝ => L' q.1 q.2) := by
        refine (contMDiff_diamFam_design 0 ![u, v, v] hQm).congr fun q => ?_
        simp only [hL']
      have hD'fam : ContMDiff
          (𝓘(ℝ, (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
          (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 3) =>
            D' q.1 q.2) := by
        refine (contMDiff_sweep_refThird_fam (cblk 2) hQRm).congr fun q => ?_
        simp only [hD']
      have hbase' : GoodLoopChain (L' (t₀, ξ.1)) (D' (t₀, ξ.1)) := by
        simp only [hL', hD']
        exact hbase
      refine (eventually_good_meetBox_at
        (p₀ := ((t₀, ξ.1) : EuclideanSpace ℝ (Fin 12) × ℝ))
        L' D' hL'fam hD'fam hbase').mono ?_
      intro p hp
      exact hp
    refine (eventually_forall_meetBox_of_eventually_smooth (p₀ := t₀) hLfam hDfam
      (fun p θ => GoodLoopChain
        (diamLoop (blockChart (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j p) 0) θ)
        (clampedSweep (cblk 2) (fun r => 1 - r)
          (fun y => chartPert (blk 2 p) (diskPlane QR y)))) hprop).mono ?_
    intro t ht q hq
    exact ht q (by rw [hmeetEq t]; exact hq)
  -- ## clause 3: the cut of the first chart avoids the sweep of the third plane
  have h3 : ∀ᶠ t in 𝓝 t₀, ∃ δc : ℝ, 0 < δc ∧ ∀ x : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ δc →
      x ∉ diskCut (blockChart (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j t) 0)
        (clampedSweep (cblk 2) (fun r => 1 - r)
          (fun y => chartPert (blk 2 t) (diskPlane QR y))) := by
    have hiff : ∀ t : EuclideanSpace ℝ (Fin 12),
        (∃ δc : ℝ, 0 < δc ∧ ∀ x : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ δc →
          x ∉ diskCut (blockChart (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j t) 0)
            (clampedSweep (cblk 2) (fun r => 1 - r)
              (fun y => chartPert (blk 2 t) (diskPlane QR y)))) ↔
          ∀ x ∈ Submission.Drive.unitBox 2,
            clampedSweep (cblk 2) (fun r => 1 - r)
              (fun y => chartPert (blk 2 t) (diskPlane QR y)) x
              ≠ blockChart (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j t) 0 0 := by
      intro t
      have hcont1 : Continuous (fun z : ℂ =>
          blockChart (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j t) 0 z) := by
        have hjoint := contMDiff_chartPert.continuous
        have hlin : Continuous fun z : ℂ =>
            (((blk 0 t, rotCapping (![u, v, v] 0) (Q z))) :
              EuclideanSpace ℝ (Fin 4) × CappingSpace) :=
          continuous_const.prodMk ((continuous_rotCapping (![u, v, v] 0)).comp hQm.continuous)
        have hfun : (fun z : ℂ =>
              blockChart (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j t) 0 z)
            = (fun q : EuclideanSpace ℝ (Fin 4) × CappingSpace => chartPert q.1 q.2) ∘
              (fun z : ℂ => (blk 0 t, rotCapping (![u, v, v] 0) (Q z))) := by
          funext z
          simp only [blockChart, Function.comp_apply]
        rw [hfun]
        exact hjoint.comp hlin
      have hcont2 : Continuous
          (clampedSweep (cblk 2) (fun r => 1 - r)
            (fun y => chartPert (blk 2 t) (diskPlane QR y))) := by
        have hjoint : Continuous (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) =>
            clampedSweep (cblk 2) (fun r => 1 - r)
              (fun y => chartPert (blk 2 q.1) (diskPlane QR y)) q.2) :=
          (contMDiff_sweep_refThird (cblk 2) hQRm).continuous
        have hcomp := hjoint.comp (f := fun x : EuclideanSpace ℝ (Fin 3) =>
          (t, x)) (continuous_const.prodMk continuous_id)
        simpa only [Function.comp_def] using hcomp
      rw [exists_deltaC_iff_notMem _ _ hcont1 hcont2]
      constructor
      · rintro h x hx heq
        exact h ⟨x, hx, heq⟩
      · rintro h ⟨x, hx, heq⟩
        exact h x hx heq
    have hcontS : Continuous (Function.uncurry (fun (t : EuclideanSpace ℝ (Fin 12))
        (x : EuclideanSpace ℝ (Fin 3)) =>
        clampedSweep (cblk 2) (fun r => 1 - r)
          (fun y => chartPert (blk 2 t) (diskPlane QR y)) x)) :=
      (contMDiff_sweep_refThird (cblk 2) hQRm).continuous
    have hcontC : Continuous (fun t : EuclideanSpace ℝ (Fin 12) =>
        blockChart (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j t) 0 0) := by
      have hjoint := contMDiff_chartPert.continuous
      have hlin : Continuous fun t : EuclideanSpace ℝ (Fin 12) =>
          (((blk 0 t, rotCapping (![u, v, v] 0) (Q 0))) :
            EuclideanSpace ℝ (Fin 4) × CappingSpace) :=
        (blk 0).continuous.prodMk continuous_const
      have hfun : (fun t : EuclideanSpace ℝ (Fin 12) =>
            blockChart (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j t) 0 0)
          = (fun q : EuclideanSpace ℝ (Fin 4) × CappingSpace => chartPert q.1 q.2) ∘
            (fun t : EuclideanSpace ℝ (Fin 12) =>
              (blk 0 t, rotCapping (![u, v, v] 0) (Q 0))) := by
        funext t
        simp only [blockChart, Function.comp_apply]
      rw [hfun]
      exact hjoint.comp hlin
    have hopen := isOpen_setOf_forall_ne_of_isCompact (K := Submission.Drive.unitBox 2)
      (isCompact_unitBox 2) hcontS hcontC
    have hmem : t₀ ∈ {t : EuclideanSpace ℝ (Fin 12) | ∀ x ∈ Submission.Drive.unitBox 2,
        clampedSweep (cblk 2) (fun r => 1 - r)
          (fun y => chartPert (blk 2 t) (diskPlane QR y)) x
          ≠ blockChart (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j t) 0 0} :=
      (hiff t₀).mp hcut
    have hmem' : ∀ᶠ t in 𝓝 t₀, ∀ x ∈ Submission.Drive.unitBox 2,
        clampedSweep (cblk 2) (fun r => 1 - r)
          (fun y => chartPert (blk 2 t) (diskPlane QR y)) x
          ≠ blockChart (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j t) 0 0 :=
      hopen.mem_nhds hmem
    exact hmem'.mono fun t ht => (hiff t).mpr ht
  -- ## clause 4: the family regularity at every core meet
  have h4 : ∀ᶠ t in 𝓝 t₀, ∀ q ∈ coreMeet
      (blockChart (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j t) 0) (cblk 1)
      (blockPlane (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j t) 1),
      DiamFamReg (blockChart (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j t) 0) q.1
        (cblk 2) (fun y => chartPert (blk 2 t) (diskPlane QR y)) := by
    classical
    set L : EuclideanSpace ℝ (Fin 12) → ℝ → CappingSpace := fun p θ =>
      coreLoop (blockChart (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j p) 0) θ with hL
    set D : EuclideanSpace ℝ (Fin 12) → EuclideanSpace ℝ (Fin 3) → CappingSpace := fun p x =>
      clampedSweep (cblk 1) (fun r => 1 - r)
        (blockPlane (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j p) 1) x with hD
    have hmeetEq : ∀ p : EuclideanSpace ℝ (Fin 12), meetBox (L p) (D p) =
        coreMeet (blockChart (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j p) 0)
          (cblk 1)
          (blockPlane (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j p) 1) :=
      fun p => rfl
    have hLfam : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × ℝ)) (𝓡 4) Ctop
        (fun q : EuclideanSpace ℝ (Fin 12) × ℝ => L q.1 q.2) := by
      refine (contMDiff_designLoopFam 0 0 ![u, v, v] hQm).congr fun q => ?_
      simp only [hL, coreLoop, blockChart, zero_add]
    have hDfam : ContMDiff
        (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
        (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) => D q.1 q.2) := by
      refine (contMDiff_designChainFam_blk 1 ![u, v, v] cblk hQm).congr fun q => ?_
      rfl
    refine (eventually_forall_meetBox_of_eventually_smooth (p₀ := t₀) hLfam hDfam
      (fun p θ => DiamFamReg (blockChart (fun s p => chartPert s p) Q ![u, v, v]
        (fun j => blk j p) 0) θ (cblk 2)
        (fun y => chartPert (blk 2 p) (diskPlane QR y))) ?_).mono ?_
    · intro ξ hξ
      have hbase : DiamFamReg (blockChart (fun s p => chartPert s p) Q ![u, v, v]
          (fun j => blk j t₀) 0) ξ.1 (cblk 2)
          (fun y => chartPert (blk 2 t₀) (diskPlane QR y)) :=
        hreg ξ (by rw [← hmeetEq t₀]; exact hξ)
      have hbase' : LoopBoxData
            (diamFam (blockChart (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j t₀) 0)
              ξ.1)
            (clampedSweep (cblk 2) (fun r => 1 - r)
              (fun y => chartPert (blk 2 t₀) (diskPlane QR y))) ∧
          LoopBoxData
            (arcFam (blockChart (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j t₀) 0)
              ξ.1)
            (clampedSweep (cblk 2) (fun r => 1 - r)
              (fun y => chartPert (blk 2 t₀) (diskPlane QR y))) :=
        (diamFamReg_iff_loopBoxData _ _ _ _).mp hbase
      refine (loopBoxData_eventually_at (p₀ := ((t₀, ξ.1) : EuclideanSpace ℝ (Fin 12) × ℝ))
        (A := fun p : EuclideanSpace ℝ (Fin 12) × ℝ =>
          diamFam (blockChart (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j p.1) 0) p.2)
        (A' := fun p : EuclideanSpace ℝ (Fin 12) × ℝ =>
          arcFam (blockChart (fun s p => chartPert s p) Q ![u, v, v] (fun j => blk j p.1) 0) p.2)
        (D := fun p : EuclideanSpace ℝ (Fin 12) × ℝ =>
          clampedSweep (cblk 2) (fun r => 1 - r)
            (fun y => chartPert (blk 2 p.1) (diskPlane QR y)))
        ?_ ?_ ?_ hbase'.1 hbase'.2).mono ?_
      · refine (contMDiff_diamFam_loopFam_design 0 ![u, v, v] hQm).congr fun q => ?_
        rfl
      · refine (contMDiff_arcFam_loopFam_design 0 ![u, v, v] hQm).congr fun q => ?_
        rfl
      · exact contMDiff_sweep_refThird_fam (cblk 2) hQRm
      · intro p hp
        exact (diamFamReg_iff_loopBoxData _ _ _ _).mpr hp
    · intro t ht q hq
      exact ht q (by rw [hmeetEq t]; exact hq)
  -- ## assembly of the four clauses
  filter_upwards [h1, h2, h3, h4] with t h1t h2t h3t h4t
  exact ⟨⟨h1t, h2t, h3t⟩, h4t⟩

end

end Work.Drive
