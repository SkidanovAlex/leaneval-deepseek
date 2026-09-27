import Mathlib
import Submission.Work.Drive.meetBoxForallEventual
import Submission.Work.Drive.goodPair_pertChart_isOpen
import Submission.Work.Drive.eventually_goodLoopChain_design
import Submission.Work.Drive.collapseTransport
import Submission.Work.Drive.T6GenAtDefs
import Submission.Work.Drive.sideCountDefs
import Submission.Work.Drive.chartShiftHsurj
import Submission.Work.Drive.perturbedTripleIdentity

/-!
# The diameter clause of the design is open in the design parameter

The design's second pair of `T6` factors (the ones at the level `cblk (k + 2)`) is the clause

> `∀ q ∈ coreMeet (blockChart k) (cblk (k+1)) (blockPlane (k+1)),
>      GoodLoopChain (diamLoop (blockChart k) q.1) (clampedSweep (cblk (k+2)) (blockPlane (k+2)))`

at the design's parameter `t`.  This module proves that this clause is a **neighbourhood property of
the design parameter `t`** (`Work.Drive.diamClause_design_eventually`), which is the openness half of
the sequential production of `DesignTripleAt` (the density half is
`Work.Drive.exists_diamClause_design_update`, `hdenseDiamClause.lean`).

The proof is the compactness/upper-semicontinuity engine of `meetBoxForallEventual.lean`:

* the loop of the meet is `coreLoop (blockChart t k)` and the chain is
  `clampedSweep (cblk (k+1)) (blockPlane t (k+1))`, so the meet set is `coreMeet` of the pair `(k, k+1)`
  (definitionally, `hmeetEq`);
* the joint continuity of the meet family in `(t, θ, x)` is the design family smoothness
  (`Work.Drive.contMDiff_designLoopFam`, `Work.Drive.contMDiff_designChainFam`, at the unshifted
  parameter `0`);
* the pointwise input is that `GoodLoopChain` is a neighbourhood property of a *loop family*
  (`Work.Drive.eventually_good_meetBox_at`), applied to the diameter-loop family
  `(t, θ) ↦ (σ ↦ diamLoop (blockChart t k) θ σ)` and to the chain of the block `k + 2`; the joint
  smoothness of that family is `Work.Drive.contMDiff_diamFam_design` below, and the chain smoothness
  at an arbitrary block index is `Work.Drive.contMDiff_designChainFam_blk`.

Everything here is sorry-free.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

noncomputable section

/-! ## Smoothness of the design's families at the unshifted `12`-parameter -/

/-- **The chain family of an arbitrary block `j` of the design is jointly `C^∞`** in the parameter
`t ∈ ℝ¹²`.  This is `Work.Drive.contMDiff_designChainFam` without the shift by `t₀` and for an
arbitrary block index (the design needs the chains of the blocks `k+1` *and* `k+2` at the same
parameter). -/
lemma contMDiff_designChainFam_blk (j : Fin 3) (u : Fin 3 → UnitAddCircle) (cblk : Fin 3 → ℝ)
    {Q : ℂ → CappingSpace} (hQ : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop Q) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) =>
        clampedSweep (cblk j) (fun r => 1 - r)
          (blockPlane (fun s p => chartPert s p) Q u (fun i => blk i q.1) j) q.2) := by
  have hrot : ContMDiff (𝓡 2) (𝓡 4) Ctop (rotPresentation Q (u j)) :=
    contMDiff_rotPresentation_of_contMDiff (u j) hQ
  have hPp : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2) =>
        chartPert (blk j q.1) (rotPresentation Q (u j) q.2)) := by
    have h1 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop
        (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2) => blk j q.1) :=
      contMDiff_iff_contDiff.mpr (by fun_prop)
    have h2 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop
        (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2) =>
          rotPresentation Q (u j) q.2) :=
      hrot.comp (contMDiff_iff_contDiff.mpr (by fun_prop))
    have hmain := contMDiff_chartPert.comp (h1.prodMk h2)
    refine hmain.congr fun q => ?_
    simp only [Function.comp_apply]
  have hmain := contMDiff_clampedSweep_family_gen (P := EuclideanSpace ℝ (Fin 12))
    (cblk j) (fun r : ℝ => 1 - r) (by fun_prop)
    (fun q (y : EuclideanSpace ℝ (Fin 2)) => chartPert (blk j q) (rotPresentation Q (u j) y)) hPp
  refine hmain.congr fun q => ?_
  rfl

/-- **The diameter-loop family of the design's block `k` is jointly `C^∞`** in the pair `(t, θ)` formed
by the design parameter and the *angle* of the diameter: the loop is `σ ↦ blockChart k t ((1-2σ)e^{iπθ})`,
so both the chart parameter and the angle move.  This is the smoothness input of the openness of the
diameter clause. -/
lemma contMDiff_diamFam_design {Q : ℂ → CappingSpace}
    (k : Fin 3) (u : Fin 3 → UnitAddCircle)
    (hQ : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop Q) :
    ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin 12) × ℝ) × ℝ)) (𝓡 4) Ctop
      (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × ℝ =>
        diamLoop (blockChart (fun s p => chartPert s p) Q u (fun j => blk j q.1.1) k) q.1.2 q.2) := by
  have hz : ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin 12) × ℝ) × ℝ)) (𝓘(ℝ, ℂ)) Ctop
      (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × ℝ =>
        (1 - 2 * q.2) * Complex.exp (Real.pi * (q.1.2 : ℂ) * Complex.I)) := by
    rw [contMDiff_iff_contDiff]
    have h1 : ContDiff ℝ Ctop
        (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × ℝ => (1 : ℂ) - (2 : ℂ) * (q.2 : ℂ)) :=
      contDiff_const.sub (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        (by fun_prop : ContDiff ℝ Ctop
          (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × ℝ => q.2))))
    have h2 : ContDiff ℝ Ctop
        (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × ℝ =>
          Complex.exp ((Real.pi : ℂ) * (q.1.2 : ℂ) * Complex.I)) :=
      Complex.contDiff_exp.comp
        (((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
          (by fun_prop : ContDiff ℝ Ctop
            (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × ℝ => q.1.2)))).mul contDiff_const))
    exact h1.mul h2
  have hG1 : ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin 12) × ℝ) × ℝ)) (𝓡 4) Ctop
      (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × ℝ => blk k q.1.1) :=
    contMDiff_iff_contDiff.mpr (by fun_prop)
  have hG2 : ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin 12) × ℝ) × ℝ)) (𝓡 4) Ctop
      (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × ℝ =>
        rotCapping (u k) (Q ((1 - 2 * q.2) * Complex.exp (Real.pi * (q.1.2 : ℂ) * Complex.I)))) :=
    (contMDiff_rotCappingAngle (u k)).comp (hQ.comp hz)
  have hmain := contMDiff_chartPert.comp (hG1.prodMk hG2)
  refine hmain.congr fun q => ?_
  simp only [Function.comp_apply, blockChart, diamLoop]

/-! ## The openness of the diameter clause -/

theorem diamClause_design_eventually {Q : ℂ → Work.Drive.CappingSpace}
    (hQ : Work.Drive.IsChartData Q)
    (u : Fin 3 → UnitAddCircle) (cblk : Fin 3 → ℝ) (k : Fin 3)
    {t₀ : EuclideanSpace ℝ (Fin 12)}
    (h : ∀ q ∈ Work.Drive.coreMeet
        (Work.Drive.blockChart (fun s p => Work.Drive.chartPert s p) Q u
          (fun j => Work.Drive.blk j t₀) k)
        (cblk (k + 1))
        (Work.Drive.blockPlane (fun s p => Work.Drive.chartPert s p) Q u
          (fun j => Work.Drive.blk j t₀) (k + 1)),
      Work.Drive.GoodLoopChain
        (Work.Drive.diamLoop
          (Work.Drive.blockChart (fun s p => Work.Drive.chartPert s p) Q u
            (fun j => Work.Drive.blk j t₀) k) q.1)
        (Work.Drive.clampedSweep (cblk (k + 2)) (fun r => 1 - r)
          (Work.Drive.blockPlane (fun s p => Work.Drive.chartPert s p) Q u
            (fun j => Work.Drive.blk j t₀) (k + 2)))) :
    Filter.Eventually (fun t : EuclideanSpace ℝ (Fin 12) =>
      ∀ q ∈ Work.Drive.coreMeet
        (Work.Drive.blockChart (fun s p => Work.Drive.chartPert s p) Q u
          (fun j => Work.Drive.blk j t) k)
        (cblk (k + 1))
        (Work.Drive.blockPlane (fun s p => Work.Drive.chartPert s p) Q u
          (fun j => Work.Drive.blk j t) (k + 1)),
      Work.Drive.GoodLoopChain
        (Work.Drive.diamLoop
          (Work.Drive.blockChart (fun s p => Work.Drive.chartPert s p) Q u
            (fun j => Work.Drive.blk j t) k) q.1)
        (Work.Drive.clampedSweep (cblk (k + 2)) (fun r => 1 - r)
          (Work.Drive.blockPlane (fun s p => Work.Drive.chartPert s p) Q u
            (fun j => Work.Drive.blk j t) (k + 2)))) (nhds t₀) := by
  classical
  have hQm : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop Q := hQ.1
  -- the loop and the chain of the *meet* (the design's pair `(k, k+1)`)
  set L : EuclideanSpace ℝ (Fin 12) → ℝ → CappingSpace := fun p θ =>
    coreLoop (blockChart (fun s p => chartPert s p) Q u (fun j => blk j p) k) θ with hL
  set D : EuclideanSpace ℝ (Fin 12) → EuclideanSpace ℝ (Fin 3) → CappingSpace := fun p x =>
    clampedSweep (cblk (k + 1)) (fun r => 1 - r)
      (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j p) (k + 1)) x with hD
  -- the clause to be shown eventual
  set R : EuclideanSpace ℝ (Fin 12) → ℝ → Prop := fun p θ =>
    GoodLoopChain (diamLoop (blockChart (fun s p => chartPert s p) Q u (fun j => blk j p) k) θ)
      (clampedSweep (cblk (k + 2)) (fun r => 1 - r)
        (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j p) (k + 2))) with hR
  have hmeetEq : ∀ p : EuclideanSpace ℝ (Fin 12), meetBox (L p) (D p) =
      coreMeet (blockChart (fun s p => chartPert s p) Q u (fun j => blk j p) k)
        (cblk (k + 1))
        (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j p) (k + 1)) := fun p => rfl
  -- joint smoothness of the two families of the meet
  have hLfam : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × ℝ)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin 12) × ℝ => L q.1 q.2) := by
    refine (contMDiff_designLoopFam k 0 u hQm).congr fun q => ?_
    simp only [zero_add, hL, coreLoop, blockChart]
  have hDfam : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) => D q.1 q.2) := by
    refine (contMDiff_designChainFam k 0 u cblk hQm).congr fun q => ?_
    simp only [zero_add, hD]
  -- hence the meet family is continuous in the parameter (the `.congr` + `rfl` form is what keeps the
  -- unification cheap: a direct `have` forces `whnf` on the local definitions `L`, `D`)
  have hLc : Continuous (fun q : EuclideanSpace ℝ (Fin 12) × (ℝ × EuclideanSpace ℝ (Fin 3)) =>
      L q.1 q.2.1) :=
    (hLfam.continuous.comp (f := fun q : EuclideanSpace ℝ (Fin 12) ×
        (ℝ × EuclideanSpace ℝ (Fin 3)) => (q.1, q.2.1)) (by fun_prop)).congr fun q => rfl
  have hDc : Continuous (fun q : EuclideanSpace ℝ (Fin 12) × (ℝ × EuclideanSpace ℝ (Fin 3)) =>
      D q.1 q.2.2) :=
    (hDfam.continuous.comp (f := fun q : EuclideanSpace ℝ (Fin 12) ×
        (ℝ × EuclideanSpace ℝ (Fin 3)) => (q.1, q.2.2)) (by fun_prop)).congr fun q => rfl
  have hc : Continuous (fun q : EuclideanSpace ℝ (Fin 12) × (ℝ × EuclideanSpace ℝ (Fin 3)) =>
      (L q.1 q.2.1, D q.1 q.2.2)) := hLc.prodMk hDc
  -- the pointwise input: at a base meet the clause is open in `(t, θ)`
  have hprop : ∀ ξ ∈ meetBox (L t₀) (D t₀),
      ∀ᶠ z in 𝓝 ((t₀, ξ.1) : EuclideanSpace ℝ (Fin 12) × ℝ), R z.1 z.2 := by
    intro ξ hξ
    have hξ' : ξ ∈ coreMeet (blockChart (fun s p => chartPert s p) Q u (fun j => blk j t₀) k)
        (cblk (k + 1))
        (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t₀) (k + 1)) := by
      rw [← hmeetEq t₀]
      exact hξ
    have hbase := h ξ hξ'
    -- the family `(t, θ) ↦ (diam loop, chain of the block k+2)`
    set L' : (EuclideanSpace ℝ (Fin 12) × ℝ) → ℝ → CappingSpace := fun p σ =>
      diamLoop (blockChart (fun s p => chartPert s p) Q u (fun j => blk j p.1) k) p.2 σ with hL'
    set D' : (EuclideanSpace ℝ (Fin 12) × ℝ) → EuclideanSpace ℝ (Fin 3) → CappingSpace := fun p x =>
      clampedSweep (cblk (k + 2)) (fun r => 1 - r)
        (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j p.1) (k + 2)) x with hD'
    have hL'fam : ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin 12) × ℝ) × ℝ)) (𝓡 4) Ctop
        (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × ℝ => L' q.1 q.2) := by
      refine (contMDiff_diamFam_design k u hQm).congr fun q => ?_
      simp only [hL']
    have hD'fam : ContMDiff
        (𝓘(ℝ, (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
        (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 3) => D' q.1 q.2) := by
      have hp : ContMDiff
          (𝓘(ℝ, (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 3)))
          (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3))) Ctop
          (fun q : (EuclideanSpace ℝ (Fin 12) × ℝ) × EuclideanSpace ℝ (Fin 3) =>
            (q.1.1, q.2)) :=
        contMDiff_iff_contDiff.mpr (by fun_prop)
      refine ((contMDiff_designChainFam_blk (k + 2) u cblk hQm).comp hp).congr fun q => ?_
      simp only [Function.comp_apply, hD']
    have hbase' : GoodLoopChain (L' (t₀, ξ.1)) (D' (t₀, ξ.1)) := by
      simp only [hL', hD']
      exact hbase
    refine (eventually_good_meetBox_at
      (p₀ := ((t₀, ξ.1) : EuclideanSpace ℝ (Fin 12) × ℝ)) L' D' hL'fam hD'fam hbase').mono ?_
    intro p hp
    simpa only [hR] using hp
  -- the compactness engine
  have hEv := eventually_forall_meetBox_of_eventually (P := EuclideanSpace ℝ (Fin 12)) (p₀ := t₀)
    (L := L) (D := D) hc R hprop
  refine hEv.mono fun t ht => ?_
  intro q hq
  exact ht q (by rw [hmeetEq t]; exact hq)

end

end Work.Drive
