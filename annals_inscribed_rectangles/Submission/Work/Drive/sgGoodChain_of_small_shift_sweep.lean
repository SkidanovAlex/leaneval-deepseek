import Mathlib
import Submission.Work.Drive.hdenseDiamBridge
import Submission.Work.Drive.T6GenAtDefs
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.sgAssembly
import Submission.Work.Drive.goodPair_pertChart_isOpen
import Submission.Work.Drive.goodPair_pertChart_exists_near
import Submission.Work.Drive.localSard
import Submission.Work.Drive.sgPiecesDefs
import Submission.Work.Drive.gatherCLM_mem_unitBox
import Submission.Work.Drive.sgFace_gatherCLM
import Submission.Work.Drive.contMDiff_clampedSweep_family
import Submission.Work.Drive.levelOf_clampedSweep
import Submission.Work.Drive.clampedSweepLevel
import Submission.Work.Drive.sweepTripleGeneric
import Submission.Work.Drive.contDiffAt_chartDiff_family_fin
import Submission.Work.Drive.exists_forall_good_and_notMem_family_multi
import Submission.Work.Drive.exists_compact_chart_cover
import Submission.Work.Drive.exists_pos_norm_le_mem_of_compact
import Submission.Work.Drive.exists_pos_norm_subset_of_isCompact_subset_isOpen
import Submission.Work.Drive.range_mfderiv_comp_surjective_linear
import Submission.Work.Drive.finite_loopChainMeet_of_transverse
import Submission.Work.Drive.chartDiffRangeBridge

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# The mirror of the germ-route Sard: a small shift of the *chain's* chart

`Work.Drive.sgGoodPair_of_small_shift` (`goodPair_pertChart_exists_near.lean`) perturbs the chart of
the *loop* and keeps the chain (the clamped sweep of a fixed plane presentation) fixed.  This module
proves the **mirror**: the loop `L` is a fixed smooth loop (with its image in the levels `> c`), and
the chart of the *chain* is perturbed, i.e.

> for every `ε₀ > 0` there is `p` with `‖p‖ < ε₀` and
> `GoodLoopChain L (clampedSweep c (1 - ·) (diskPlane (Ξ (s₀+p) ∘ Q)))`.

The outer structure is that of `sgAssembly.lean` (chart cover of the loop image, the `psg`-style
compact projections `K i`, cut-off-scaled charted difference systems, the parametric-Sard brick
`Work.Drive.exists_forall_good_and_notMem_family_multi`, and the conversion of the two generic
clauses into transversality — through `range_sup_eq_top_of_chartDiff_surjective` — and interiority —
through the avoidance clause on the eight boundary pieces `sgFace`).

The two *new* analytic inputs (all the others are on disk) are

* `Work.Drive.hsurj_sweepFam` — the parameter-derivative of the *charted chain* is onto: the family
  is the composite of `t ↦ Ξ (s₀+t) (diskPlane Q y)` (onto by `ChartPert`) with the radial dilation
  `dil`, whose differential is invertible exactly when the radial parameter is nonzero — this is the
  proved brick `Work.Drive.surjective_fderiv_chart_clampedSweep_ne_zero`
  (`sweepTripleGeneric.lean`), transported along the shift `s₀ + ·`;
* the **level band** `hlev : ∀ t, c < levelOf (L t)` enters exactly here: at a meet, if the chain's
  radial parameter vanished, the chain's value would lie in the level `c` (`clampedSweep_face_zero`),
  contradicting the loop's level.  So every meet of the (perturbed) system has nonzero radial
  parameter, which is precisely the hypothesis of the brick.
-/

namespace Work.Drive

open Manifold Filter Set Metric
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

/-- The differentiability order `⊤` is not zero. -/
private lemma sgg_top_ne_zero : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
  rw [ne_eq, ← WithTop.coe_zero]
  intro h
  exact ENat.top_ne_zero (WithTop.coe_injective h)


private lemma sgg_sqIdx_zero : sqIdx (0 : Fin 2) = (0 : Fin 5) := rfl

/-- The point `a` of `ℝ¹`. -/
private def sggMk1 (a : ℝ) : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ => a)

@[simp] private lemma sggMk1_apply (a : ℝ) (i : Fin 1) : sggMk1 a i = a := by
  simp [sggMk1]

private lemma sgg_sqPart_zero (z : Amb 4) : (sqPart z).ofLp 0 = z.ofLp 0 := by
  rw [sqPart_apply, sgg_sqIdx_zero]

/-! ## 1. The loop side: the fixed loop, read through the first square coordinate -/

/-- **The loop of the mirror** as a map on the square block: the loop parameter is the first
coordinate, the second is a dummy. -/
def sggLoopFam (L : ℝ → CappingSpace) : EuclideanSpace ℝ (Fin 2) → CappingSpace := fun u => L (u 0)

@[simp] lemma sggLoopFam_apply (L : ℝ → CappingSpace) (u : EuclideanSpace ℝ (Fin 2)) :
    sggLoopFam L u = L (u 0) := rfl

lemma sggLoopFam_eq (L : ℝ → CappingSpace) :
    sggLoopFam L = fun u : EuclideanSpace ℝ (Fin 2) => L (u 0) := rfl

/-- **Smoothness of the loop of the mirror.** -/
theorem contMDiff_sggLoopFam {L : ℝ → CappingSpace} (hL : IsSmoothLoop L) :
    ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : EuclideanSpace ℝ (Fin 2) => L (u 0)) := by
  have hdiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : EuclideanSpace ℝ (Fin 2) => u 0) := by
    have hL' : (fun u : EuclideanSpace ℝ (Fin 2) => u 0)
        = ⇑(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0) := rfl
    rw [hL']
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
  have hproj : ContMDiff (𝓡 2) (𝓘(ℝ, ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : EuclideanSpace ℝ (Fin 2) => u 0) :=
    contMDiff_iff_contDiff.mpr hdiff
  exact hL.comp hproj

/-! ## 2. The chain side: the clamped sweep of the perturbed chart -/

/-- **Joint smoothness of the perturbed-plane family** `(t, y) ↦ Ξ t (diskPlane Q y)`. -/
theorem contMDiff_sggPertPlane_fam {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2))) (𝓡 4)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) =>
        Ξ q.1 (diskPlane Q q.2)) := by
  have hfst : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2)))
      (𝓡 m) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) => q.1) :=
    contMDiff_iff_contDiff.mpr (by fun_prop)
  have hsnd : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2)))
      (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) => diskPlane Q q.2) :=
    (contMDiff_diskPlane hQ).comp (contMDiff_iff_contDiff.mpr (by fun_prop))
  have h := hΞ.2.1.comp (hfst.prodMk hsnd)
  simpa only [Function.comp_def] using h

/-- **Joint smoothness of the shifted perturbed-plane family** `(t, y) ↦ Ξ (s₀+t) (diskPlane Q y)`. -/
theorem contMDiff_sggPertPlane_fam_shift {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (s0 : EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2))) (𝓡 4)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) =>
        Ξ (s0 + q.1) (diskPlane Q q.2)) := by
  have hfst : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2)))
      (𝓡 m) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) => s0 + q.1) :=
    contMDiff_iff_contDiff.mpr (by fun_prop)
  have hsnd : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2)))
      (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) => diskPlane Q q.2) :=
    (contMDiff_diskPlane hQ).comp (contMDiff_iff_contDiff.mpr (by fun_prop))
  have h := hΞ.2.1.comp (hfst.prodMk hsnd)
  simpa only [Function.comp_def] using h

/-- **Joint smoothness of the unshifted chain family** `(t, x) ↦ clampedSweep c (1 - ·) (Ξ t ∘ P) x`. -/
theorem contMDiff_sggSweepFam_zero {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3))) (𝓡 4)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) =>
        clampedSweep c (fun s => 1 - s) (fun y => Ξ q.1 (diskPlane Q y)) q.2) := by
  have hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => 1 - s) := by fun_prop
  exact contMDiff_clampedSweep_family (P := EuclideanSpace ℝ (Fin m)) c
    (fun s : ℝ => 1 - s) hψ (fun t y => Ξ t (diskPlane Q y))
    (contMDiff_sggPertPlane_fam Ξ Q hΞ hQ)

/-- **The slice of the unshifted chain family at a fixed box point**: `t ↦ clampedSweep c (1 - ·)
(Ξ t ∘ diskPlane Q) x` is `C^∞`.  This is the `hsm` hypothesis of the charted brick
`Work.Drive.surjective_fderiv_chart_clampedSweep_ne_zero`. -/
theorem contMDiff_sggSweepSlice {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (x : EuclideanSpace ℝ (Fin 3)) :
    ContMDiff (𝓡 m) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : EuclideanSpace ℝ (Fin m) =>
        clampedSweep c (fun s => 1 - s) (fun y => Ξ t (diskPlane Q y)) x) := by
  have hs : ContMDiff (𝓡 m) (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : EuclideanSpace ℝ (Fin m) => (t, x)) :=
    contMDiff_iff_contDiff.mpr (by fun_prop)
  exact (contMDiff_sggSweepFam_zero Ξ Q c hΞ hQ).comp hs

/-- **Joint smoothness of the (shifted) chain family of the mirror.** -/
theorem contMDiff_sggSweepFam {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (s0 : EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3))) (𝓡 4)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) =>
        clampedSweep c (fun s => 1 - s) (diskPlane (pertChart Ξ Q (s0 + q.1))) q.2) := by
  have hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => 1 - s) := by fun_prop
  exact contMDiff_clampedSweep_family (P := EuclideanSpace ℝ (Fin m)) c
    (fun s : ℝ => 1 - s) hψ (fun t y => Ξ (s0 + t) (diskPlane Q y))
    (contMDiff_sggPertPlane_fam_shift Ξ Q hΞ hQ s0)

/-! ## 3. The level of the floored sweep, and the chain-side `hsurj` brick -/

/-- **A clamped sweep whose radial parameter vanishes lies in the level `c`.** -/
lemma levelOf_sggSweep_face_zero (c : ℝ) (hc : 0 < c)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (x : EuclideanSpace ℝ (Fin 3))
    (hx : x 2 = 0) :
    levelOf (clampedSweep c (fun s => 1 - s) P x) = c := by
  rw [clampedSweep_face_zero c hc (fun s => 1 - s) P (by norm_num) x hx, levelOf_shadow]

/-- **The chain-side `hsurj` brick of the mirror**: the parameter-derivative of the charted chain
family is onto, as soon as the radial parameter of the sweep is nonzero.

The family is the composite of the shift `t' ↦ s₀ + t'` (whose derivative is the identity) with the
unshifted family, whose surjectivity is
`Work.Drive.surjective_fderiv_chart_clampedSweep_ne_zero` (`sweepTripleGeneric.lean`). -/
theorem hsurj_sggSweepFam {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (hc : 0 < c) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (s0 : EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin 3)) (hx : x 2 ≠ 0)
    (t : EuclideanSpace ℝ (Fin m)) (p : CappingSpace)
    (hsrc : clampedSweep c (fun s => 1 - s) (fun y => Ξ (s0 + t) (diskPlane Q y)) x
      ∈ (chr p).source) :
    Function.Surjective
      (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
        chr p (clampedSweep c (fun s => 1 - s)
          (fun y => Ξ (s0 + t') (diskPlane Q y)) x)) t) := by
  have hsm : ContMDiff (𝓡 m) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : EuclideanSpace ℝ (Fin m) =>
        clampedSweep c (fun s => 1 - s) (fun y => Ξ u (diskPlane Q y)) x) :=
    contMDiff_sggSweepSlice Ξ Q c hΞ hQ x
  have hinner := surjective_fderiv_chart_clampedSweep_ne_zero (P := diskPlane Q) hΞ c hc x hx
    (s0 + t) p hsrc hsm
  have hfun : (fun t' : EuclideanSpace ℝ (Fin m) =>
        chr p (clampedSweep c (fun s => 1 - s) (fun y => Ξ (s0 + t') (diskPlane Q y)) x))
      = (fun u : EuclideanSpace ℝ (Fin m) =>
          chr p (clampedSweep c (fun s => 1 - s) (fun y => Ξ u (diskPlane Q y)) x))
        ∘ (fun t' : EuclideanSpace ℝ (Fin m) => s0 + t') := rfl
  rw [hfun]
  have hG : HasFDerivAt
      (fun u : EuclideanSpace ℝ (Fin m) =>
        chr p (clampedSweep c (fun s => 1 - s) (fun y => Ξ u (diskPlane Q y)) x))
      (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin m) =>
        chr p (clampedSweep c (fun s => 1 - s) (fun y => Ξ u (diskPlane Q y)) x)) (s0 + t))
      (s0 + t) := by
    have h1 : ContMDiffAt (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (chr p)
        (clampedSweep c (fun s => 1 - s) (fun y => Ξ (s0 + t) (diskPlane Q y)) x) :=
      (contMDiffOn_chr p).contMDiffAt ((chr p).open_source.mem_nhds hsrc)
    have h2 : ContMDiffAt (𝓡 m) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : EuclideanSpace ℝ (Fin m) =>
          clampedSweep c (fun s => 1 - s) (fun y => Ξ u (diskPlane Q y)) x) (s0 + t) :=
      hsm.contMDiffAt
    have h3 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : EuclideanSpace ℝ (Fin m) =>
          chr p (clampedSweep c (fun s => 1 - s) (fun y => Ξ u (diskPlane Q y)) x)) (s0 + t) :=
      contMDiffAt_iff_contDiffAt.mp (h1.comp (s0 + t) h2)
    exact (h3.differentiableAt sgg_top_ne_zero).hasFDerivAt
  have hA : HasFDerivAt (fun t' : EuclideanSpace ℝ (Fin m) => s0 + t')
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m))) t :=
    (hasFDerivAt_id t).const_add s0
  have hcomp := hG.comp t hA
  rw [hcomp.fderiv]
  intro w
  obtain ⟨v, hv⟩ := hinner w
  exact ⟨v, by simpa using hv⟩

/-! ## 4. The cut-off-scaled charted difference system of the mirror

The loop is fixed, the chain carries the parameter: the system is
`q ↦ χ q • chartDiff p Loop (Sweep q.1) q.2`, and its smoothness is the mirror of
`Work.Drive.contDiff_sgCutoff_chartDiff` (with the two sides exchanged). -/

/-- A point outside the topological support of `f` has a neighbourhood on which `f` vanishes. -/
private lemma sgg_eventually_eq_zero_of_notMem_tsupport {X Y : Type*} [TopologicalSpace X] [Zero Y]
    {f : X → Y} {x : X} (h : x ∉ tsupport f) : ∀ᶠ y in 𝓝 x, f y = 0 := by
  have hopen : IsOpen (tsupport f)ᶜ := (isClosed_tsupport f).isOpen_compl
  refine Filter.mem_of_superset (hopen.mem_nhds (by simpa using h)) ?_
  intro y hy
  by_contra hne
  exact hy (subset_tsupport f hne)

/-- **Global smoothness of the cut-off-scaled charted difference system of the mirror.** -/
theorem contDiff_cutoff_chartDiff_chain {m : ℕ}
    (L : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hL : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) L)
    (Sweep : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (hSweep : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => Sweep q.1 q.2))
    (p : CappingSpace) {χ : EuclideanSpace ℝ (Fin m) × Amb 4 → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    {U : Set (EuclideanSpace ℝ (Fin m) × Amb 4)}
    (hU : U ⊆ {q : EuclideanSpace ℝ (Fin m) × Amb 4 |
      L (sqPart q.2) ∈ (chr p).source ∧ Sweep q.1 (cbPart q.2) ∈ (chr p).source})
    (hχsupp : tsupport χ ⊆ U) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => χ q • chartDiff p L (Sweep q.1) q.2) := by
  rw [contDiff_iff_contDiffAt]
  intro q₀
  by_cases h0 : q₀ ∈ tsupport χ
  · have hreg := hU (hχsupp h0)
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => chartDiff p L (Sweep q.1) q.2) q₀ :=
      contDiffAt_chartDiff_family_fin m L hL Sweep hSweep p q₀.1 hreg
    exact hχ.contDiffAt.smul h1
  · refine (contDiffAt_const (c := (0 : Tgt 4))).congr_of_eventuallyEq ?_
    filter_upwards [sgg_eventually_eq_zero_of_notMem_tsupport h0] with q hq
    rw [hq, zero_smul]

/-! ## 5. The main theorem -/

theorem sgGoodChain_of_small_shift_sweep {m : Nat} (hm : 4 ≤ m) (L : ℝ → Work.Drive.CappingSpace) (hL : Work.Drive.IsSmoothLoop L) (Xi : EuclideanSpace ℝ (Fin m) → Work.Drive.CappingSpace → Work.Drive.CappingSpace) (Q : ℂ → Work.Drive.CappingSpace) (c : ℝ) (hc : 0 < c) (hXi : Work.Drive.ChartPert Q m Xi) (hQ : Work.Drive.IsSmoothChart Q) (hlev : ∀ t ∈ Set.Icc (0 : ℝ) 1, c < Work.Drive.levelOf (L t)) (s0 : EuclideanSpace ℝ (Fin m)) (e0 : ℝ) (he0 : 0 < e0) : ∃ p : EuclideanSpace ℝ (Fin m), ‖p‖ < e0 ∧ Work.Drive.GoodLoopChain L (Work.Drive.clampedSweep c (fun t : ℝ => 1 - t) (Work.Drive.diskPlane (Work.Drive.pertChart Xi Q (s0 + p)))) := by
  classical
  -- ## 0. the two sides
  set Loop : EuclideanSpace ℝ (Fin 2) → CappingSpace := fun u => L (u 0) with hLoopdef
  set Sweep : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 3) → CappingSpace :=
    fun t x => clampedSweep c (fun s => 1 - s) (diskPlane (pertChart Xi Q (s0 + t))) x
    with hSweepdef
  have hLoopsm : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) Loop :=
    contMDiff_sggLoopFam hL
  have hLsm : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) L := hL
  have hSweepsm : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => Sweep q.1 q.2) :=
    contMDiff_sggSweepFam Xi Q c hXi hQ s0
  have hcontLoop : Continuous (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => Loop (sqPart q.2)) := by
    have h1 : (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => Loop (sqPart q.2))
        = fun q => L (q.2 0) := by
      funext q
      rw [hLoopdef]
      simp only
      rw [sgg_sqPart_zero]
    rw [h1]
    exact hLsm.continuous.comp
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 5 => ℝ) 0).continuous.comp continuous_snd)
  have hcontSweep : Continuous (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => Sweep q.1 (cbPart q.2)) :=
    hSweepsm.continuous.comp (continuous_fst.prodMk (continuous_cbPart.comp continuous_snd))
  -- ## 1. the loop image and its chart cover
  set Simg : Set CappingSpace := L '' Set.Icc (0 : ℝ) 1 with hSimgdef
  have hSimg_compact : IsCompact Simg := isCompact_Icc.image hLsm.continuous
  obtain ⟨r, pch, C0, C1, hC0c, hC1c, hC0int, hC1sub, hcover⟩ :=
    exists_compact_chart_cover Simg hSimg_compact
  have hSimg_ne : Simg.Nonempty := ⟨L 0, ⟨0, by norm_num, rfl⟩⟩
  -- ## 2. the per-piece sets, the chart regions and their thickening
  set Sset : Fin r → Set (EuclideanSpace ℝ (Fin m) × Amb 4) := fun i => {q |
    ‖q.1‖ ≤ 1 ∧ q.2 ∈ Submission.Drive.unitBox 4 ∧
      Loop (sqPart q.2) ∈ C0 i ∧ Sweep q.1 (cbPart q.2) ∈ C1 i} with hSsetdef
  have hSset_compact : ∀ i, IsCompact (Sset i) := by
    intro i
    have hEq : Sset i = ((Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 ×ˢ
          Submission.Drive.unitBox 4)
        ∩ ((fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => Loop (sqPart q.2)) ⁻¹' (C0 i)))
        ∩ ((fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => Sweep q.1 (cbPart q.2)) ⁻¹' (C1 i)) := by
      ext q
      simp only [hSsetdef, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_preimage,
        Metric.mem_closedBall, dist_zero_right]
      tauto
    refine IsCompact.of_isClosed_subset
      ((isCompact_closedBall 0 1).prod (isCompact_unitBox 4)) ?_ ?_
    · rw [hEq]
      refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
      · exact Metric.isClosed_closedBall.prod (isClosed_unitBox 4)
      · exact (hC0c i).isClosed.preimage hcontLoop
      · exact (hC1c i).isClosed.preimage hcontSweep
    · intro q hq
      rw [hEq] at hq
      exact hq.1.1
  set U : Fin r → Set (EuclideanSpace ℝ (Fin m) × Amb 4) := fun i => {q |
    Loop (sqPart q.2) ∈ (chr (pch i)).source ∧ Sweep q.1 (cbPart q.2) ∈ (chr (pch i)).source}
    with hUdef
  have hUopen : ∀ i, IsOpen (U i) := by
    intro i
    have hEq : U i = ((fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => Loop (sqPart q.2)) ⁻¹'
          ((chr (pch i)).source))
        ∩ ((fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => Sweep q.1 (cbPart q.2)) ⁻¹'
          ((chr (pch i)).source)) := by
      ext q; simp only [hUdef, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
    rw [hEq]
    exact ((chr (pch i)).open_source.preimage hcontLoop).inter
      ((chr (pch i)).open_source.preimage hcontSweep)
  have hSsetU : ∀ i, Sset i ⊆ U i := by
    intro i q hq
    have hq' : q.2 ∈ Submission.Drive.unitBox 4 ∧
        Loop (sqPart q.2) ∈ C0 i ∧ Sweep q.1 (cbPart q.2) ∈ C1 i := by
      have h := hq
      rw [hSsetdef] at h
      exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
    exact ⟨hC1sub i (interior_subset (hC0int i hq'.2.1)), hC1sub i hq'.2.2⟩
  have hthick : ∀ i, ∃ δ : ℝ, 0 < δ ∧
      ∀ (q q' : EuclideanSpace ℝ (Fin m)) (z : Amb 4),
        (q, z) ∈ Sset i → ‖q' - q‖ ≤ δ → (q', z) ∈ U i := fun i =>
    exists_pos_norm_subset_of_isCompact_subset_isOpen (hSset_compact i) (hUopen i) (hSsetU i)
  choose δ hδpos hδ using hthick
  -- ## 3. the radii
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (i : Fin r)
      (q q' : EuclideanSpace ℝ (Fin m)) (z : Amb 4),
      (q, z) ∈ Sset i → ‖q' - q‖ ≤ δ₀ → (q', z) ∈ U i :=
    exists_pos_forall_fin
      (P := fun i (d : ℝ) => ∀ (q q' : EuclideanSpace ℝ (Fin m)) (z : Amb 4),
        (q, z) ∈ Sset i → ‖q' - q‖ ≤ d → (q', z) ∈ U i)
      (fun i ε ε' hle h q q' z hq hqq => h q q' z hq (le_trans hqq hle))
      (fun i => ⟨δ i, hδpos i, hδ i⟩)
  set ε : ℝ := min (min (e0 / 2) (δ₀ / 2)) (1 / 2) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact lt_min (lt_min (by linarith) (by linarith)) (by norm_num)
  have hεe0 : ε ≤ e0 / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hε1 : ε ≤ 1 / 2 := min_le_right _ _
  have hεδ : ∀ _i : Fin r, 2 * ε ≤ δ₀ := fun _i => by
    have h1 : ε ≤ δ₀ / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  -- ## 4. the compact Sard sets, the cut-offs and the systems
  set K : Fin r → Set (Amb 4) := fun i => {z | ∃ q : EuclideanSpace ℝ (Fin m),
    ‖q‖ ≤ ε ∧ (q, z) ∈ Sset i} with hKdef
  have hKcomp : ∀ i, IsCompact (K i) := by
    intro i
    have hEq : K i = Prod.snd '' (Sset i ∩
        {q : EuclideanSpace ℝ (Fin m) × Amb 4 | ‖q.1‖ ≤ ε}) := by
      ext z
      constructor
      · rintro ⟨q, hq, hqz⟩
        exact ⟨(q, z), ⟨hqz, hq⟩, rfl⟩
      · rintro ⟨q, hq, rfl⟩
        exact ⟨q.1, by simpa using hq.2, hq.1⟩
    rw [hEq]
    exact ((hSset_compact i).inter_right
      (isClosed_le (continuous_norm.comp continuous_fst) continuous_const)).image continuous_snd
  have hKsub : ∀ i, Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) ε ×ˢ K i ⊆ U i := by
    intro i
    rintro ⟨q, z⟩ ⟨hq, hz⟩
    obtain ⟨q₀, hq₀, hq₀S⟩ := hz
    have hqq : ‖q - q₀‖ ≤ δ₀ := by
      have hqε : ‖q‖ ≤ ε := by simpa [Metric.mem_closedBall, dist_zero_right] using hq
      have h1 : ‖q - q₀‖ ≤ ‖q‖ + ‖q₀‖ := norm_sub_le q q₀
      linarith [hεδ i]
    exact hδ₀ i q₀ q z hq₀S hqq
  have hcut : ∀ i, ∃ χ : EuclideanSpace ℝ (Fin m) × Amb 4 → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧
      (∀ q ∈ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) ε) ×ˢ K i, χ q = 1) ∧
      tsupport χ ⊆ U i := fun i =>
    gpn_exists_cutoff_one_on_of_subset ((isCompact_closedBall 0 ε).prod (hKcomp i))
      (hUopen i) (hKsub i)
  choose χ hχsm hχone hχsupp using hcut
  set Kzero : (i : Fin r) → (Fin 4 × Fin 2) → Set (EuclideanSpace ℝ (Fin 3)) := fun i j =>
    Submission.Drive.unitBox 2 ∩ (sgFace j.1 j.2 ⁻¹' K i) with hKzerodef
  have hKzero_compact : ∀ (i : Fin r) (j : Fin 4 × Fin 2), IsCompact (Kzero i j) := by
    intro i j
    exact (isCompact_unitBox 2).inter_right
      ((hKcomp i).isClosed.preimage (continuous_sgFace j.1 j.2))
  set Phi : Fin r → EuclideanSpace ℝ (Fin m) × Amb 4 → Tgt 4 := fun i q =>
    χ i q • chartDiff (pch i) Loop (Sweep q.1) q.2 with hPhidef
  have hΦsm : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Phi i) := fun i =>
    contDiff_cutoff_chartDiff_chain Loop hLoopsm (fun t x => Sweep t x) hSweepsm (pch i)
      (hχsm i) (U := U i) (by
        intro q hq
        rw [hUdef] at hq
        exact hq) (hχsupp i)
  -- ## 5. the parameter-derivative of the system at its zeros
  have hsurjPhi : ∀ (i : Fin r) (q : EuclideanSpace ℝ (Fin m)) (z : Amb 4), ‖q‖ < ε →
      (z ∈ K i ∨ ∃ j : Fin 4 × Fin 2, z ∈ sgFace j.1 j.2 '' Kzero i j) → Phi i (q, z) = 0 →
      Function.Surjective (fderiv ℝ (fun q' : EuclideanSpace ℝ (Fin m) => Phi i (q', z)) q) := by
    intro i q z hq hz h0
    have hzK : z ∈ K i := hz.elim id fun h => by
      obtain ⟨j, y, hy, rfl⟩ := h
      exact hy.2
    have hχ1 : χ i (q, z) = 1 := hχone i (q, z)
      ⟨by rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt hq, hzK⟩
    have hreg : (q, z) ∈ U i := hKsub i (show (q, z) ∈
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) ε ×ˢ K i from
      ⟨by rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt hq, hzK⟩)
    rw [hUdef] at hreg
    have hcd0 : chartDiff (pch i) Loop (Sweep q) z = 0 := by
      have h := h0
      rw [hPhidef] at h
      simp only at h
      rw [hχ1, one_smul] at h
      exact h
    have heq : Loop (sqPart z) = Sweep q (cbPart z) := (chartDiff_eq_zero_iff hreg).mp hcd0
    -- the radial parameter is nonzero, by the level band
    have hx2 : (cbPart z) 2 ≠ 0 := by
      intro hz2
      have hlvl : levelOf (Sweep q (cbPart z)) = c := by
        rw [hSweepdef]
        exact levelOf_sggSweep_face_zero c hc _ (cbPart z) hz2
      have hgt : c < levelOf (Sweep q (cbPart z)) := by
        rw [← heq]
        have hzbox : z ∈ Submission.Drive.unitBox 4 := by
          obtain ⟨q', -, hq'z⟩ := hzK
          rw [hSsetdef] at hq'z
          exact hq'z.2.1
        refine hlev ((sqPart z) 0) ⟨?_, ?_⟩
        · rw [sqPart_apply]; exact (hzbox (sqIdx 0)).1
        · rw [sqPart_apply]; exact (hzbox (sqIdx 0)).2
      linarith
    -- the charted parameter-derivative of the chain is onto
    have hchain := hsurj_sggSweepFam Xi Q c hc hXi hQ s0 (cbPart z) hx2 q (pch i) hreg.2
    -- the cut-off does not change the derivative at the zero
    have hχat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q' : EuclideanSpace ℝ (Fin m) =>
        χ i (q', z)) q :=
      (hχsm i).contDiffAt.comp q (contDiffAt_id.prodMk contDiffAt_const)
    have hcdat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q' : EuclideanSpace ℝ (Fin m) => chartDiff (pch i) Loop (Sweep q') z) q := by
      have hjoint : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun qq : EuclideanSpace ℝ (Fin m) × Amb 4 =>
            chartDiff (pch i) Loop (Sweep qq.1) qq.2) (q, z) :=
        contDiffAt_chartDiff_family_fin m Loop hLoopsm (fun t x => Sweep t x) hSweepsm
          (pch i) q hreg
      have hcomp : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          ((fun qq : EuclideanSpace ℝ (Fin m) × Amb 4 =>
            chartDiff (pch i) Loop (Sweep qq.1) qq.2) ∘
            (fun q' : EuclideanSpace ℝ (Fin m) => (q', z))) q :=
        hjoint.comp q (contDiffAt_id.prodMk contDiffAt_const)
      exact hcomp
    have hχfd : HasFDerivAt (fun q' : EuclideanSpace ℝ (Fin m) => χ i (q', z))
        (fderiv ℝ (fun q' : EuclideanSpace ℝ (Fin m) => χ i (q', z)) q) q :=
      (hχat.differentiableAt sgg_top_ne_zero).hasFDerivAt
    have hcdfd : HasFDerivAt
        (fun q' : EuclideanSpace ℝ (Fin m) => chartDiff (pch i) Loop (Sweep q') z)
        (fderiv ℝ (fun q' : EuclideanSpace ℝ (Fin m) =>
          chartDiff (pch i) Loop (Sweep q') z) q) q :=
      (hcdat.differentiableAt sgg_top_ne_zero).hasFDerivAt
    have hsmul := hχfd.smul hcdfd
    have h1 : (χ i (q, z)) • (fderiv ℝ (fun q' : EuclideanSpace ℝ (Fin m) =>
          chartDiff (pch i) Loop (Sweep q') z) q)
        + (fderiv ℝ (fun q' : EuclideanSpace ℝ (Fin m) => χ i (q', z)) q).smulRight
            (chartDiff (pch i) Loop (Sweep q) z)
        = fderiv ℝ (fun q' : EuclideanSpace ℝ (Fin m) =>
            chartDiff (pch i) Loop (Sweep q') z) q := by
      rw [hχ1, one_smul, hcd0]
      simp
    rw [h1] at hsmul
    have hfd : fderiv ℝ (fun q' : EuclideanSpace ℝ (Fin m) =>
          χ i (q', z) • chartDiff (pch i) Loop (Sweep q') z) q
        = fderiv ℝ (fun q' : EuclideanSpace ℝ (Fin m) =>
            chartDiff (pch i) Loop (Sweep q') z) q := hsmul.fderiv
    have hgoal : (fun q' : EuclideanSpace ℝ (Fin m) => Phi i (q', z))
        = fun q' : EuclideanSpace ℝ (Fin m) =>
            χ i (q', z) • chartDiff (pch i) Loop (Sweep q') z := rfl
    rw [hgoal, hfd]
    have h1 : (fun q' : EuclideanSpace ℝ (Fin m) => chartDiff (pch i) Loop (Sweep q') z)
        = (fun q' : EuclideanSpace ℝ (Fin m) => chr (pch i) (Loop (sqPart z)) -
            chr (pch i) (clampedSweep c (fun s => 1 - s)
              (fun y => Xi (s0 + q') (diskPlane Q y)) (cbPart z))) := by
      funext q'
      rw [hSweepdef]
      rfl
    rw [h1, fderiv_const_sub]
    intro w
    obtain ⟨v, hv⟩ := hchain (-w)
    exact ⟨v, by rw [neg_apply, hv, neg_neg]⟩
  -- ## 6. the parametric Sard
  have hfin3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) < 4 := by
    rw [finrank_euclideanSpace]
    norm_num
  obtain ⟨pst, hpst, hregK, havoid⟩ :=
    exists_forall_good_and_notMem_family_multi (m := m) (n := 4) (r := r)
      (K := K) (hK := hKcomp)
      (ι := fun _ => Fin 4 × Fin 2) (X := fun _ _ => EuclideanSpace ℝ (Fin 3))
      (hX := fun _ _ => hfin3)
      (B := fun _ j => sgFace j.1 j.2) (hB := fun _ j => contDiff_sgFace j.1 j.2)
      (K₀ := Kzero) (hK₀ := hKzero_compact) (Φ := Phi) (hΦ := hΦsm)
      (ε := ε) (hε := hεpos) (hsurj := hsurjPhi)
  have hpst_le : ‖pst‖ ≤ ε := le_of_lt hpst
  have hpst_le1 : ‖pst‖ ≤ 1 := by linarith [hε1]
  -- ## 7. the conversions at the parameter `pst`
  have hSweepsmPst : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (Sweep pst) := by
    have hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => 1 - s) := by fun_prop
    have hpt : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (pertChart Xi Q (s0 + pst)) :=
      contMDiff_pertChart Xi Q hXi hQ (s0 + pst)
    exact contMDiff_clampedSweep c (fun s => 1 - s) (diskPlane (pertChart Xi Q (s0 + pst)))
      hψ (contMDiff_diskPlane hpt)
  -- ### 7a. the data of a meet
  have hmeetdata : ∀ q ∈ meetBox L (Sweep pst), ∃ i : Fin r,
      Loop (sqPart (meetPt q)) ∈ C0 i ∧ meetPt q ∈ K i ∧
      (Loop (sqPart (meetPt q)) ∈ (chr (pch i)).source ∧
        Sweep pst (cbPart (meetPt q)) ∈ (chr (pch i)).source) ∧
      (Loop (sqPart (meetPt q)) = Sweep pst (cbPart (meetPt q))) ∧
      Phi i (pst, meetPt q) = 0 := by
    rintro q ⟨hq1, hq2, hmeet⟩
    have hv : L q.1 ∈ Simg := ⟨q.1, hq1, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hv)
    have hbox : meetPt q ∈ Submission.Drive.unitBox 4 := meetPt_mem_unitBox_of hq1 hq2
    have hloop : Loop (sqPart (meetPt q)) = L q.1 := by
      rw [hLoopdef]
      simp only [PiLp.proj_apply, sqPart_meetPt]
      rfl
    have hchain : Sweep pst (cbPart (meetPt q)) = Sweep pst q.2 := by rw [cbPart_meetPt]
    have hzS : (pst, meetPt q) ∈ Sset i := by
      refine ⟨hpst_le1, hbox, ?_, ?_⟩
      · rw [hloop]; exact hi
      · rw [hchain, ← hmeet]; exact interior_subset (hC0int i hi)
    have hzK : meetPt q ∈ K i := ⟨pst, hpst_le, hzS⟩
    have hzU : (pst, meetPt q) ∈ U i := hKsub i
      ⟨by rw [Metric.mem_closedBall, dist_zero_right]; exact hpst_le, hzK⟩
    rw [hUdef] at hzU
    have heq : Loop (sqPart (meetPt q)) = Sweep pst (cbPart (meetPt q)) := by
      rw [hchain, hloop]
      exact hmeet
    have hPhi0 : Phi i (pst, meetPt q) = 0 := by
      have hχ1 : χ i (pst, meetPt q) = 1 := hχone i (pst, meetPt q)
        ⟨by rw [Metric.mem_closedBall, dist_zero_right]; exact hpst_le, hzK⟩
      change χ i (pst, meetPt q) • chartDiff (pch i) Loop (Sweep pst) (meetPt q) = 0
      rw [hχ1, one_smul]
      exact (chartDiff_eq_zero_iff hzU).mpr heq
    exact ⟨i, hi, hzK, hzU, heq, hPhi0⟩
  -- ### 7b. the transversality
  have hTrans : ∀ q : ℝ × EuclideanSpace ℝ (Fin 3),
      q.1 ∈ Set.Icc (0 : ℝ) 1 → q.2 ∈ Submission.Drive.unitBox 2 →
      L q.1 = Sweep pst q.2 →
      LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) L q.1).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) (Sweep pst) q.2).toLinearMap = ⊤ := by
    intro q hq1 hq2 hmeet
    obtain ⟨i, hiC0, hzK, hzU, heq, hPhi0⟩ :=
      hmeetdata q ⟨hq1, hq2, hmeet⟩
    have hzderiv : Function.Surjective (fderiv ℝ (fun z' : Amb 4 =>
        chartDiff (pch i) Loop (Sweep pst) z') (meetPt q)) := by
      have hS := hregK i (meetPt q) hzK hPhi0
      have hχ1 : χ i (pst, meetPt q) = 1 := hχone i (pst, meetPt q)
        ⟨by rw [Metric.mem_closedBall, dist_zero_right]; exact hpst_le, hzK⟩
      have hcdat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z' : Amb 4 => chartDiff (pch i) Loop (Sweep pst) z') (meetPt q) := by
        have hjoint : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun zz : EuclideanSpace ℝ (Fin m) × Amb 4 =>
              chartDiff (pch i) Loop (Sweep zz.1) zz.2) (pst, meetPt q) :=
          contDiffAt_chartDiff_family_fin m Loop hLoopsm (fun t x => Sweep t x) hSweepsm
            (pch i) pst hzU
        have hcomp : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            ((fun zz : EuclideanSpace ℝ (Fin m) × Amb 4 =>
              chartDiff (pch i) Loop (Sweep zz.1) zz.2) ∘
              (fun z' : Amb 4 => (pst, z'))) (meetPt q) :=
          hjoint.comp (meetPt q) (contDiffAt_const.prodMk contDiffAt_id)
        exact hcomp
      have hcd0 : chartDiff (pch i) Loop (Sweep pst) (meetPt q) = 0 :=
        (chartDiff_eq_zero_iff hzU).mpr heq
      have hcdp : HasFDerivAt (fun z' : Amb 4 => chartDiff (pch i) Loop (Sweep pst) z')
          (fderiv ℝ (fun z' : Amb 4 =>
            chartDiff (pch i) Loop (Sweep pst) z') (meetPt q)) (meetPt q) :=
        (hcdat.differentiableAt sgg_top_ne_zero).hasFDerivAt
      have hχat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z' : Amb 4 => χ i (pst, z')) (meetPt q) := by
        have hpair : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun z' : Amb 4 => (pst, z')) (meetPt q) :=
          contDiffAt_const.prodMk contDiffAt_id
        exact (hχsm i).contDiffAt.comp (meetPt q) hpair
      have hbp : HasFDerivAt (fun z' : Amb 4 => χ i (pst, z'))
          (fderiv ℝ (fun z' : Amb 4 => χ i (pst, z')) (meetPt q)) (meetPt q) :=
        (hχat.differentiableAt sgg_top_ne_zero).hasFDerivAt
      have hsmul := hbp.smul hcdp
      have h1 : (χ i (pst, meetPt q)) • (fderiv ℝ (fun z' : Amb 4 =>
            chartDiff (pch i) Loop (Sweep pst) z') (meetPt q))
          + (fderiv ℝ (fun z' : Amb 4 => χ i (pst, z')) (meetPt q)).smulRight
              (chartDiff (pch i) Loop (Sweep pst) (meetPt q))
          = fderiv ℝ (fun z' : Amb 4 =>
              chartDiff (pch i) Loop (Sweep pst) z') (meetPt q) := by
        rw [hχ1, one_smul, hcd0]
        simp
      rw [h1] at hsmul
      have hfd : fderiv ℝ (fun z' : Amb 4 =>
            χ i (pst, z') • chartDiff (pch i) Loop (Sweep pst) z') (meetPt q)
          = fderiv ℝ (fun z' : Amb 4 =>
              chartDiff (pch i) Loop (Sweep pst) z') (meetPt q) := hsmul.fderiv
      have hgoal : (fun z' : Amb 4 => Phi i (pst, z'))
          = fun z' : Amb 4 => χ i (pst, z') • chartDiff (pch i) Loop (Sweep pst) z' := rfl
      rw [hgoal, hfd] at hS
      exact hS
    have hbridge := range_sup_eq_top_of_chartDiff_surjective (pch i) Loop (Sweep pst)
      hLoopsm hSweepsmPst hzU heq hzderiv
    have hconv : LinearMap.range (mfderiv (𝓡 2) (𝓡 4) Loop (sqPart (meetPt q))).toLinearMap
        = LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) L q.1).toLinearMap := by
      have h := range_mfderiv_comp_surjective_linear L hLsm
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0)
        (fun a => ⟨mk2 a 0, by simp [mk2, PiLp.proj_apply]⟩) (sqPart (meetPt q))
      have h3 : (fun x : EuclideanSpace ℝ (Fin 2) =>
            L ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0) x)) = Loop := by
        funext x
        rw [hLoopdef]
        rfl
      rw [h3] at h
      have h2 : (sqPart (meetPt q)) 0 = q.1 := by rw [sqPart_meetPt]; rfl
      rw [PiLp.proj_apply, h2] at h
      exact h
    rw [hconv, cbPart_meetPt] at hbridge
    exact hbridge
  -- ### 7c. the finiteness
  have hFin : (meetBox L (Sweep pst)).Finite := by
    let L1 : EuclideanSpace ℝ (Fin 1) → CappingSpace :=
      fun x => L ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0) x)
    have hL1sm : ContMDiff (𝓡 1) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) L1 :=
      hLsm.comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0).contMDiff
    have htrans : ∀ (u : EuclideanSpace ℝ (Fin 1)) (x : EuclideanSpace ℝ (Fin 3)),
        u ∈ Submission.Drive.unitBox 0 → x ∈ Submission.Drive.unitBox 2 → L1 u = Sweep pst x →
        LinearMap.range (mfderiv (𝓡 1) (𝓡 4) L1 u).toLinearMap ⊔
          LinearMap.range (mfderiv (𝓡 3) (𝓡 4) (Sweep pst) x).toLinearMap = ⊤ := by
      intro u x hu hx heq
      have huI : (u 0) ∈ Set.Icc (0 : ℝ) 1 := by simpa [Submission.Drive.unitBox] using hu
      have h := hTrans (u 0, x) huI hx (by
        have h1 : L1 u = L (u 0) := rfl
        rw [h1] at heq
        exact heq)
      have hconv : LinearMap.range (mfderiv (𝓡 1) (𝓡 4) L1 u).toLinearMap
          = LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) L (u 0)).toLinearMap := by
        have hh := range_mfderiv_comp_surjective_linear L hLsm
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0)
          (fun a => ⟨sggMk1 a, by simp [sggMk1, PiLp.proj_apply]⟩) u
        have h2 : (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0) u = u 0 := rfl
        rw [h2] at hh
        exact hh
      rw [hconv]
      exact h
    have hfin1 := finite_loopChainMeet_of_transverse L1 (Sweep pst) hL1sm hSweepsmPst htrans
    have himg : (fun p : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3) =>
        (p.1 0, p.2)) '' {p | p.1 ∈ Submission.Drive.unitBox 0 ∧
          p.2 ∈ Submission.Drive.unitBox 2 ∧ L1 p.1 = Sweep pst p.2}
        = meetBox L (Sweep pst) := by
      ext q
      constructor
      · rintro ⟨p, ⟨hp1, hp2, hpm⟩, rfl⟩
        exact ⟨by simpa [Submission.Drive.unitBox] using hp1, hp2, by
          have h1 : L1 p.1 = L (p.1 0) := rfl
          rw [h1] at hpm
          exact hpm⟩
      · rintro ⟨hq1, hq2, hqm⟩
        refine ⟨(sggMk1 q.1, q.2), ⟨?_, hq2, ?_⟩, ?_⟩
        · have hp1 : (sggMk1 q.1 : EuclideanSpace ℝ (Fin 1)) ∈ Submission.Drive.unitBox 0 := by
            simpa [Submission.Drive.unitBox, sggMk1] using hq1
          exact hp1
        · have h1 : L1 (sggMk1 q.1) = L q.1 := rfl
          rw [h1]
          exact hqm
        · simp [sggMk1]
    rw [← himg]
    exact hfin1.image _
  -- ### 7d. the interiority
  have hInt : ∀ q ∈ meetBox L (Sweep pst),
      q.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ ∀ j : Fin 3, q.2 j ∈ Set.Ioo (0 : ℝ) 1 := by
    rintro q hq
    obtain ⟨hq1, hq2, hmeet⟩ := hq
    obtain ⟨i, hiC0, hzK, hzU, heq, hPhi0⟩ := hmeetdata q ⟨hq1, hq2, hmeet⟩
    have hzbox : ∀ k : Fin 5, k ≠ 1 → meetPt q k ∈ Set.Icc (0 : ℝ) 1 :=
      fun k _ => meetPt_mem_unitBox_of hq1 hq2 k
    have hcontra : ∀ (k : Fin 4) (t : Fin 2), (t : ℝ) = meetPt q (boxIdx k) → False := by
      intro k t ht
      have hybox : gatherCLM k (meetPt q) ∈ Submission.Drive.unitBox 2 :=
        gatherCLM_mem_unitBox hzbox
      have hface : sgFace k t (gatherCLM k (meetPt q)) ∈ K i := by
        rw [sgFace_gatherCLM k t (meetPt_apply_one q) ht]
        exact hzK
      have hyK : gatherCLM k (meetPt q) ∈ Kzero i (k, t) := ⟨hybox, hface⟩
      have hne := havoid i (k, t) (gatherCLM k (meetPt q)) hyK
      rw [sgFace_gatherCLM k t (meetPt_apply_one q) ht] at hne
      exact hne hPhi0
    refine ⟨?_, fun j => ?_⟩
    · refine ⟨?_, ?_⟩
      · by_contra h
        push_neg at h
        exact hcontra 0 ⟨0, by norm_num⟩ (by
          rw [boxIdx_zero, meetPt_apply_zero, le_antisymm h hq1.1]; norm_num)
      · by_contra h
        push_neg at h
        exact hcontra 0 ⟨1, by norm_num⟩ (by
          rw [boxIdx_zero, meetPt_apply_zero, le_antisymm hq1.2 h]; norm_num)
    · refine ⟨?_, ?_⟩
      · by_contra h
        push_neg at h
        exact hcontra (Fin.succ j) ⟨0, by norm_num⟩ (by
          rw [← cbIdx_eq_boxIdx j, meetPt_cbIdx, le_antisymm h (hq2 j).1]; norm_num)
      · by_contra h
        push_neg at h
        exact hcontra (Fin.succ j) ⟨1, by norm_num⟩ (by
          rw [← cbIdx_eq_boxIdx j, meetPt_cbIdx, le_antisymm (hq2 j).2 h]; norm_num)
  -- ## 8. the conclusion
  have hpste0 : ‖pst‖ < e0 := by
    have h1 : ε ≤ e0 / 2 := hεe0
    linarith
  have hTrans' : ∀ q ∈ meetBox L (Sweep pst),
      LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) L q.1).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) (Sweep pst) q.2).toLinearMap = ⊤ :=
    fun q hq => hTrans q hq.1 hq.2.1 hq.2.2
  have hgood : GoodLoopChain L (Sweep pst) := ⟨hFin, hInt, hTrans'⟩
  exact ⟨pst, hpste0, hgood⟩

end

end Work.Drive
