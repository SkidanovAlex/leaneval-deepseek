import Mathlib
import Submission.Work.Drive.sgSweepDefs
import Submission.Work.Drive.chartDiffRangeBridge
import Submission.Work.Drive.exists_forall_good_and_notMem_family_multi
import Submission.Work.Drive.sgPiecesDefs

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# The charted difference system of the germ route (loop family vs fixed chain)

`Submission/Work/Drive/sideGerm_good_exists.lean` asks for chart perturbations `Ξ` of a chart `Q` of the
capped plane at which the pair `(Ξ t.1 ∘ Q, rotCapping w ∘ Ξ t.2 ∘ Q)` is a `GoodPair`.  This module
builds the *charted difference system* to which the parametric-Sard bricks of the workspace are applied:

> `Ψ p z = β (p, z) • chartDiff (p i) (sgLoop Ξ Q p) (sgSweep0 Q c w) z`,   `z : Amb 4 = ℝ⁵`,

i.e. the blockwise difference of the charted loop family and the charted (fixed) sweep, times a smooth
cut-off `β`.  It contains

* `Work.Drive.contMDiff_sgSweep0` — the fixed chain `sgSweep0 Q c w : ℝ³ → CappingSpace` is `C^∞`;
* `Work.Drive.contMDiff_sgLoop_fam` — the loop family `(p, z) ↦ sgLoop Ξ Q p (sqPart z)` is `C^∞` on
  `ℝ^m × ℝ^5`;
* `Work.Drive.contDiffAt_sgChartDiff` — joint smoothness of the charted difference system at a point
  where both values lie in the chart's source;
* `Work.Drive.contDiff_sgCutoff_chartDiff` — global smoothness of the cut-off-scaled system, from
  `tsupport γ ×ˢ tsupport β` lying in the charted region;
* `Work.Drive.hsurj_sgCutoff` — the *parameter*-derivative of that system is onto at its zeros, which
  is the `hsurj` hypothesis of the Sard bricks; the content is `Work.Drive.hsurj_sgLoop` (the
  parameter derivative of the charted loop value is onto, `ChartPert`'s third conjunct).

Everything is stated for the concrete maps of `sgSweepDefs`; the only inputs on `Ξ, Q` are
`ChartPert Q m Ξ` and `IsSmoothChart Q`.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

variable {m : ℕ} (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
  (Q : ℂ → CappingSpace) (c : ℝ) (w : UnitAddCircle)

/-! ## Smoothness of the fixed chain -/

/-- **The fixed chain `sgSweep0 Q c w` is `C^∞`.**  It is the clamped sweep of the disk presentation of
the rotated chart, and both factors are smooth. -/
theorem contMDiff_sgSweep0 (hQ : IsSmoothChart Q) :
    ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (sgSweep0 Q c w) := by
  obtain ⟨t, ht⟩ := Quotient.mk''_surjective w
  have hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => 1 - s) := by fun_prop
  refine contMDiff_clampedSweep c (fun s : ℝ => 1 - s) _ hψ ?_
  refine contMDiff_diskPlane ?_
  intro z
  have h := Work.Drive.contMDiffAt_rotCapping_comp (I := 𝓘(ℝ, ℂ)) Q (fun _ : ℂ => t) z
    hQ.contMDiffAt contMDiffAt_const
  simpa [ht] using h

/-! ## Smoothness of the loop family on the parameter space -/

/-- The exponential parametrisation of the loop, read on the `5`-box. -/
private def sgLoopPt (q : EuclideanSpace ℝ (Fin 5)) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.ofRealCLM (q 0) * Complex.I)

private lemma contDiff_sgLoopPt :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 5) => sgLoopPt q) := by
  rw [show (fun q : EuclideanSpace ℝ (Fin 5) => sgLoopPt q)
      = fun q => Complex.exp ((Real.pi : ℂ) * Complex.ofRealCLM (q 0) * Complex.I) from rfl]
  fun_prop

/-- **The loop family is jointly `C^∞` on `ℝ^m × ℝ^5`**, where the square block of `ℝ^5` carries the
loop parameter and the remaining (dummy) coordinate is ignored. -/
theorem contMDiff_sgLoop_fam (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5))) (𝓡 4)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) =>
        sgLoop Ξ Q q.1 (sqPart q.2)) := by
  have hpt : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5))) (𝓘(ℝ, ℂ))
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) =>
        sgLoopPt q.2) :=
    contDiff_sgLoopPt.contMDiff.comp ((ContinuousLinearMap.snd ℝ
      (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin 5))).contMDiff
        (n := ((⊤ : ℕ∞) : WithTop ℕ∞)))
  have hQ5 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5))) (𝓡 4)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) => Q (sgLoopPt q.2)) :=
    hQ.comp hpt
  have hfst : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5))) (𝓡 m)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) => q.1) :=
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin 5))).contMDiff
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
  have hpair : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5)))
      ((𝓡 m).prod (𝓡 4)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) => (q.1, Q (sgLoopPt q.2))) :=
    hfst.prodMk hQ5
  have hmain := hΞ.2.1.comp hpair
  refine hmain.congr fun q => ?_
  simp only [sgLoop, coreLoop, Function.comp_def, sgLoopPt]
  rfl

/-- **The loop of a single parameter as a map of the square block is smooth.** -/
theorem contMDiff_sgLoop_fixed (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (p : EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (sgLoop Ξ Q p) := by
  have hQ2 : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : EuclideanSpace ℝ (Fin 2) => Q (sgAux.loopPt u)) :=
    hQ.comp sgAux.contMDiff_loopPt
  have hpair : ContMDiff (𝓡 2) ((𝓡 m).prod (𝓡 4)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : EuclideanSpace ℝ (Fin 2) => (p, Q (sgAux.loopPt u))) :=
    contMDiff_const.prodMk hQ2
  have hcomp := hΞ.2.1.comp hpair
  refine hcomp.congr fun u => ?_
  simp only [sgLoop, coreLoop, sgAux.loopPt, Function.comp_def]

/-! ## The charted difference system -/

/-- The chart `chr p` is `C^∞` on its source. -/
private lemma contMDiffOn_chr_sg (p : CappingSpace) :
    ContMDiffOn (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (chr p) (chr p).source := by
  have h := contMDiffOn_extChartAt (I := 𝓡 4) (x := p) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
  simpa [chr] using h

/-- A charted smooth map on the parameter space is jointly smooth where its value lies in the chart
source. -/
private lemma contDiffAt_chart_sgOf
    (f : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) → CappingSpace)
    (hf : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5))) (𝓡 4)
      ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (p : CappingSpace) (q₀ : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5))
    (hreg : f q₀ ∈ (chr p).source) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q => (chr p) (f q)) q₀ := by
  have h1 : ContMDiffAt (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (chr p) (f q₀) :=
    (contMDiffOn_chr_sg p).contMDiffAt ((chr p).open_source.mem_nhds hreg)
  exact contMDiffAt_iff_contDiffAt.mp (h1.comp q₀ hf.contMDiffAt)

/-- The block projection `(q : ℝ^m × ℝ^5) ↦ sqPart q.2`. -/
private def sgSqCLM (m : ℕ) :
    EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  sqPartCLM.comp (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin 5)))

private lemma sgSqCLM_apply (m : ℕ)
    (q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5)) : sgSqCLM m q = sqPart q.2 := by
  simp [sgSqCLM, sqPartCLM_eq_sqPart]

/-- The block projection `(q : ℝ^m × ℝ^5) ↦ cbPart q.2`. -/
private def sgCbCLM (m : ℕ) :
    EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  cbPartCLM.comp (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin 5)))

private lemma sgCbCLM_apply (m : ℕ)
    (q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5)) : sgCbCLM m q = cbPart q.2 := by
  simp [sgCbCLM, cbPartCLM_eq_cbPart]

/-- The loop family, as a map on the parameter space. -/
private lemma contMDiff_sgLoop_fam' (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5))) (𝓡 4)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) =>
        sgLoop Ξ Q q.1 (sqPart q.2)) :=
  contMDiff_sgLoop_fam Ξ Q hΞ hQ

/-- The fixed chain, as a map on the parameter space. -/
private lemma contMDiff_sgSweep_fam' (hQ : IsSmoothChart Q) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5))) (𝓡 4)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) =>
        sgSweep0 Q c w (cbPart q.2)) := by
  have h := (contMDiff_sgSweep0 Q c w hQ).comp
    ((sgCbCLM m).contMDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞)))
  simpa [Function.comp_def, sgCbCLM_apply] using h

/-- **Joint smoothness of the charted difference system of the loop family against the fixed chain**,
at a parameter point where both values lie in the chart's source. -/
theorem contDiffAt_sgChartDiff (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q) (p : CappingSpace)
    {q₀ : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5)}
    (hreg : sgLoop Ξ Q q₀.1 (sqPart q₀.2) ∈ (chr p).source ∧
      sgSweep0 Q c w (cbPart q₀.2) ∈ (chr p).source) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) =>
        chartDiff p (sgLoop Ξ Q q.1) (sgSweep0 Q c w) q.2) q₀ := by
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) =>
        (chr p) (sgLoop Ξ Q q.1 (sqPart q.2))) q₀ :=
    contDiffAt_chart_sgOf (m := m) (fun q => sgLoop Ξ Q q.1 (sqPart q.2))
      (contMDiff_sgLoop_fam Ξ Q hΞ hQ) p q₀ hreg.1
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) =>
        (chr p) (sgSweep0 Q c w (cbPart q.2))) q₀ :=
    contDiffAt_chart_sgOf (m := m) (fun q => sgSweep0 Q c w (cbPart q.2))
      (contMDiff_sgSweep_fam' Q c w hQ) p q₀ hreg.2
  exact h1.sub h2

/-! ## The cut-off-scaled system and its parameter derivative -/

section Cutoff

/-- The differentiability order `⊤` is not zero. -/
private lemma top_ne_zero_order_sg : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
  rw [ne_eq, ← WithTop.coe_zero]
  intro h
  exact ENat.top_ne_zero (WithTop.coe_injective h)

/-- A point outside the topological support of `f` has a neighbourhood on which `f` vanishes. -/
private lemma eventually_eq_zero_of_notMem_tsupport_sg {X Y : Type*} [TopologicalSpace X] [Zero Y]
    {f : X → Y} {x : X} (h : x ∉ tsupport f) : ∀ᶠ y in 𝓝 x, f y = 0 := by
  have hopen : IsOpen (tsupport f)ᶜ := (isClosed_tsupport f).isOpen_compl
  refine Filter.mem_of_superset (hopen.mem_nhds (by simpa using h)) ?_
  intro y hy
  by_contra hne
  exact hy (subset_tsupport f hne)

/-- **Global smoothness of the cut-off-scaled charted difference system.**  The two cut-offs `γ` (on
the parameter) and `β` (on the box) put the support inside the region where both values lie in the
chart's source, which is the only place the charted difference map is defined. -/
theorem contDiff_sgCutoff_chartDiff (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (p : CappingSpace) {γ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hγ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {β : Work.Drive.Amb 4 → ℝ} (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    {U : Set (EuclideanSpace ℝ (Fin m))} {V : Set (Work.Drive.Amb 4)}
    (hUV : U ×ˢ V ⊆ {q : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb 4 |
      sgLoop Ξ Q q.1 (sqPart q.2) ∈ (chr p).source ∧
      sgSweep0 Q c w (cbPart q.2) ∈ (chr p).source})
    (hγsupp : tsupport γ ⊆ U) (hβsupp : tsupport β ⊆ V) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb 4 =>
        (γ q.1 * β q.2) • chartDiff p (sgLoop Ξ Q q.1) (sgSweep0 Q c w) q.2) := by
  rw [contDiff_iff_contDiffAt]
  intro q₀
  by_cases hγ0 : q₀.1 ∈ tsupport γ
  · by_cases hβ0 : q₀.2 ∈ tsupport β
    · have hreg : {q : EuclideanSpace ℝ (Fin m) × Amb 4 |
          sgLoop Ξ Q q.1 (sqPart q.2) ∈ (chr p).source ∧
          sgSweep0 Q c w (cbPart q.2) ∈ (chr p).source} (q₀) :=
        hUV ⟨hγsupp hγ0, hβsupp hβ0⟩
      have hχ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
            chartDiff p (sgLoop Ξ Q q.1) (sgSweep0 Q c w) q.2) q₀ :=
        contDiffAt_sgChartDiff Ξ Q c w hΞ hQ p hreg
      have hg : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => γ q.1 * β q.2) q₀ :=
        (hγ.contDiffAt.comp q₀ contDiffAt_fst).mul (hβ.contDiffAt.comp q₀ contDiffAt_snd)
      exact hg.smul hχ
    · refine (contDiffAt_const (c := (0 : Tgt 4))).congr_of_eventuallyEq ?_
      filter_upwards [(continuous_snd.tendsto q₀).eventually
        (eventually_eq_zero_of_notMem_tsupport_sg hβ0)] with q hq
      rw [hq, mul_zero, zero_smul]
  · refine (contDiffAt_const (c := (0 : Tgt 4))).congr_of_eventuallyEq ?_
    filter_upwards [(continuous_fst.tendsto q₀).eventually
      (eventually_eq_zero_of_notMem_tsupport_sg hγ0)] with q hq
    rw [hq, zero_mul, zero_smul]

/-- **The parameter derivative of the cut-off-scaled system is onto at its zeros.**  The parameter
derivative of the charted *loop* value is onto at every point by `ChartPert`, and the chain term does
not depend on the parameter, so the derivative of the difference is onto as well; the cut-off factors
multiply it by the non-zero scalar `γ p₀ * β z`. -/
theorem hsurj_sgCutoff (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q) (p : CappingSpace)
    {γ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hγ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {β : Work.Drive.Amb 4 → ℝ} (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    {U : Set (EuclideanSpace ℝ (Fin m))} {V : Set (Work.Drive.Amb 4)}
    (hUV : U ×ˢ V ⊆ {q : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb 4 |
      sgLoop Ξ Q q.1 (sqPart q.2) ∈ (chr p).source ∧
      sgSweep0 Q c w (cbPart q.2) ∈ (chr p).source})
    (hγsupp : tsupport γ ⊆ U) (hβsupp : tsupport β ⊆ V)
    {p₀ : EuclideanSpace ℝ (Fin m)} (hp₀ : p₀ ∈ tsupport γ)
    {z : Work.Drive.Amb 4} (hz : z ∈ tsupport β)
    (hγ1 : γ p₀ = 1) (hβ1 : β z = 1)
    (hzero : (γ p₀ * β z) • chartDiff p (sgLoop Ξ Q p₀) (sgSweep0 Q c w) z = 0) :
    Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) =>
      (γ p' * β z) • chartDiff p (sgLoop Ξ Q p') (sgSweep0 Q c w) z) p₀) := by
  have hreg : {q : EuclideanSpace ℝ (Fin m) × Amb 4 |
      sgLoop Ξ Q q.1 (sqPart q.2) ∈ (chr p).source ∧
      sgSweep0 Q c w (cbPart q.2) ∈ (chr p).source} (p₀, z) :=
    hUV ⟨hγsupp hp₀, hβsupp hz⟩
  have hχ0 : chartDiff p (sgLoop Ξ Q p₀) (sgSweep0 Q c w) z = 0 := by
    simpa [hγ1, hβ1, mul_one, one_smul] using hzero
  have hχat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
        chartDiff p (sgLoop Ξ Q q.1) (sgSweep0 Q c w) q.2) (p₀, z) :=
    contDiffAt_sgChartDiff Ξ Q c w hΞ hQ p hreg
  have hχcomp : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      ((fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
        chartDiff p (sgLoop Ξ Q q.1) (sgSweep0 Q c w) q.2) ∘
        (fun p' : EuclideanSpace ℝ (Fin m) => (p', z))) p₀ :=
    hχat.comp p₀ (contDiffAt_id.prodMk contDiffAt_const)
  have hχat' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p' : EuclideanSpace ℝ (Fin m) =>
        chartDiff p (sgLoop Ξ Q p') (sgSweep0 Q c w) z) p₀ := hχcomp
  have hχp : HasFDerivAt (fun p' : EuclideanSpace ℝ (Fin m) =>
      chartDiff p (sgLoop Ξ Q p') (sgSweep0 Q c w) z)
      (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) =>
        chartDiff p (sgLoop Ξ Q p') (sgSweep0 Q c w) z) p₀) p₀ :=
    (hχat'.differentiableAt top_ne_zero_order_sg).hasFDerivAt
  have hγβp : HasFDerivAt (fun p' : EuclideanSpace ℝ (Fin m) => γ p' * β z)
      (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => γ p' * β z) p₀) p₀ :=
    ((hγ.contDiffAt.mul contDiffAt_const).differentiableAt top_ne_zero_order_sg).hasFDerivAt
  have hsmul := hγβp.smul hχp
  have h1 : (γ p₀ * β z) •
        (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) =>
          chartDiff p (sgLoop Ξ Q p') (sgSweep0 Q c w) z) p₀)
      + (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => γ p' * β z) p₀).smulRight
          (chartDiff p (sgLoop Ξ Q p₀) (sgSweep0 Q c w) z)
      = fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) =>
          chartDiff p (sgLoop Ξ Q p') (sgSweep0 Q c w) z) p₀ := by
    rw [hγ1, hβ1, mul_one, hχ0]
    simp
  rw [h1] at hsmul
  have hfd : fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) =>
        (γ p' * β z) • chartDiff p (sgLoop Ξ Q p') (sgSweep0 Q c w) z) p₀
      = fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) =>
          chartDiff p (sgLoop Ξ Q p') (sgSweep0 Q c w) z) p₀ := hsmul.fderiv
  rw [hfd]
  -- the parameter derivative of the charted loop value is onto
  have hsrc : pertChart Ξ Q p₀
      (Complex.exp ((Real.pi : ℂ) * (((sqPart z) 0 : ℝ) : ℂ) * Complex.I)) ∈ (chr p).source := by
    simpa [sgLoop, coreLoop, pertChart, Function.comp_def, sqPartCLM_eq_sqPart] using hreg.1
  have hloop := hsurj_sgLoop Ξ Q hΞ hQ p p₀ (sqPart z) hsrc
  have hfun : (fun p' : EuclideanSpace ℝ (Fin m) => chr p (sgLoop Ξ Q p' (sqPart z)))
      = (fun t' : EuclideanSpace ℝ (Fin m) => chr p (pertChart Ξ Q t'
          (Complex.exp ((Real.pi : ℂ) * (((sqPart z) 0 : ℝ) : ℂ) * Complex.I)))) := by
    funext p'
    simp only [sgLoop, coreLoop, pertChart, Function.comp_def]
  have hsub : fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) =>
        chr p (sgLoop Ξ Q p' (sqPart z)) - chr p (sgSweep0 Q c w (cbPart z))) p₀
      = fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => chr p (sgLoop Ξ Q p' (sqPart z))) p₀ := by
    rw [fderiv_sub_const]
  have hfun2 : (fun p' : EuclideanSpace ℝ (Fin m) =>
        chartDiff p (sgLoop Ξ Q p') (sgSweep0 Q c w) z)
      = (fun p' : EuclideanSpace ℝ (Fin m) =>
        chr p (sgLoop Ξ Q p' (sqPart z)) - chr p (sgSweep0 Q c w (cbPart z))) := rfl
  rw [hfun2, hsub, hfun]
  exact hloop

end Cutoff

end

end Work.Drive
