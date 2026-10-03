import Mathlib
import Submission.Lib.Unif2.Work.Kernel.GreenCover
import Submission.Lib.Unif2.Work.Kernel.psmooth_tools
import Submission.Lib.Unif2.Work.Kernel.psLocalQ
import Submission.Lib.Unif2.Work.Kernel.psLocalPole
import Submission.Lib.Unif2.Work.Kernel.exists_modelBump_chartBall
import Submission.Lib.Unif2.Work.Drive.energyGreenRung
import Submission.Lib.Unif2.Work.Drive.chartPoleIdentity

open Set Metric MeasureTheory Filter
open scoped Manifold Topology Gradient ContDiff


/-!
## Note on the imports (namespace move in the shared library)

The certificates are all produced from the hypotheses of the statement, but the *statement of (P)*
that this lemma instantiates (`Work.Kernel.pairing_pole_kernel_general`), the lemmas about the
chart-local pole term it rests on (`pairTerm_pole_centered`, `pairTerm_pole_general`) and the `(Q)`
lemma (`pairing_harmonic_zero_kernel`) currently sit in modules that do **not** compile: a refactor
moved four lemmas out of the namespace `Work.Drive` into `Work.Drive.GreenRung` and those four
consumers were not updated.  To stay independent of that state this lemma uses working copies with
every declaration renamed:

* `Submission/Work/Kernel/psLocalQ.lean`     — `(Q)`, as `Work.Kernel.psPairingHarmonicZeroKernel`,
* `Submission/Work/Kernel/psLocalPole.lean`  — the chart-local pole terms, as
  `Work.Kernel.psPairTerm_pole_of_logExpansion`,
* `Submission/Work/Kernel/psmooth_tools.lean` — the analytic tools of the certificate discharge
  (chart-wise `C¹` representatives, the boundedness/growth bounds for the gradient of a clamped
  pullback, almost-everywhere strong measurability, and the `PairIntegrable`/integrability lemmas
  from support-restricted growth bounds).

The proof of `(P)` itself is reproduced here from `Work.Kernel.pairing_pole_kernel_general`, with the
certificates supplied by the local hypotheses.

-/

namespace Work.Kernel

/-- **(P) with all the technical certificates discharged.**  If the chart representative of `gA`
in the cover's pole chart has the logarithmic expansion `-log‖z-p‖ + H` on a ball `ball p r`, and
a `C¹` test function `Ψ` is supported in the cover's summation region `K`, then the whole surface
pairing of `gA` against `Ψ` evaluates to `2π Ψ a`.

This is `Work.Kernel.pairing_pole_kernel_general` with the bump `η` and *all* the smoothness,
compact-support, `PairIntegrable`, a.e.-differentiability and polar-integrability certificates
produced from the hypotheses (using the `C¹` facts `hψc1`, `hβc1` of the cover weights, which
`Work.Kernel.GreenCover` does **not** carry as fields — get them from
`Work.Kernel.exists_greenCover_centred`).

`hKc` (compactness of `K`) is essential: without it `K = Ω = X` and `Ψ ≡ 1` would satisfy the
smoothness and support hypotheses while the pairing degenerates (`clampedPullback` of a constant is
a ball indicator, so its gradient vanishes a.e.), contradicting the conclusion.  With `K` compact and
`K ⊆ Ω` the test function vanishes near `∂Ω`, and no boundary term appears. -/
theorem pairing_pole_smooth {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X}
    (E : Work.Kernel.GreenCover ι Ω K a b)
    (hKc : IsCompact K) (haK : a ∈ K) (hΩo : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {gA : X → ℝ} (hgA : Work.SimplyConnected.ABS.IsGreenOn Ω a gA)
    (hgAdiff : ∀ k, Work.Drive.ChartDiff (chartAt ℂ (E.y k)) gA (Ω \ ({a, b} : Set X)))
    {H : ℂ → ℝ} {r : ℝ} (hrpos : 0 < r) (hrρ : r ≤ E.ρ E.ia)
    (hpmem : (chartAt ℂ (E.y E.ia)) a ∈
      Metric.ball ((chartAt ℂ (E.y E.ia)) (E.y E.ia)) (E.ρ E.ia))
    (hH : InnerProductSpace.HarmonicOnNhd H (Metric.ball ((chartAt ℂ (E.y E.ia)) a) r))
    (hueq : ∀ z ∈ Metric.ball ((chartAt ℂ (E.y E.ia)) a) r,
      gA ((chartAt ℂ (E.y E.ia)).symm z)
        = -Real.log ‖z - (chartAt ℂ (E.y E.ia)) a‖ + H z)
    (hψc1 : ∀ k i, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 ((E.ψ i) ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    (hβc1 : ∀ k i, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 ((E.β i) ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    {Ψ : X → ℝ}
    (hΨdiff : ∀ k, Work.Drive.ChartDiff (chartAt ℂ (E.y k)) Ψ Ω)
    (hΨc1 : ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 (Ψ ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    (hΨK : tsupport Ψ ⊆ K) (hΨΩ : tsupport Ψ ⊆ Ω) :
    Work.Drive.pairing E.y E.ρ E.σ E.ψ gA Ψ = 2 * Real.pi * Ψ a := by

  classical
  haveI : IsManifold (modelWithCornersSelf ℝ ℂ) (⊤ : WithTop ℕ∞) X :=
    Work.SimplyConnected.ABS.isManifold_self_model_real_infty
  -- the pole chart and the image of the pole
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ (E.y E.ia) with hcdef
  set p : ℂ := c a with hpdef
  have hρpos : 0 < E.ρ E.ia := lt_of_lt_of_le (E.hspos E.ia)
    (le_of_lt (lt_trans (E.hsσ E.ia) (E.hσρ E.ia)))
  have hσnonneg : 0 ≤ E.σ E.ia := le_of_lt (lt_trans (E.hspos E.ia) (E.hsσ E.ia))
  have hσpos : 0 < E.σ E.ia := lt_trans (E.hspos E.ia) (E.hsσ E.ia)
  have hσρ : E.σ E.ia < E.ρ E.ia := E.hσρ E.ia
  have ha_src : a ∈ c.source := (E.ha_mem).1
  have hpa_ball : p ∈ Metric.ball (c (E.y E.ia)) (E.s E.ia) := (E.ha_mem).2
  have hd_lt : ‖c (E.y E.ia) - p‖ < E.s E.ia := by
    have h : dist p (c (E.y E.ia)) < E.s E.ia := Metric.mem_ball.mp hpa_ball
    rwa [dist_eq_norm, norm_sub_rev] at h
  -- a neighbourhood of `a` on which all the other weights vanish
  have hAllZero : ∀ᶠ x in 𝓝 a, ∀ i : ι, i ≠ E.ia → E.ψ i x = 0 := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : i = E.ia
    · exact Filter.Eventually.of_forall (fun x hx => absurd hi hx)
    · exact (GreenCover.ψ_eq_zero_nhds_a E i hi).mono (fun x hx _ => hx)
  obtain ⟨U, hUsub, hUopen, haU⟩ := mem_nhds_iff.mp hAllZero
  have hU'open : IsOpen (U ∩ c.source) := hUopen.inter c.open_source
  have haU' : a ∈ U ∩ c.source := ⟨haU, ha_src⟩
  obtain ⟨εU, hεUpos, hεUsub⟩ := Metric.isOpen_iff.mp
    (c.isOpen_image_of_subset_source hU'open inter_subset_right) (c a) ⟨a, haU', rfl⟩
  obtain ⟨εc, hεcpos, hεcsub⟩ := Metric.isOpen_iff.mp c.open_target (c a) (c.map_source ha_src)
  -- the size of the localising bump
  set m : ℝ := min (r / 2) (min εU (min εc ((E.σ E.ia - ‖c (E.y E.ia) - p‖) / 2))) with hmdef
  have hmpos : 0 < m := by
    rw [hmdef]
    exact lt_min (by linarith) (lt_min hεUpos (lt_min hεcpos (by linarith [hd_lt, E.hsσ E.ia])))
  set ε : ℝ := m / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hεr : ε < r := by
    have h1 : m ≤ r / 2 := by rw [hmdef]; exact min_le_left _ _
    rw [hεdef]; linarith
  have hεU : ε ≤ εU := by
    have h1 : m ≤ εU := le_trans (min_le_right _ _) (min_le_left _ _)
    rw [hεdef]; linarith
  have hεc : ε ≤ εc := by
    have h1 : m ≤ εc := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    rw [hεdef]; linarith
  have hεσ : ε + ‖c (E.y E.ia) - p‖ ≤ E.σ E.ia := by
    have h1 : m ≤ (E.σ E.ia - ‖c (E.y E.ia) - p‖) / 2 :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    rw [hεdef]; linarith
  -- the bump
  obtain ⟨η, hηsm, hηnn, hηle, hηone_ball, hηsupp_ball⟩ :=
    Work.Kernel.exists_modelBump_chartBall (y := E.y E.ia) (p := p) (r₁ := ε / 2) (r₂ := ε)
      (by linarith) hεpos ((Metric.ball_subset_ball hεc).trans hεcsub)
  have hηOne : η =ᶠ[𝓝 a] 1 := by
    have hmem : a ∈ Submission.chartBall c p (ε / 4) := by
      refine Submission.mem_chartBall.mpr ⟨ha_src, ?_⟩
      rw [Metric.mem_ball, dist_self]; linarith
    filter_upwards [(Submission.chartBall_isOpen c p (ε / 4)).mem_nhds hmem] with x hx
    obtain ⟨hxsrc, hxball⟩ := Submission.mem_chartBall.mp hx
    exact hηone_ball x hxsrc
      (Metric.ball_subset_closedBall (Metric.ball_subset_ball (by linarith) hxball))
  have hηK : tsupport (η * Ψ) ⊆ K := (tsupport_mul_subset_right).trans hΨK
  have hηΩ : tsupport (η * Ψ) ⊆ Ω := (tsupport_mul_subset_right).trans hΨΩ
  have hηψ : ∀ i : ι, i ≠ E.ia → ∀ x ∈ tsupport (η * Ψ), E.ψ i x = 0 := by
    intro i hi x hx
    obtain ⟨hxsrc, hxball⟩ := hηsupp_ball (tsupport_mul_subset_left hx)
    have hxU : x ∈ U := by
      have h1 : c x ∈ Metric.ball p εU := Metric.ball_subset_ball hεU hxball
      obtain ⟨u, ⟨huU, husrc⟩, hcu⟩ := hεUsub h1
      have h2 : c.symm (c x) = c.symm (c u) := by rw [hcu]
      rw [c.left_inv hxsrc, c.left_inv husrc] at h2
      rw [h2]; exact huU
    exact hUsub hxU i hi
  have hηc1k : ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 (η ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x) :=
    fun k => PS.contDiffAt_chart_of_contMDiff' hηsm (E.y k)
  have hηc1 : ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 ((η * Ψ) ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x) := by
    intro k x hx
    have hfun : ((η * Ψ) ∘ (chartAt ℂ (E.y k)).symm)
        = (fun w : ℂ => η ((chartAt ℂ (E.y k)).symm w) * Ψ ((chartAt ℂ (E.y k)).symm w)) := rfl
    rw [hfun]
    exact (hηc1k k x hx).mul (hΨc1 k x hx)
  have hηdiff : ∀ k, Work.Drive.ChartDiff (chartAt ℂ (E.y k)) (η * Ψ) Ω := fun k x hx =>
    (hηc1 k x hx.2).differentiableAt (by norm_num)
  have hηsupp : tsupport (η * Ψ) ⊆ c ⁻¹' Metric.ball (c (E.y E.ia)) (E.σ E.ia) := by
    intro x hx
    obtain ⟨hxsrc, hxball⟩ := hηsupp_ball (tsupport_mul_subset_left hx)
    rw [Set.mem_preimage]
    have h2 : ‖c x - p‖ < ε := by
      rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hxball
      exact hxball
    have h1 : ‖c x - c (E.y E.ia)‖ ≤ ‖c x - p‖ + ‖p - c (E.y E.ia)‖ := by
      have h := norm_add_le (c x - p) (p - c (E.y E.ia))
      rwa [sub_add_sub_cancel] at h
    have h3 : ‖c x - c (E.y E.ia)‖ < E.σ E.ia := by
      have h4 : ‖p - c (E.y E.ia)‖ = ‖c (E.y E.ia) - p‖ := norm_sub_rev p (c (E.y E.ia))
      linarith
    rwa [Metric.mem_ball, dist_eq_norm]
  have hηcs := Work.Drive.GreenRung.contDiff_clampedPullback_hasCompactSupport (x₀ := E.y E.ia)
    (u := η * Ψ) (ρ := E.ρ E.ia) (ρ₀ := E.σ E.ia) hρpos hσnonneg hσρ (E.htgt E.ia)
    (hηc1 E.ia) hηsupp
  have hηc1a : ContDiff ℝ 1 (Work.Drive.clampedPullback (E.y E.ia) (E.ρ E.ia) (η * Ψ)) := hηcs.1
  have hηcsa : HasCompactSupport (Work.Drive.clampedPullback (E.y E.ia) (E.ρ E.ia) (η * Ψ)) :=
    hηcs.2
  have hχsupp_closed : tsupport (Work.Drive.clampedPullback (E.y E.ia) (E.ρ E.ia) (η * Ψ)) ⊆
      Metric.closedBall p ε := by
    have hsupp_sub : Function.support (Work.Drive.clampedPullback (E.y E.ia) (E.ρ E.ia) (η * Ψ))
        ⊆ Metric.ball p ε := by
      intro z hz
      rw [Function.mem_support] at hz
      have hzρ : z ∈ Metric.ball (c (E.y E.ia)) (E.ρ E.ia) := by
        by_contra hcon
        exact hz (Work.Drive.clampedPullback_eq_zero_of_notMem_ball hcon)
      have hzne : (η * Ψ) (c.symm z) ≠ 0 := by
        rw [← Work.Drive.clampedPullback_apply_of_mem (u := η * Ψ) hzρ]; exact hz
      have hzts : c.symm z ∈ tsupport (η * Ψ) := subset_tsupport _ (Function.mem_support.mpr hzne)
      have hb := (hηsupp_ball (tsupport_mul_subset_left hzts)).2
      rw [Set.mem_preimage, c.right_inv (E.htgt E.ia hzρ)] at hb
      exact hb
    calc tsupport (Work.Drive.clampedPullback (E.y E.ia) (E.ρ E.ia) (η * Ψ))
        = closure (Function.support (Work.Drive.clampedPullback (E.y E.ia) (E.ρ E.ia) (η * Ψ))) :=
          rfl
      _ ⊆ closure (Metric.ball p ε) := closure_mono hsupp_sub
      _ = Metric.closedBall p ε := closure_ball p (ne_of_gt hεpos)
  have hεr2 : ε < r / 2 := by
    have h1 : m ≤ r / 2 := by rw [hmdef]; exact min_le_left _ _
    rw [hεdef]; linarith [hrpos]
  have hηball : tsupport (Work.Drive.clampedPullback (E.y E.ia) (E.ρ E.ia) (η * Ψ)) ⊆
      Metric.ball p r := by
    calc tsupport (Work.Drive.clampedPullback (E.y E.ia) (E.ρ E.ia) (η * Ψ))
        ⊆ Metric.closedBall p ε := hχsupp_closed
      _ ⊆ Metric.ball p (r / 2) := Metric.closedBall_subset_ball hεr2
      _ ⊆ Metric.ball p r := Metric.ball_subset_ball (by linarith [hrpos])
  -- the chart ball of the cover lies in `Ω` and in the chart source
  have hchartΩ : ∀ (i : ι) (y : ℂ),
      y ∈ Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.ρ i) →
        (chartAt ℂ (E.y i)).symm y ∈ Ω ∩ (chartAt ℂ (E.y i)).source := by
    intro i y hy
    refine ⟨?_, (chartAt ℂ (E.y i)).map_target (E.htgt i hy)⟩
    refine E.hballΩ i ⟨(chartAt ℂ (E.y i)).map_target (E.htgt i hy), ?_⟩
    rw [Set.mem_preimage, (chartAt ℂ (E.y i)).right_inv (E.htgt i hy)]
    exact hy
  -- (1) almost-everywhere differentiability of the clamped chart pullbacks
  have hηd : ∀ i, ∀ᵐ z ∂(volume : Measure ℂ),
      DifferentiableAt ℝ (Work.Drive.clampedPullback (E.y i) (E.ρ i) (η * Ψ)) z := by
    intro i
    refine Work.Drive.GreenRung.clampedPullback_differentiableAt_ae_of_differentiableOn
      (x := E.y i) (ρ := E.ρ i) (u := η * Ψ) (E.htgt i) ?_
    intro y hy
    have hytgt : (chartAt ℂ (E.y i)) y ∈ (chartAt ℂ (E.y i)).target := E.htgt i hy
    have hysrc : (chartAt ℂ (E.y i)).symm ((chartAt ℂ (E.y i)) y) ∈
        (chartAt ℂ (E.y i)).source := (chartAt ℂ (E.y i)).map_target hytgt
    have hyright : (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)).symm ((chartAt ℂ (E.y i)) y)) =
        (chartAt ℂ (E.y i)) y := (chartAt ℂ (E.y i)).right_inv hytgt
    have hyΩ : (chartAt ℂ (E.y i)).symm ((chartAt ℂ (E.y i)) y) ∈ Ω := by
      refine E.hballΩ i ⟨hysrc, ?_⟩
      rw [Set.mem_preimage, hyright]; exact hy
    have h := hηdiff i _ ⟨hyΩ, hysrc⟩
    rwa [hyright] at h
  have hDd : ∀ i, ∀ᵐ z ∂(volume : Measure ℂ),
      DifferentiableAt ℝ (Work.Drive.clampedPullback (E.y i) (E.ρ i) (Ψ - η * Ψ)) z := by
    intro i
    refine Work.Drive.GreenRung.clampedPullback_differentiableAt_ae_of_differentiableOn
      (x := E.y i) (ρ := E.ρ i) (u := Ψ - η * Ψ) (E.htgt i) ?_
    intro y hy
    have hytgt : (chartAt ℂ (E.y i)) y ∈ (chartAt ℂ (E.y i)).target := E.htgt i hy
    have hysrc : (chartAt ℂ (E.y i)).symm ((chartAt ℂ (E.y i)) y) ∈
        (chartAt ℂ (E.y i)).source := (chartAt ℂ (E.y i)).map_target hytgt
    have hyright : (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)).symm ((chartAt ℂ (E.y i)) y)) =
        (chartAt ℂ (E.y i)) y := (chartAt ℂ (E.y i)).right_inv hytgt
    have hyΩ : (chartAt ℂ (E.y i)).symm ((chartAt ℂ (E.y i)) y) ∈ Ω := by
      refine E.hballΩ i ⟨hysrc, ?_⟩
      rw [Set.mem_preimage, hyright]; exact hy
    have h1 := hΨdiff i _ ⟨hyΩ, hysrc⟩
    have h2 := hηdiff i _ ⟨hyΩ, hysrc⟩
    rw [hyright] at h1 h2
    change DifferentiableAt ℝ (fun w : ℂ => (Ψ - η * Ψ) ((chartAt ℂ (E.y i)).symm w))
      ((chartAt ℂ (E.y i)) y)
    rw [show (fun w : ℂ => (Ψ - η * Ψ) ((chartAt ℂ (E.y i)).symm w))
        = (fun w : ℂ => Ψ ((chartAt ℂ (E.y i)).symm w)
            - (η * Ψ) ((chartAt ℂ (E.y i)).symm w)) from rfl]
    exact h1.sub h2
  have hQI1 : ∀ i k, ∀ᵐ z ∂(volume : Measure ℂ),
      DifferentiableAt ℝ (Work.Drive.clampedPullback (E.y i) (E.ρ i) (E.ψ k * (Ψ - η * Ψ))) z := by
    intro i k
    refine Work.Drive.GreenRung.clampedPullback_differentiableAt_ae_of_differentiableOn
      (x := E.y i) (ρ := E.ρ i) (u := E.ψ k * (Ψ - η * Ψ)) (E.htgt i) ?_
    intro y hy
    have hytgt : (chartAt ℂ (E.y i)) y ∈ (chartAt ℂ (E.y i)).target := E.htgt i hy
    have hysrc : (chartAt ℂ (E.y i)).symm ((chartAt ℂ (E.y i)) y) ∈
        (chartAt ℂ (E.y i)).source := (chartAt ℂ (E.y i)).map_target hytgt
    have hyright : (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)).symm ((chartAt ℂ (E.y i)) y)) =
        (chartAt ℂ (E.y i)) y := (chartAt ℂ (E.y i)).right_inv hytgt
    have h1 := (hψc1 i k _ hysrc).differentiableAt (by norm_num)
    have h2 := (hΨc1 i _ hysrc).differentiableAt (by norm_num)
    have h3 := (hηc1 i _ hysrc).differentiableAt (by norm_num)
    rw [hyright] at h1 h2 h3
    change DifferentiableAt ℝ (fun w : ℂ => (E.ψ k * (Ψ - η * Ψ)) ((chartAt ℂ (E.y i)).symm w))
      ((chartAt ℂ (E.y i)) y)
    rw [show (fun w : ℂ => (E.ψ k * (Ψ - η * Ψ)) ((chartAt ℂ (E.y i)).symm w))
        = (fun w : ℂ => E.ψ k ((chartAt ℂ (E.y i)).symm w)
            * (Ψ ((chartAt ℂ (E.y i)).symm w) - (η * Ψ) ((chartAt ℂ (E.y i)).symm w))) from rfl]
    exact h1.mul (h2.sub h3)
  -- chart-wise `C¹` of the second summand
  have htestc1 : ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 ((Ψ - η * Ψ) ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x) := by
    intro k x hx
    have hfun : ((Ψ - η * Ψ) ∘ (chartAt ℂ (E.y k)).symm)
        = (fun w : ℂ => Ψ ((chartAt ℂ (E.y k)).symm w)
            - (η * Ψ) ((chartAt ℂ (E.y k)).symm w)) := rfl
    rw [hfun]
    exact (hΨc1 k x hx).sub (hηc1 k x hx)
  -- (2) the per-chart growth data of the clamped pullback of `gA`
  have hgrowth : ∀ i : ι, ∃ (q : ℂ) (C : ℝ), 0 < C ∧
      ∀ z ∈ Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.s i), z ≠ q →
        ‖gradient (Work.Drive.clampedPullback (E.y i) (E.ρ i) gA) z‖ ≤ C / ‖z - q‖ := by
    intro i
    by_cases hi : i = E.ia
    · subst hi
      obtain ⟨C, hCpos, hC⟩ := PS.exists_growth_clampedPullback_le_of_logExpansion
        (Ω := Ω) (a := a) (gA := gA) (y := E.y E.ia) (ρ := E.ρ E.ia) (σ := E.s E.ia)
        (δ := r) (H := H) hgA (lt_trans (E.hsσ E.ia) (E.hσρ E.ia)) (E.htgt E.ia)
        (E.hballΩ E.ia) hrpos hH (fun z hz _ => hueq z hz)
      exact ⟨(chartAt ℂ (E.y E.ia)) a, C, hCpos, hC⟩
    · obtain ⟨C, hCpos, hC⟩ := PS.exists_bound_clampedPullback_le_of_notMem
        (Ω := Ω) (a := a) (gA := gA) (y := E.y i) (ρ := E.ρ i) (σ := E.σ i)
        hgA (E.hσρ i) (E.htgt i) (E.hballΩ i) (E.ha_nmem i hi)
      refine ⟨(chartAt ℂ (E.y i)) (E.y i), C * E.s i + 1,
        by nlinarith [hCpos, E.hspos i], ?_⟩
      intro z hz hzq
      have hzb : ‖gradient (Work.Drive.clampedPullback (E.y i) (E.ρ i) gA) z‖ ≤ C :=
        hC z (Metric.closedBall_subset_closedBall (le_of_lt (E.hsσ i)) hz)
      refine le_trans hzb ?_
      have hnorm : ‖z - (chartAt ℂ (E.y i)) (E.y i)‖ ≤ E.s i := by
        rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hz
      have hpos : 0 < ‖z - (chartAt ℂ (E.y i)) (E.y i)‖ :=
        norm_pos_iff.mpr (sub_ne_zero.mpr hzq)
      rw [le_div_iff₀ hpos]
      nlinarith [hCpos, E.hspos i, hnorm]
  -- the harmonicity of `gA` gives the chart-wise `C¹` property off the pole
  have hgAc1 : ∀ (i : ι) (x : X), x ∈ Submission.chartBall (chartAt ℂ (E.y i))
      ((chartAt ℂ (E.y i)) (E.y i)) (E.ρ i) → x ≠ a →
      ContDiffAt ℝ 1 (gA ∘ (chartAt ℂ (E.y i)).symm) ((chartAt ℂ (E.y i)) x) := by
    intro i x hx hxne
    have hharm : Submission.HarmonicOnXAt gA x := hgA.2.1 x ⟨E.hballΩ i hx, hxne⟩
    have h := (Submission.HarmonicOnXAt_iff_chart (u := gA) (x := x) (y := E.y i) hx.1).mp hharm
    exact h.1.of_le (by norm_num)
  -- (3) the `PairIntegrable` certificates
  have hηI : ∀ i, Work.Drive.PairIntegrable (E.y i) (E.ρ i) (E.σ i) (E.ψ i) gA (η * Ψ) := by
    intro i
    obtain ⟨q, C, hCpos, hC⟩ := hgrowth i
    obtain ⟨Cχ, hCχnn, hCχ⟩ := PS.gradient_clampedPullback_le' (y := E.y i) (ρ := E.ρ i)
      (σ := E.σ i) (Φ := η * Ψ) (E.hσρ i) (E.htgt i) (hηc1 i)
    have hsuppW : tsupport (E.ψ i) ⊆
        Submission.chartBall (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)) (E.y i)) (E.s i) :=
      E.hψsupp i
    have hW := Work.Drive.GreenRung.contDiff_clampedPullback_hasCompactSupport (x₀ := E.y i)
      (u := E.ψ i) (ρ := E.σ i) (ρ₀ := E.s i) (lt_trans (E.hspos i) (E.hsσ i))
      (le_of_lt (E.hspos i)) (E.hsσ i)
      ((Metric.ball_subset_ball (le_of_lt (E.hσρ i))).trans (E.htgt i)) (hψc1 i i)
      (fun x hx => (hsuppW hx).2)
    refine PS.pairIntegrable_of_support_growth' (x := E.y i) (ρ := E.ρ i) (σ := E.σ i)
      (W := E.ψ i) (f := gA) (χ := η * Ψ) (p := q) (C := C) (K := Cχ)
      hCpos.le hCχnn hW.1.continuous hW.2 ?_ ?_ ?_
    · filter_upwards [compl_mem_ae_iff.mpr (measure_singleton q)] with z hzq hz
      have hzball : z ∈ Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.s i) :=
        PS.tsupport_clampedPullback_subset_closedBall'
          ((Metric.ball_subset_ball (le_of_lt (E.hσρ i))).trans (E.htgt i)) hsuppW hz
      exact hC z hzball (by simpa using hzq)
    · filter_upwards with z hz
      have hzball : z ∈ Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.s i) :=
        PS.tsupport_clampedPullback_subset_closedBall'
          ((Metric.ball_subset_ball (le_of_lt (E.hσρ i))).trans (E.htgt i)) hsuppW hz
      exact hCχ z (Metric.closedBall_subset_ball (E.hsσ i) hzball)
    · exact (PS.aeStronglyMeasurable_gradient_clampedPullback' (y := E.y i) (ρ := E.ρ i)
        (u := gA) (x₀ := a) (E.htgt i) (hgAc1 i)).inner
        (PS.aeStronglyMeasurable_gradient_clampedPullback' (y := E.y i) (ρ := E.ρ i)
          (u := η * Ψ) (x₀ := a) (E.htgt i) (fun x hx _ => hηc1 i x hx.1))
  have hDI : ∀ i, Work.Drive.PairIntegrable (E.y i) (E.ρ i) (E.σ i) (E.ψ i) gA (Ψ - η * Ψ) := by
    intro i
    obtain ⟨q, C, hCpos, hC⟩ := hgrowth i
    obtain ⟨Cχ, hCχnn, hCχ⟩ := PS.gradient_clampedPullback_le' (y := E.y i) (ρ := E.ρ i)
      (σ := E.σ i) (Φ := Ψ - η * Ψ) (E.hσρ i) (E.htgt i) (htestc1 i)
    have hsuppW : tsupport (E.ψ i) ⊆
        Submission.chartBall (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)) (E.y i)) (E.s i) :=
      E.hψsupp i
    have hW := Work.Drive.GreenRung.contDiff_clampedPullback_hasCompactSupport (x₀ := E.y i)
      (u := E.ψ i) (ρ := E.σ i) (ρ₀ := E.s i) (lt_trans (E.hspos i) (E.hsσ i))
      (le_of_lt (E.hspos i)) (E.hsσ i)
      ((Metric.ball_subset_ball (le_of_lt (E.hσρ i))).trans (E.htgt i)) (hψc1 i i)
      (fun x hx => (hsuppW hx).2)
    refine PS.pairIntegrable_of_support_growth' (x := E.y i) (ρ := E.ρ i) (σ := E.σ i)
      (W := E.ψ i) (f := gA) (χ := Ψ - η * Ψ) (p := q) (C := C) (K := Cχ)
      hCpos.le hCχnn hW.1.continuous hW.2 ?_ ?_ ?_
    · filter_upwards [compl_mem_ae_iff.mpr (measure_singleton q)] with z hzq hz
      have hzball : z ∈ Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.s i) :=
        PS.tsupport_clampedPullback_subset_closedBall'
          ((Metric.ball_subset_ball (le_of_lt (E.hσρ i))).trans (E.htgt i)) hsuppW hz
      exact hC z hzball (by simpa using hzq)
    · filter_upwards with z hz
      have hzball : z ∈ Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.s i) :=
        PS.tsupport_clampedPullback_subset_closedBall'
          ((Metric.ball_subset_ball (le_of_lt (E.hσρ i))).trans (E.htgt i)) hsuppW hz
      exact hCχ z (Metric.closedBall_subset_ball (E.hsσ i) hzball)
    · exact (PS.aeStronglyMeasurable_gradient_clampedPullback' (y := E.y i) (ρ := E.ρ i)
        (u := gA) (x₀ := a) (E.htgt i) (hgAc1 i)).inner
        (PS.aeStronglyMeasurable_gradient_clampedPullback' (y := E.y i) (ρ := E.ρ i)
          (u := Ψ - η * Ψ) (x₀ := a) (E.htgt i) (fun x hx _ => htestc1 i x hx.1))
  have hQI2 : ∀ i k, Work.Drive.PairIntegrable (E.y i) (E.ρ i) (E.σ i) (E.ψ i * E.β k)
      gA (E.ψ k * (Ψ - η * Ψ)) := by
    intro i k
    obtain ⟨q, C, hCpos, hC⟩ := hgrowth i
    have hsuppW : tsupport (E.ψ i * E.β k) ⊆
        Submission.chartBall (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)) (E.y i)) (E.s i) :=
      (tsupport_mul_subset_left).trans (E.hψsupp i)
    have hWc1 : ∀ x ∈ (chartAt ℂ (E.y i)).source,
        ContDiffAt ℝ 1 ((E.ψ i * E.β k) ∘ (chartAt ℂ (E.y i)).symm)
          ((chartAt ℂ (E.y i)) x) := by
      intro x hx
      have hfun : ((E.ψ i * E.β k) ∘ (chartAt ℂ (E.y i)).symm)
          = (fun w : ℂ => E.ψ i ((chartAt ℂ (E.y i)).symm w)
              * E.β k ((chartAt ℂ (E.y i)).symm w)) := rfl
      rw [hfun]
      exact (hψc1 i i x hx).mul (hβc1 i k x hx)
    have hW := Work.Drive.GreenRung.contDiff_clampedPullback_hasCompactSupport (x₀ := E.y i)
      (u := E.ψ i * E.β k) (ρ := E.σ i) (ρ₀ := E.s i) (lt_trans (E.hspos i) (E.hsσ i))
      (le_of_lt (E.hspos i)) (E.hsσ i)
      ((Metric.ball_subset_ball (le_of_lt (E.hσρ i))).trans (E.htgt i)) hWc1
      (fun x hx => (hsuppW hx).2)
    have hχc1 : ∀ x ∈ (chartAt ℂ (E.y i)).source,
        ContDiffAt ℝ 1 ((E.ψ k * (Ψ - η * Ψ)) ∘ (chartAt ℂ (E.y i)).symm)
          ((chartAt ℂ (E.y i)) x) := by
      intro x hx
      have hfun : ((E.ψ k * (Ψ - η * Ψ)) ∘ (chartAt ℂ (E.y i)).symm)
          = (fun w : ℂ => E.ψ k ((chartAt ℂ (E.y i)).symm w)
              * (Ψ ((chartAt ℂ (E.y i)).symm w) - (η * Ψ) ((chartAt ℂ (E.y i)).symm w))) := rfl
      rw [hfun]
      exact (hψc1 i k x hx).mul ((hΨc1 i x hx).sub (hηc1 i x hx))
    obtain ⟨Cχ, hCχnn, hCχ⟩ := PS.gradient_clampedPullback_le' (y := E.y i) (ρ := E.ρ i)
      (σ := E.σ i) (Φ := E.ψ k * (Ψ - η * Ψ)) (E.hσρ i) (E.htgt i) hχc1
    refine PS.pairIntegrable_of_support_growth' (x := E.y i) (ρ := E.ρ i) (σ := E.σ i)
      (W := E.ψ i * E.β k) (f := gA) (χ := E.ψ k * (Ψ - η * Ψ)) (p := q) (C := C) (K := Cχ)
      hCpos.le hCχnn hW.1.continuous hW.2 ?_ ?_ ?_
    · filter_upwards [compl_mem_ae_iff.mpr (measure_singleton q)] with z hzq hz
      have hzball : z ∈ Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.s i) :=
        PS.tsupport_clampedPullback_subset_closedBall'
          ((Metric.ball_subset_ball (le_of_lt (E.hσρ i))).trans (E.htgt i)) hsuppW hz
      exact hC z hzball (by simpa using hzq)
    · filter_upwards with z hz
      have hzball : z ∈ Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.s i) :=
        PS.tsupport_clampedPullback_subset_closedBall'
          ((Metric.ball_subset_ball (le_of_lt (E.hσρ i))).trans (E.htgt i)) hsuppW hz
      exact hCχ z (Metric.closedBall_subset_ball (E.hsσ i) hzball)
    · exact (PS.aeStronglyMeasurable_gradient_clampedPullback' (y := E.y i) (ρ := E.ρ i)
        (u := gA) (x₀ := a) (E.htgt i) (hgAc1 i)).inner
        (PS.aeStronglyMeasurable_gradient_clampedPullback' (y := E.y i) (ρ := E.ρ i)
          (u := E.ψ k * (Ψ - η * Ψ)) (x₀ := a) (E.htgt i) (fun x hx _ => hχc1 x hx.1))
  -- (4) the polar integrability certificates
  have hpol1 : Integrable (fun z : ℂ => inner (𝕜 := ℝ)
      (gradient (fun y : ℂ => -Real.log ‖y - p‖) z)
      (gradient (Work.Drive.clampedPullback (E.y E.ia) (E.ρ E.ia) (η * Ψ)) z)) :=
    Work.Analysis.Harmonic.integrable_inner_gradient_logNorm_sub hηc1a hηcsa
  have hpol2 : Integrable (fun z : ℂ => inner (𝕜 := ℝ) (gradient H z)
      (gradient (Work.Drive.clampedPullback (E.y E.ia) (E.ρ E.ia) (η * Ψ)) z)) := by
    refine Work.Analysis.Harmonic.integrable_inner_gradient_of_contDiffAt_near hηc1a hηcsa ?_
    intro z hz
    have hzr : z ∈ Metric.ball p r :=
      Metric.ball_subset_ball (by linarith [hrpos]) (hηball hz)
    exact (hH z hzr).1.of_le (by norm_num)
  have hpol3 : Integrable (fun z : ℂ => inner (𝕜 := ℝ)
      (gradient (Work.Drive.clampedPullback (E.y E.ia) (E.ρ E.ia) gA) z)
      (gradient (Work.Drive.clampedPullback (E.y E.ia) (E.ρ E.ia) (η * Ψ)) z)) := by
    obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.Drive.exists_norm_gradient_le_of_logExpansion
      (u := fun w : ℂ => gA (c.symm w)) (H := H) (p := p) (ρ := r) hrpos hH
      (fun z hz _ => hueq z hz)
    refine PS.integrable_inner_gradient_of_growth'
      (f := Work.Drive.clampedPullback (E.y E.ia) (E.ρ E.ia) gA)
      (χ := Work.Drive.clampedPullback (E.y E.ia) (E.ρ E.ia) (η * Ψ)) (p := p) (C := C₁)
      hC₁pos.le ?_ hηc1a hηcsa ?_
    · exact PS.aeStronglyMeasurable_gradient_clampedPullback' (y := E.y E.ia) (ρ := E.ρ E.ia)
        (u := gA) (x₀ := a) (E.htgt E.ia) (hgAc1 E.ia)
    · filter_upwards [compl_mem_ae_iff.mpr (measure_singleton p)] with z hzp hz
      have hzr : z ∈ Metric.ball p (r / 2) :=
        Metric.closedBall_subset_ball hεr2 (hχsupp_closed hz)
      have hzp' : ‖z - p‖ ≤ ε := by
        have h := hχsupp_closed hz
        rwa [Metric.mem_closedBall, dist_eq_norm] at h
      have hzρ : z ∈ Metric.ball (c (E.y E.ia)) (E.ρ E.ia) := by
        rw [Metric.mem_ball, dist_eq_norm]
        calc ‖z - c (E.y E.ia)‖ ≤ ‖z - p‖ + ‖p - c (E.y E.ia)‖ := by
              have h := norm_add_le (z - p) (p - c (E.y E.ia))
              rwa [sub_add_sub_cancel] at h
          _ = ‖z - p‖ + ‖c (E.y E.ia) - p‖ := by rw [norm_sub_rev p (c (E.y E.ia))]
          _ ≤ ε + ‖c (E.y E.ia) - p‖ := by linarith
          _ ≤ E.σ E.ia := hεσ
          _ < E.ρ E.ia := E.hσρ E.ia
      have heq : gradient (Work.Drive.clampedPullback (E.y E.ia) (E.ρ E.ia) gA) z
          = gradient (fun w : ℂ => gA (c.symm w)) z :=
        (PS.clamped_eq_unclamped_of_mem_ball (ρ := E.ρ E.ia) (g := gA) (y := E.y E.ia) hzρ).self_of_nhds
      rw [heq]
      exact hC₁ z hzr (by simpa using hzp)

  -- `a` is not in the support of the localised second summand.
  have hnota : a ∉ tsupport (Ψ - η * Ψ) := by
    intro hmem
    have h0 : (fun x : X => Ψ x - η x * Ψ x) =ᶠ[𝓝 a] 0 := by
      filter_upwards [hηOne] with x hx
      show Ψ x - η x * Ψ x = 0
      rw [show η x = 1 from by simpa using hx, one_mul, sub_self]
    obtain ⟨U, hUsub, hUopen, haU⟩ := mem_nhds_iff.mp h0
    have hsub : Function.support (Ψ - η * Ψ) ⊆ Uᶜ := by
      intro x hx hxU
      exact hx (hUsub hxU)
    have hcl : tsupport (Ψ - η * Ψ) ⊆ Uᶜ := closure_minimal hsub hUopen.isClosed_compl
    exact hcl hmem haU
  -- its support is contained in the union of the two summands' supports
  have hsupp_sub : tsupport (Ψ - η * Ψ) ⊆ tsupport Ψ ∪ tsupport (η * Ψ) := by
    rw [tsupport]
    refine closure_minimal ?_ ((isClosed_tsupport _).union (isClosed_tsupport _))
    intro x hx
    rw [Function.mem_support, Pi.sub_apply] at hx
    by_cases h1 : Ψ x = 0
    · refine Or.inr (subset_tsupport _ (Function.mem_support.mpr ?_))
      intro h2
      exact hx (by rw [h1, h2, sub_zero])
    · exact Or.inl (subset_tsupport _ (Function.mem_support.mpr h1))
  -- (1) linearity of the pairing in the test function
  have hadd : ∀ φ₁ φ₂ : X → ℝ,
      (∀ i, ∀ᵐ z ∂(volume : Measure ℂ),
        DifferentiableAt ℝ (Work.Drive.clampedPullback (E.y i) (E.ρ i) φ₁) z) →
      (∀ i, ∀ᵐ z ∂(volume : Measure ℂ),
        DifferentiableAt ℝ (Work.Drive.clampedPullback (E.y i) (E.ρ i) φ₂) z) →
      (∀ i, Work.Drive.PairIntegrable (E.y i) (E.ρ i) (E.σ i) (E.ψ i) gA φ₁) →
      (∀ i, Work.Drive.PairIntegrable (E.y i) (E.ρ i) (E.σ i) (E.ψ i) gA φ₂) →
      Work.Drive.pairing E.y E.ρ E.σ E.ψ gA (φ₁ + φ₂)
        = Work.Drive.pairing E.y E.ρ E.σ E.ψ gA φ₁
          + Work.Drive.pairing E.y E.ρ E.σ E.ψ gA φ₂ := by
    intro φ₁ φ₂ h1 h2 h3 h4
    simp only [Work.Drive.pairing]
    calc ∑ i, Work.Drive.pairTerm (E.y i) (E.ρ i) (E.σ i) (E.ψ i) gA (φ₁ + φ₂)
        = ∑ i, (Work.Drive.pairTerm (E.y i) (E.ρ i) (E.σ i) (E.ψ i) gA φ₁
            + Work.Drive.pairTerm (E.y i) (E.ρ i) (E.σ i) (E.ψ i) gA φ₂) :=
          Finset.sum_congr rfl fun i _ =>
            Work.Drive.pairTerm_add (h1 i) (h2 i) (h3 i) (h4 i)
      _ = (∑ i, Work.Drive.pairTerm (E.y i) (E.ρ i) (E.σ i) (E.ψ i) gA φ₁)
          + (∑ i, Work.Drive.pairTerm (E.y i) (E.ρ i) (E.σ i) (E.ψ i) gA φ₂) :=
          Finset.sum_add_distrib
  have hlin : Work.Drive.pairing E.y E.ρ E.σ E.ψ gA Ψ
      = Work.Drive.pairing E.y E.ρ E.σ E.ψ gA (η * Ψ)
        + Work.Drive.pairing E.y E.ρ E.σ E.ψ gA (Ψ - η * Ψ) := by
    conv_lhs => rw [show Ψ = η * Ψ + (Ψ - η * Ψ) from by
      funext x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
      ring]
    exact hadd (η * Ψ) (Ψ - η * Ψ) hηd hDd hηI hDI
  -- (2) (Q) kills the second summand
  have hQ : Work.Drive.pairing E.y E.ρ E.σ E.ψ gA (Ψ - η * Ψ) = 0 := by
    refine psPairingHarmonicZeroKernel E ?_ ?_ ?_ ?_ ?_ ?_ hψc1 hβc1 hQI1 hQI2
    · intro k x hx
      have h1 := hΨdiff k x hx
      have h2 := hηdiff k x hx
      have : (fun w : ℂ => (Ψ - η * Ψ) ((chartAt ℂ (E.y k)).symm w))
          = (fun w : ℂ => Ψ ((chartAt ℂ (E.y k)).symm w)
              - (η * Ψ) ((chartAt ℂ (E.y k)).symm w)) := rfl
      rw [this]
      exact h1.sub h2
    · intro k x hx
      have h1 := hΨc1 k x hx
      have h2 := hηc1 k x hx
      have : ((Ψ - η * Ψ) ∘ (chartAt ℂ (E.y k)).symm)
          = (fun w : ℂ => Ψ ((chartAt ℂ (E.y k)).symm w)
              - (η * Ψ) ((chartAt ℂ (E.y k)).symm w)) := rfl
      rw [this]
      exact h1.sub h2
    · intro x hx
      rcases hsupp_sub hx with h1 | h2
      · exact hΨK h1
      · exact hηK h2
    · intro x hx
      rcases hsupp_sub hx with h1 | h2
      · exact hΨΩ h1
      · exact hηΩ h2
    · intro x hx
      have hxΩ : x ∈ Ω := by
        rcases hsupp_sub hx with h1 | h2
        · exact hΨΩ h1
        · exact hηΩ h2
      exact hgA.2.1 x ⟨hxΩ, fun hxa => hnota (hxa ▸ hx)⟩
    · exact hgAdiff
  -- (3) the pairing of `η * Ψ` collapses to the `ia`-th term
  have hterminate : ∀ i, i ≠ E.ia →
      Work.Drive.pairTerm (E.y i) (E.ρ i) (E.σ i) (E.ψ i) gA (η * Ψ) = 0 := by
    intro i hi
    have hzero : ∀ y ∈ tsupport (η * Ψ), E.ψ i y = (fun _ : X => (0 : ℝ)) y :=
      fun y hy => hηψ i hi y hy
    exact (Work.Drive.GreenRung.pairTerm_congr_weight (E.htgt i) (E.hσρ i) hzero).trans
      (Work.Kernel.psPairTerm_zero_weight (E.y i) (E.ρ i) (E.σ i) gA (η * Ψ))
  have h3 : Work.Drive.pairing E.y E.ρ E.σ E.ψ gA (η * Ψ)
      = Work.Drive.pairTerm (E.y E.ia) (E.ρ E.ia) (E.σ E.ia) (fun _ : X => (1 : ℝ))
          gA (η * Ψ) := by
    rw [Work.Drive.pairing, Finset.sum_eq_single E.ia]
    · have hw : ∀ y ∈ tsupport (η * Ψ),
          E.ψ E.ia y = (fun _ : X => (1 : ℝ)) y := by
        intro y hy
        have h1 : ∑ j, E.ψ j y = 1 := E.hsum y (hηK hy)
        rw [Finset.sum_eq_single E.ia (fun j _ hj => hηψ j hj y hy) (by simp)] at h1
        simpa using h1
      exact Work.Drive.GreenRung.pairTerm_congr_weight (E.htgt E.ia) (E.hσρ E.ia) hw
    · intro j _ hj
      exact hterminate j hj
    · intro hmem
      exact absurd (Finset.mem_univ E.ia) hmem
  -- (4) the chart-local pole term
  have h4 : Work.Drive.pairTerm (E.y E.ia) (E.ρ E.ia) (E.σ E.ia) (fun _ : X => (1 : ℝ))
        gA (η * Ψ)
      = 2 * Real.pi * Work.Drive.clampedPullback (E.y E.ia) (E.ρ E.ia) (η * Ψ) p :=
    Work.Kernel.psPairTerm_pole_of_logExpansion (x₀ := E.y E.ia) (hσ := hσnonneg) (hσρ := E.hσρ E.ia)
      (hrρ := hrρ) (htgt := E.htgt E.ia) (hχsupp := hηsupp) (hH := hH) (hueq := hueq)
      (hχc1 := hηc1a) (hχcs := hηcsa) (hχball := hηball) (hi1 := hpol1) (hi2 := hpol2)
      (hint := hpol3)
  -- (5) evaluation of the clamped pullback at the pole
  have h5 : Work.Drive.clampedPullback (E.y E.ia) (E.ρ E.ia) (η * Ψ) p = Ψ a := by
    rw [Work.Drive.clampedPullback_apply_of_mem (u := η * Ψ) hpmem, c.left_inv ha_src]
    rw [Pi.mul_apply, hηOne.self_of_nhds, Pi.one_apply, one_mul]
  exact (show Work.Drive.pairing E.y E.ρ E.σ E.ψ gA Ψ
      = 2 * Real.pi * Ψ a from by rw [hlin, hQ, add_zero, h3, h4, h5])

end Work.Kernel
