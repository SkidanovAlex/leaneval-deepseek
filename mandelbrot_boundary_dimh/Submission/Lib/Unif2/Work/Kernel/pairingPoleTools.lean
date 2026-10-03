import Mathlib
import Submission.Lib.Unif2.Work.Drive.pairing_leibniz
import Submission.Lib.Unif2.Work.Kernel.GreenCoverTools
import Submission.Lib.Unif2.RiemannSurface
import Submission.Lib.Unif2.Work.Drive.greenCoverExists
import Submission.Lib.Unif2.Work.Drive.lastMileCollar
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.localPoleExpansion_of_hasLogPoleOn
import Submission.Lib.Unif2.Work.Drive.polarPtBasics

/-!
# Interface bricks for `Work.Kernel.pairing_pole_of_comp`

The pole identity `(P)` (`Work.Kernel.pairing_pole_kernel_general`) demands a long list of interface
hypotheses about the test function `Ψ` and about the pole bump `η`.  This file collects the bricks
that discharge them for a test function of the shape `Ψ = w * Φ (gB)`, which is the shape used by the
reciprocity argument (`NOTES_greenSymmetryGeneral_energy_ENDGAME.md`, §2 and §7).

## Bricks

* `tsupport_clampedPullback_subset_closedBall` — the topological support of a clamped chart pullback
  is contained in the **closed** ball of the radius on which the function is supported.  This gives
  `hηball` of `(P)`: choose the pole bump `η` supported in a ball of radius `σ' < min (σ, r)`; the
  clamped support of `η * Ψ` then sits inside `closedBall p σ' ⊆ ball p r`.

* `chartDiff_of_harmonicOnX` — a function harmonic on `U` is differentiable in **every** preferred
  chart at every point of `U` (`Work.Drive.ChartDiff`).  This is obligation **(i)** of
  `pairing_pole_of_comp`: `hgAdiff` for `gA`, obtained from `IsGreenOn`'s harmonicity on `Ω ∖ {a}`
  (with `Ω ∖ {a,b} ⊆ Ω ∖ {a}`), via `Submission.HarmonicOnXAt_iff_chart` (chart independence of
  harmonicity) and the very definition `InnerProductSpace.HarmonicAt f z = (ContDiffAt ℝ 2 f z) ∧ …`.
  `ChartDiff.mono` restricts the set of points.
-/

open Set Metric Filter MeasureTheory
open scoped Manifold Topology

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
-- `haveI` is genuinely needed below: `IsManifold (modelWithCornersSelf ℝ ℂ) ⊤ X` is a type class
-- instance required by `Work.Drive.contDiffAt_comp_symm_of_contMDiff`.
set_option linter.style.haveILetI false

namespace Work.Kernel

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-- **Support bound for a clamped chart pullback.**  If `w` is supported in the chart ball of radius
`σ` around the base point, then the clamped pullback of `w` at the (larger) radius `ρ` is supported
in the closed ball of radius `σ`. -/
theorem tsupport_clampedPullback_subset_closedBall {x : X} {ρ σ : ℝ} {w : X → ℝ}
    (htgt : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target)
    (hsupp : tsupport w ⊆
      Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) σ) :
    tsupport (Work.Drive.clampedPullback x ρ w) ⊆
      Metric.closedBall ((chartAt ℂ x) x) σ := by
  refine closure_minimal (fun z hz => ?_) Metric.isClosed_closedBall
  rw [Function.mem_support] at hz
  have hzρ : z ∈ Metric.ball ((chartAt ℂ x) x) ρ := by
    by_contra h
    exact hz (Work.Drive.clampedPullback_apply_of_notMem h)
  have hwz : w ((chartAt ℂ x).symm z) ≠ 0 := by
    intro h0
    exact hz (by rw [Work.Drive.clampedPullback_apply_of_mem hzρ, h0])
  have hmem : (chartAt ℂ x).symm z ∈
      Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) σ :=
    hsupp (subset_tsupport w (Function.mem_support.mpr hwz))
  obtain ⟨-, hball⟩ := Submission.mem_chartBall.mp hmem
  rw [(chartAt ℂ x).right_inv (htgt hzρ)] at hball
  exact Metric.ball_subset_closedBall hball

section Harmonic

variable [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Chart differentiability of a harmonic function.**  If `u` is harmonic on `U`, then its chart
representative in any preferred chart is differentiable at the image of every point of `U` that lies
in the chart's source. -/
theorem chartDiff_of_harmonicOnX {u : X → ℝ} {U : Set X}
    (hu : Submission.HarmonicOnX u U) (y : X) :
    Work.Drive.ChartDiff (chartAt ℂ y) u U := by
  intro x hx
  obtain ⟨hxU, hxy⟩ := hx
  have h1 : InnerProductSpace.HarmonicAt (u ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) :=
    (Submission.HarmonicOnXAt_iff_chart (u := u) (x := x) (y := y) hxy).mp (hu x hxU)
  exact h1.1.differentiableAt (by norm_num)

/-- **Monotonicity of `Work.Drive.ChartDiff` in the set of points.** -/
theorem ChartDiff.mono {c : OpenPartialHomeomorph X ℂ} {u : X → ℝ} {U U' : Set X}
    (hUU' : U ⊆ U') (h : Work.Drive.ChartDiff c u U') : Work.Drive.ChartDiff c u U :=
  fun x hx => h x ⟨hUU' hx.1, hx.2⟩

/-- **Obligation (i) of `pairing_pole_of_comp`**: the chart differentiability of `gA` off the two
poles, from `Work.SimplyConnected.ABS.IsGreenOn`. -/
theorem chartDiff_of_isGreenOn {gA : X → ℝ} {Ω : Set X} {a b : X}
    (hgA : Work.SimplyConnected.ABS.IsGreenOn Ω a gA) (y : X) :
    Work.Drive.ChartDiff (chartAt ℂ y) gA (Ω \ ({a, b} : Set X)) :=
  ChartDiff.mono (U := Ω \ ({a, b} : Set X)) (U' := Ω \ {a})
    (fun _ hx => ⟨hx.1, fun ha => hx.2 (Or.inl ha)⟩)
    (chartDiff_of_harmonicOnX hgA.2.1 y)

/-- **Obligation (ii) of `pairing_pole_of_comp`**: the chart differentiability and the `C¹`
condition of the test function `Ψ = w * Φ (gB)`.

`w` is smooth and supported in `Ω`; `gB` is harmonic on `Ω \ {b}`; `Φ` is `C¹` and constant above the
level `M`, and `M ≤ gB` holds near `b`.  Then, in **every** preferred chart `chartAt ℂ y`, `Ψ` is
differentiable on `Ω` and its chart representative is `C¹` at the image of *every* point of the chart
source — the unrestricted form demanded by `Work.Kernel.pairing_pole_kernel_general`.

Three cases at `x ∈ (chartAt ℂ y).source`:

* `x ∉ Ω`: then `x ∉ tsupport w` (since `tsupport w ⊆ Ω`), so `Ψ` vanishes identically on a
  neighbourhood of `x`, and so does its chart representative near `(chartAt ℂ y) x`;
* `x = b`: near `b` one has `gB ≥ M`, hence `Φ (gB) = Φ M`, so `Ψ =ᶠ[𝓝 b] w * Φ M`, which is smooth;
* `x ∈ Ω`, `x ≠ b`: `Submission.HarmonicOnXAt_iff_chart` reads the harmonicity of `gB` in the chart
  `chartAt ℂ y` itself (no chart transfer is needed), and `InnerProductSpace.HarmonicAt` is *by
  definition* `ContDiffAt ℝ 2`; `w`'s chart representative is `C¹` by
  `Work.Drive.contDiffAt_comp_symm_of_contMDiff`, and the product is `C¹`. -/
theorem chartDiff_and_contDiffAt_mul_comp {Ω : Set X} {b : X} {w gB : X → ℝ} {Φ : ℝ → ℝ} {M : ℝ}
    (hwsupp : tsupport w ⊆ Ω)
    (hw : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    (hgB : Submission.HarmonicOnX gB (Ω \ {b}))
    (hgt : ∀ᶠ z in 𝓝 b, M ≤ gB z)
    (hΦ : ContDiff ℝ 1 Φ) (hΦev : ∀ x : ℝ, M ≤ x → Φ x = Φ M) (y : X) :
    (Work.Drive.ChartDiff (chartAt ℂ y) (fun z => w z * Φ (gB z)) Ω) ∧
      ∀ x ∈ (chartAt ℂ y).source,
        ContDiffAt ℝ 1 ((fun z => w z * Φ (gB z)) ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) := by
  haveI : IsManifold (modelWithCornersSelf ℝ ℂ) (⊤ : WithTop ℕ∞) X :=
    Work.SimplyConnected.ABS.isManifold_self_model_real_infty
  have hc1 : ∀ x ∈ (chartAt ℂ y).source,
      ContDiffAt ℝ 1 ((fun z => w z * Φ (gB z)) ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) := by
    intro x hx
    have hxtgt : (chartAt ℂ y) x ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hx
    by_cases hxΩ : x ∈ Ω
    · by_cases hxb : x = b
      · -- near `b`, `gB ≥ M`, so `Φ (gB) = Φ M`
        have hev : (fun z => w z * Φ (gB z)) =ᶠ[𝓝 b] (fun z => w z * Φ M) := by
          filter_upwards [hgt] with z hz
          rw [hΦev (gB z) hz]
        have hpt : (chartAt ℂ y).symm ((chartAt ℂ y) x) = x := (chartAt ℂ y).left_inv hx
        have hev_at : (fun z => w z * Φ (gB z))
            =ᶠ[𝓝 ((chartAt ℂ y).symm ((chartAt ℂ y) x))] (fun z => w z * Φ M) := by
          rw [hpt, hxb]
          exact hev
        have hev' : ((fun z => w z * Φ (gB z)) ∘ (chartAt ℂ y).symm)
            =ᶠ[𝓝 ((chartAt ℂ y) x)]
              ((fun z => w z * Φ M) ∘ (chartAt ℂ y).symm) := by
          filter_upwards [((chartAt ℂ y).continuousAt_symm hxtgt).eventually hev_at] with z hz
          simpa only [Function.comp_apply] using hz
        have hw' : ContDiffAt ℝ 1 ((fun z => w z * Φ M) ∘ (chartAt ℂ y).symm)
            ((chartAt ℂ y) x) := by
          have h1 : ContDiffAt ℝ 1 (w ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) :=
            Work.Drive.contDiffAt_comp_symm_of_contMDiff hw (chart_mem_atlas ℂ y) hx
          have h2 : ContDiffAt ℝ 1 (fun _ : ℂ => (Φ M : ℝ)) ((chartAt ℂ y) x) :=
            contDiffAt_const
          rw [show ((fun z => w z * Φ M) ∘ (chartAt ℂ y).symm)
              = (fun z : ℂ => w ((chartAt ℂ y).symm z) * Φ M) from rfl]
          exact h1.mul h2
        exact hw'.congr_of_eventuallyEq hev'
      · -- `x` is a smoothness point of `gB`
        have hx' : x ∈ Ω \ {b} := ⟨hxΩ, by simpa [Set.mem_singleton_iff] using hxb⟩
        have h1 : InnerProductSpace.HarmonicAt (gB ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) :=
          (Submission.HarmonicOnXAt_iff_chart (u := gB) (x := x) (y := y) hx).mp (hgB x hx')
        have hg1 : ContDiffAt ℝ 1 (gB ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) :=
          h1.1.of_le (by norm_num)
        have hw1 : ContDiffAt ℝ 1 (w ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) :=
          Work.Drive.contDiffAt_comp_symm_of_contMDiff hw (chart_mem_atlas ℂ y) hx
        have hphi : ContDiffAt ℝ 1 (Φ ∘ (gB ∘ (chartAt ℂ y).symm)) ((chartAt ℂ y) x) :=
          hΦ.contDiffAt.comp _ hg1
        rw [show ((fun z => w z * Φ (gB z)) ∘ (chartAt ℂ y).symm)
            = (fun z : ℂ => w ((chartAt ℂ y).symm z) * Φ (gB ((chartAt ℂ y).symm z))) from rfl]
        exact hw1.mul hphi
    · -- `Ψ` vanishes near `x`
      have hnot : x ∉ tsupport w := fun h => hxΩ (hwsupp h)
      have hVmem : ((tsupport w)ᶜ) ∈ 𝓝 x := (isClosed_tsupport w).isOpen_compl.mem_nhds hnot
      have hpre : ((chartAt ℂ y).symm ⁻¹' (tsupport w)ᶜ) ∈ 𝓝 ((chartAt ℂ y) x) := by
        have h1 : (tsupport w)ᶜ ∈ 𝓝 ((chartAt ℂ y).symm ((chartAt ℂ y) x)) := by
          rwa [(chartAt ℂ y).left_inv hx]
        exact ((chartAt ℂ y).continuousAt_symm hxtgt).preimage_mem_nhds h1
      have hev : ((fun _ : ℂ => (0 : ℝ)) =ᶠ[𝓝 ((chartAt ℂ y) x)]
          ((fun z => w z * Φ (gB z)) ∘ (chartAt ℂ y).symm)) := by
        filter_upwards [hpre] with z hz
        have hz0 : w ((chartAt ℂ y).symm z) = 0 := image_eq_zero_of_notMem_tsupport hz
        simp only [Function.comp_apply, hz0, zero_mul]
      exact (contDiffAt_const (x := (chartAt ℂ y) x) (c := (0 : ℝ))).congr_of_eventuallyEq
        hev.symm
  exact ⟨fun x hx => (hc1 x hx.2).differentiableAt (by norm_num), hc1⟩

/-- **Obligation (ii), second half: the pole bump times the test function.**  If `η` is smooth and
supported in `Ω`, and `Ψ` satisfies the conclusion of `chartDiff_and_contDiffAt_mul_comp` in every
preferred chart, then so does `η * Ψ` — which is what `hηdiff` and `hηc1` of
`Work.Kernel.pairing_pole_kernel_general` demand.

The product is smooth on the whole chart source for the same two reasons as before, now split at the
point in question:

* `x ∈ Ω`: both chart representatives are `C¹` at the image of `x` (`η`'s from `ContMDiff`, `Ψ`'s
  from the hypothesis, which holds for *every* point of the chart source) — and `ContDiffAt.mul` is
  applied after unfolding the composition;
* `x ∉ Ω`: then `x ∉ tsupport η` because `tsupport η ⊆ Ω`, so `η` — hence `η * Ψ` — vanishes on a
  neighbourhood of `x`, and so does its chart representative. -/
theorem chartDiff_and_contDiffAt_mul {Ω : Set X} {η Ψ : X → ℝ}
    (hη : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) η)
    (hηsupp : tsupport η ⊆ Ω)
    (hΨ : ∀ y : X, (Work.Drive.ChartDiff (chartAt ℂ y) Ψ Ω) ∧
      ∀ x ∈ (chartAt ℂ y).source,
        ContDiffAt ℝ 1 (Ψ ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x))
    (y : X) :
    (Work.Drive.ChartDiff (chartAt ℂ y) (η * Ψ) Ω) ∧
      ∀ x ∈ (chartAt ℂ y).source,
        ContDiffAt ℝ 1 ((η * Ψ) ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) := by
  haveI : IsManifold (modelWithCornersSelf ℝ ℂ) (⊤ : WithTop ℕ∞) X :=
    Work.SimplyConnected.ABS.isManifold_self_model_real_infty
  have hc1 : ∀ x ∈ (chartAt ℂ y).source,
      ContDiffAt ℝ 1 ((η * Ψ) ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) := by
    intro x hx
    by_cases hxΩ : x ∈ Ω
    · have h1 : ContDiffAt ℝ 1 (η ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) :=
        Work.Drive.contDiffAt_comp_symm_of_contMDiff hη (chart_mem_atlas ℂ y) hx
      have h2 : ContDiffAt ℝ 1 (Ψ ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) := (hΨ y).2 x hx
      rw [show ((η * Ψ) ∘ (chartAt ℂ y).symm)
          = (fun z : ℂ => η ((chartAt ℂ y).symm z) * Ψ ((chartAt ℂ y).symm z)) from rfl]
      exact h1.mul h2
    · have hnot : x ∉ tsupport η := fun h => hxΩ (hηsupp h)
      have hVmem : ((tsupport η)ᶜ) ∈ 𝓝 x := (isClosed_tsupport η).isOpen_compl.mem_nhds hnot
      have hxtgt : (chartAt ℂ y) x ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hx
      have hpre : ((chartAt ℂ y).symm ⁻¹' (tsupport η)ᶜ) ∈ 𝓝 ((chartAt ℂ y) x) := by
        have h1 : (tsupport η)ᶜ ∈ 𝓝 ((chartAt ℂ y).symm ((chartAt ℂ y) x)) := by
          rwa [(chartAt ℂ y).left_inv hx]
        exact ((chartAt ℂ y).continuousAt_symm hxtgt).preimage_mem_nhds h1
      have hev : ((fun _ : ℂ => (0 : ℝ)) =ᶠ[𝓝 ((chartAt ℂ y) x)]
          ((η * Ψ) ∘ (chartAt ℂ y).symm)) := by
        filter_upwards [hpre] with z hz
        have hz0 : η ((chartAt ℂ y).symm z) = 0 := image_eq_zero_of_notMem_tsupport hz
        simp only [Function.comp_apply, Pi.mul_apply, hz0, zero_mul]
      exact (contDiffAt_const (x := (chartAt ℂ y) x) (c := (0 : ℝ))).congr_of_eventuallyEq hev.symm
  exact ⟨fun x hx => (hc1 x hx.2).differentiableAt (by norm_num), hc1⟩

/-- **Obligations (ii) in one statement, in the exact shape (P) asks for**: the pole bump `η` times
`w * Φ (gB)`, again in every preferred chart. -/
theorem chartDiff_and_contDiffAt_mul_mul_comp {Ω : Set X} {b : X} {η w gB : X → ℝ} {Φ : ℝ → ℝ}
    {M : ℝ}
    (hη : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) η)
    (hηsupp : tsupport η ⊆ Ω)
    (hwsupp : tsupport w ⊆ Ω)
    (hw : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    (hgB : Submission.HarmonicOnX gB (Ω \ {b}))
    (hgt : ∀ᶠ z in 𝓝 b, M ≤ gB z)
    (hΦ : ContDiff ℝ 1 Φ) (hΦev : ∀ x : ℝ, M ≤ x → Φ x = Φ M) (y : X) :
    (Work.Drive.ChartDiff (chartAt ℂ y) (fun z => η z * (w z * Φ (gB z))) Ω) ∧
      ∀ x ∈ (chartAt ℂ y).source,
        ContDiffAt ℝ 1 ((fun z => η z * (w z * Φ (gB z))) ∘ (chartAt ℂ y).symm)
          ((chartAt ℂ y) x) :=
  chartDiff_and_contDiffAt_mul hη hηsupp
    (fun y => chartDiff_and_contDiffAt_mul_comp hwsupp hw hgB hgt hΦ hΦev y) y

end Harmonic

/-- **Obligation (iii) of `pairing_pole_of_comp`: the pole bump.**

For every `σ > 0` there is a smooth `η : X → ℝ` which is `1` on a whole neighbourhood of `a` and
whose support lies in the `σ`-ball of the chart at `a`.  This is `hηOne` together with the support
control that makes `hηball` true (`σ' < min (E.σ E.ia) r` gives
`tsupport (clampedPullback a ρ (η * Ψ)) ⊆ closedBall p σ' ⊆ ball p r` by
`Work.Kernel.tsupport_clampedPullback_subset_closedBall`).

The bump is `Work.Kernel.exists_contMDiff_eq_one_of_isClosed_subset_isOpen` applied to the closed
chart disc of radius `r` and the open chart ball of radius `σ`, where `r ≤ σ/2` is capped so that the
closed disc still lies inside the chart target (needed for its closedness via
`Submission.isClosed_chartClosedBall`). -/
theorem exists_poleBump {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [SecondCountableTopology X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {a : X} {σ : ℝ} (hσ : 0 < σ) :
    ∃ η : X → ℝ,
      ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ)
        ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧
      η =ᶠ[𝓝 a] 1 ∧
      tsupport η ⊆ Submission.chartBall (chartAt ℂ a) ((chartAt ℂ a) a) σ := by
  haveI : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ℂ X
  haveI : SigmaCompactSpace X := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : IsManifold (modelWithCornersSelf ℝ ℂ) (⊤ : WithTop ℕ∞) X :=
    Work.SimplyConnected.ABS.isManifold_self_model_real_infty
  classical
  -- a radius `ε` with the *closed* `ε`-ball inside the chart target
  have htarget : (chartAt ℂ a).target ∈ 𝓝 ((chartAt ℂ a) a) :=
    (chartAt ℂ a).open_target.mem_nhds ((chartAt ℂ a).map_source (mem_chart_source ℂ a))
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp htarget
  -- the radius of the closed disc, capped so that it stays inside the target and inside `σ`
  set r : ℝ := min (σ / 2) (ε / 2) with hrdef
  have hr : 0 < r := lt_min (by linarith) (by linarith)
  have hrσ : r < σ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrε : r < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hcltgt : Metric.closedBall ((chartAt ℂ a) a) r ⊆ (chartAt ℂ a).target :=
    (Metric.closedBall_subset_ball hrε).trans hεsub
  -- `a` lies in both the small ball and the closed disc
  have haball : a ∈ Submission.chartBall (chartAt ℂ a) ((chartAt ℂ a) a) r :=
    Submission.mem_chartBall.mpr ⟨mem_chart_source ℂ a, by
      rw [Metric.mem_ball, dist_self]; exact hr⟩
  -- the bump
  obtain ⟨η, hη, hηone, hηsupp⟩ :=
    Work.Kernel.exists_contMDiff_eq_one_of_isClosed_subset_isOpen
      (Submission.isClosed_chartClosedBall hcltgt) (Submission.chartBall_isOpen _ _ _)
      (fun x hx => Submission.mem_chartBall.mpr
        ⟨(Submission.mem_chartClosedBall.mp hx).1,
          Metric.closedBall_subset_ball hrσ (Submission.mem_chartClosedBall.mp hx).2⟩)
  refine ⟨η, hη, ?_, hηsupp⟩
  filter_upwards [(Submission.chartBall_isOpen (chartAt ℂ a) ((chartAt ℂ a) a) r).mem_nhds haball]
    with x hx
  exact hηone x (Submission.chartBall_subset_chartClosedBall _ _ _ hx)

/-- **`hηc1a` and `hηcsa` of `(P)`, generic form**: the clamped pullback of a function which is `C¹`
in the chart and supported in a smaller chart ball is `C¹` (globally on `ℂ`) with compact support.
This is `Work.Drive.GreenRung.contDiff_clampedPullback_hasCompactSupport` with the support hypothesis
stated through `Submission.chartBall` (which is definitionally `source ∩ preimage of the ball`, so
`Set.inter_subset_right` bridges the two).

NOTE: the underlying result lives in `Submission/Work/Drive/energyGreenRung.lean`, whose namespace is
being reorganised by another agent (§9).  If it moves again, either update the name below or copy the
proof in here. -/
theorem contDiff_and_hasCompactSupport_clampedPullback {x : X} {u : X → ℝ} {ρ ρ₀ : ℝ}
    (hρ : 0 < ρ) (hρ₀ : 0 ≤ ρ₀) (hρ₀ρ : ρ₀ < ρ)
    (htgt : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target)
    (hu : ∀ y ∈ (chartAt ℂ x).source,
      ContDiffAt ℝ 1 (u ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y))
    (hsupp : tsupport u ⊆ Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) ρ₀) :
    ContDiff ℝ 1 (Work.Drive.clampedPullback x ρ u) ∧
      HasCompactSupport (Work.Drive.clampedPullback x ρ u) :=
  Work.Drive.GreenRung.contDiff_clampedPullback_hasCompactSupport hρ hρ₀ hρ₀ρ htgt hu
    (hsupp.trans Set.inter_subset_right)

/-- **`hηc1a` and `hηcsa` of `(P)`, in the shape the pole identity uses**: the clamped pullback of
`η * Ψ`, where `η` is supported in the small chart ball of radius `ρ₀` (the bump of
`Work.Kernel.exists_poleBump`) and `η * Ψ` is `C¹` in the chart (obligation (ii),
`Work.Kernel.chartDiff_and_contDiffAt_mul`). -/
theorem contDiff_and_hasCompactSupport_clampedPullback_mul {x : X} {η Ψ : X → ℝ} {ρ ρ₀ : ℝ}
    (hρ : 0 < ρ) (hρ₀ : 0 ≤ ρ₀) (hρ₀ρ : ρ₀ < ρ)
    (htgt : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target)
    (hu : ∀ y ∈ (chartAt ℂ x).source,
      ContDiffAt ℝ 1 ((η * Ψ) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y))
    (hηsupp : tsupport η ⊆ Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) ρ₀) :
    ContDiff ℝ 1 (Work.Drive.clampedPullback x ρ (η * Ψ)) ∧
      HasCompactSupport (Work.Drive.clampedPullback x ρ (η * Ψ)) := by
  refine contDiff_and_hasCompactSupport_clampedPullback hρ hρ₀ hρ₀ρ htgt hu ?_
  refine (show tsupport (η * Ψ) ⊆ tsupport η from ?_).trans hηsupp
  refine closure_minimal ?_ (isClosed_tsupport η)
  intro w hw
  rw [Function.mem_support] at hw
  exact subset_tsupport η (Function.mem_support.mpr
    (fun h => hw (by rw [Pi.mul_apply, h, zero_mul])))

/-- **`hηsupp` of `(P)`**: the pole bump can be required to be supported in any prescribed set that
contains a chart ball around `a`. -/
theorem exists_poleBump_subset {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [SecondCountableTopology X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {a : X} {σ : ℝ} (hσ : 0 < σ) {K : Set X}
    (hK : Submission.chartBall (chartAt ℂ a) ((chartAt ℂ a) a) σ ⊆ K) :
    ∃ η : X → ℝ,
      ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ)
        ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧
      η =ᶠ[𝓝 a] 1 ∧ tsupport η ⊆ K := by
  obtain ⟨η, h1, h2, h3⟩ := exists_poleBump (a := a) (σ := σ) hσ
  exact ⟨η, h1, h2, h3.trans hK⟩

/-- **`hηψ` of `(P)`**: if the bump is supported in a chart ball around `a` on which *all* the other
partition weights vanish, then those weights vanish on `tsupport (η * Ψ)` — the test function is
supported in the bump, and the bump in that ball. -/
theorem tsupport_poleBump_mul_vanishes {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X}
    (E : Work.Kernel.GreenCover ι Ω K a b) {σ : ℝ} {η Ψ : X → ℝ}
    (hV : Submission.chartBall (chartAt ℂ a) ((chartAt ℂ a) a) σ ⊆
      {x : X | ∀ i : ι, i ≠ E.ia → E.ψ i x = 0})
    (hηsupp : tsupport η ⊆ Submission.chartBall (chartAt ℂ a) ((chartAt ℂ a) a) σ) :
    ∀ i : ι, i ≠ E.ia → ∀ x ∈ tsupport (η * Ψ), E.ψ i x = 0 := by
  have hsub : tsupport (η * Ψ) ⊆ tsupport η := by
    refine closure_minimal ?_ (isClosed_tsupport η)
    intro z hz
    rw [Function.mem_support] at hz
    exact subset_tsupport η (Function.mem_support.mpr
      (fun h => hz (by rw [Pi.mul_apply, h, zero_mul])))
  intro i hi x hx
  exact hV (hηsupp (hsub hx)) i hi

/-- **The gradient growth bound at a logarithmic pole.**  If `f` has the expansion
`f (c.symm z) = -log ‖z - p‖ + H z` on `ball p r`, its clamped support lies in `ball p r`, and
`‖∇H‖ ≤ M` there, then `‖∇(clampedPullback x ρ f)‖ ≤ C / ‖z - p‖` a.e. with `C := 1 + M * r`. -/
theorem gradient_clampedPullback_le_of_logExpansion {x : X} {ρ r : ℝ} {f : X → ℝ} {p : ℂ}
    {H : ℂ → ℝ} {M : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (hM : 0 ≤ M)
    (htgt : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target)
    (hsupppr : ∀ z ∈ tsupport (Work.Drive.clampedPullback x ρ f), z ∈ Metric.ball p r)
    (hH : ∀ z ∈ Metric.ball p r, DifferentiableAt ℝ H z)
    (hHb : ∀ z ∈ Metric.ball p r, ‖gradient H z‖ ≤ M)
    (hueq : ∀ z ∈ Metric.ball p r, z ≠ p →
      f ((chartAt ℂ x).symm z) = -Real.log ‖z - p‖ + H z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ z ∂(volume : Measure ℂ),
      ‖gradient (Work.Drive.clampedPullback x ρ f) z‖ ≤ C / ‖z - p‖ := by
  refine ⟨1 + M * r, by positivity, ?_⟩
  filter_upwards [compl_mem_ae_iff.mpr (Measure.addHaar_sphere volume ((chartAt ℂ x) x) ρ),
    compl_mem_ae_iff.mpr (measure_singleton p)] with z hzsph hzp
  have hzne : z ≠ p := Set.mem_compl_singleton_iff.mp hzp
  by_cases hzt : z ∈ tsupport (Work.Drive.clampedPullback x ρ f)
  · -- inside the topological support
    have hzr : z ∈ Metric.ball p r := hsupppr z hzt
    have hzclosed : z ∈ Metric.closedBall ((chartAt ℂ x) x) ρ := by
      refine closure_minimal (fun w hw => ?_) Metric.isClosed_closedBall hzt
      rw [Function.mem_support] at hw
      by_contra hwc
      refine hw (Work.Drive.clampedPullback_apply_of_notMem ?_)
      exact fun hb => hwc (Metric.ball_subset_closedBall hb)
    have hzball : z ∈ Metric.ball ((chartAt ℂ x) x) ρ := by
      rcases eq_or_ne (dist z ((chartAt ℂ x) x)) ρ with h | h
      · exact absurd (Metric.mem_sphere.mpr h) hzsph
      · exact Metric.mem_ball.mpr (lt_of_le_of_ne (Metric.mem_closedBall.mp hzclosed) h)
    have h1 : Work.Drive.clampedPullback x ρ f =ᶠ[𝓝 z] (f ∘ (chartAt ℂ x).symm) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hzball] with w hw
      rw [Work.Drive.clampedPullback_apply_of_mem hw]
      rfl
    have h2 : (f ∘ (chartAt ℂ x).symm) =ᶠ[𝓝 z]
        (fun y : ℂ => -Real.log ‖y - p‖ + H y) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hzr,
        isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hzne)] with w hw hwp
      exact hueq w hw (Set.mem_compl_singleton_iff.mp hwp)
    have hd1 : DifferentiableAt ℝ (fun y : ℂ => -Real.log ‖y - p‖) z :=
      (Work.Drive.hasFDerivAt_neg_log_norm_sub hzne).differentiableAt
    have hd2 : DifferentiableAt ℝ H z := hH z hzr
    have hgc : gradient (Work.Drive.clampedPullback x ρ f) z
        = gradient (fun y : ℂ => -Real.log ‖y - p‖ + H y) z := by
      rw [Filter.EventuallyEq.gradient_eq h1, Filter.EventuallyEq.gradient_eq h2]
    have h3 : gradient (fun y : ℂ => -Real.log ‖y - p‖ + H y) z
        = gradient (fun y : ℂ => -Real.log ‖y - p‖) z + gradient H z := by
      show (InnerProductSpace.toDual ℝ ℂ).symm
          (fderiv ℝ (fun y : ℂ => -Real.log ‖y - p‖ + H y) z) = _
      rw [show (fun y : ℂ => -Real.log ‖y - p‖ + H y)
          = (fun y : ℂ => -Real.log ‖y - p‖) + H from rfl]
      rw [fderiv_add hd1 hd2, map_add]
      rfl
    rw [hgc, h3, Work.Drive.gradient_neg_log_norm_sub hzne]
    have hnorm : ‖(-(‖z - p‖ ^ 2)⁻¹ : ℝ) • (z - p)‖ = (‖z - p‖)⁻¹ := by
      rw [norm_smul, norm_neg, Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
      rcases eq_or_ne ‖z - p‖ 0 with h | h
      · rw [h]; simp
      · rw [← inv_pow, pow_two, mul_assoc, inv_mul_cancel₀ h, mul_one]
    have hpos : 0 < ‖z - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzne)
    have hle : ‖z - p‖ ≤ r := by
      rw [← dist_eq_norm]; exact le_of_lt (Metric.mem_ball.mp hzr)
    calc ‖-(‖z - p‖ ^ 2)⁻¹ • (z - p) + gradient H z‖
        ≤ ‖-(‖z - p‖ ^ 2)⁻¹ • (z - p)‖ + ‖gradient H z‖ := norm_add_le _ _
      _ ≤ (‖z - p‖)⁻¹ + M := by
          rw [hnorm]
          linarith [hHb z hzr]
      _ ≤ (1 + M * r) / ‖z - p‖ := by
          rw [add_div, one_div]
          have h1' : M ≤ M * r / ‖z - p‖ := by
            rw [le_div_iff₀ hpos]
            exact mul_le_mul_of_nonneg_left hle hM
          linarith
  · -- outside the topological support the gradient vanishes
    have hzgrad : gradient (Work.Drive.clampedPullback x ρ f) z = 0 := by
      by_contra h
      exact hzt (Work.Analysis.Harmonic.tsupport_gradient_subset _
        (subset_tsupport _ (Function.mem_support.mpr h)))
    rw [hzgrad, norm_zero]
    exact div_nonneg (by nlinarith [mul_nonneg hM hr.le]) (norm_nonneg _)

/-- **Compact support of a clamped chart pullback** (`hWcs` of
`Work.Drive.pairIntegrable_of_gradient_bounds`): the clamping itself puts the support inside a closed
ball, so this needs **no** hypothesis on `W`.  It is the common prerequisite for every index of
`hηI`, `hDI`, `hQI2` and the pole integrability facts. -/
theorem hasCompactSupport_clampedPullback {x : X} {σ : ℝ} {W : X → ℝ} :
    HasCompactSupport (Work.Drive.clampedPullback x σ W) := by
  rw [hasCompactSupport_def]
  refine IsCompact.of_isClosed_subset (isCompact_closedBall ((chartAt ℂ x) x) σ)
    isClosed_closure (closure_minimal (fun z hz => ?_) Metric.isClosed_closedBall)
  rw [Function.mem_support] at hz
  refine Metric.ball_subset_closedBall ?_
  by_contra hzball
  exact hz (Work.Drive.clampedPullback_apply_of_notMem hzball)

/-- **Bounded gradient of a clamped chart pullback** — the companion of
`gradient_clampedPullback_le_of_logExpansion`, and the right tool off the pole chart (where the
`C / ‖z - p‖` form may involve a junk `p`).  It serves the `hχ` slot of
`Work.Drive.pairIntegrable_of_gradient_bounds` with `u := η * Ψ`, and every non-pole chart of
`hηI`/`hDI`/`hQI2`/`hpol1..3` with `u := gA`. -/
theorem gradient_clampedPullback_le_of_contDiffOn {x : X} {ρ s : ℝ} {u : X → ℝ}
    (hρ : 0 < ρ) (hs : 0 ≤ s) (hsρ : s < ρ)
    (htgt : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target)
    (hu : ∀ y ∈ (chartAt ℂ x).source,
      ContDiffAt ℝ 1 (u ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y))
    (hsupp : tsupport u ⊆ Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) s) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᵐ z ∂(volume : Measure ℂ),
      ‖gradient (Work.Drive.clampedPullback x ρ u) z‖ ≤ K := by
  obtain ⟨hc, -⟩ :=
    contDiff_and_hasCompactSupport_clampedPullback hρ hs hsρ htgt hu hsupp
  have hgcont : Continuous (gradient (Work.Drive.clampedPullback x ρ u)) := by
    have h1 : Continuous (fderiv ℝ (Work.Drive.clampedPullback x ρ u)) :=
      hc.continuous_fderiv (by norm_num)
    exact (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp h1
  have hsub : tsupport (Work.Drive.clampedPullback x ρ u) ⊆
      Metric.closedBall ((chartAt ℂ x) x) ρ := by
    refine closure_minimal (fun w hw => ?_) Metric.isClosed_closedBall
    rw [Function.mem_support] at hw
    refine Metric.ball_subset_closedBall ?_
    by_contra hwball
    exact hw (Work.Drive.clampedPullback_apply_of_notMem hwball)
  obtain ⟨K, hK⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_closedBall ((chartAt ℂ x) x) ρ) hgcont.continuousOn
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  filter_upwards with z
  by_cases hz : z ∈ Metric.closedBall ((chartAt ℂ x) x) ρ
  · exact le_trans (hK z hz) (le_max_left _ _)
  · have hz0 : gradient (Work.Drive.clampedPullback x ρ u) z = 0 := by
      by_contra h
      exact hz (hsub (Work.Analysis.Harmonic.tsupport_gradient_subset _
        (subset_tsupport _ (Function.mem_support.mpr h))))
    rw [hz0, norm_zero]
    exact le_max_right _ _

/-- **The pole index of the certificate block**: `PairIntegrable` when the first function of the
pairing has a logarithmic pole in the chart.  This is the wiring of the two already-proved tools: the
`C` of the first-gradient slot comes from `gradient_clampedPullback_le_of_logExpansion`, `hWc`/`hWcs`
are the weight slots and `hχ` the second-gradient slot of
`Work.Drive.pairIntegrable_of_gradient_bounds`. -/
theorem pairIntegrable_of_logExpansion {x : X} {ρ σ r : ℝ} {W f χ : X → ℝ} {p : ℂ} {H : ℂ → ℝ}
    {M K : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (hM : 0 ≤ M) (hσρ : σ < ρ)
    (hWc : Continuous (Work.Drive.clampedPullback x σ W))
    (hWcs : HasCompactSupport (Work.Drive.clampedPullback x σ W))
    (htgt : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target)
    (hsupppr : ∀ z ∈ tsupport (Work.Drive.clampedPullback x ρ f), z ∈ Metric.ball p r)
    (hH : ∀ z ∈ Metric.ball p r, DifferentiableAt ℝ H z)
    (hHb : ∀ z ∈ Metric.ball p r, ‖gradient H z‖ ≤ M)
    (hueq : ∀ z ∈ Metric.ball p r, z ≠ p →
      f ((chartAt ℂ x).symm z) = -Real.log ‖z - p‖ + H z)
    (hχ : ∀ᵐ z ∂(volume : Measure ℂ),
      ‖gradient (Work.Drive.clampedPullback x ρ χ) z‖ ≤ K)
    (hmeas : AEStronglyMeasurable (fun z : ℂ => inner (𝕜 := ℝ)
      (gradient (Work.Drive.clampedPullback x ρ f) z)
      (gradient (Work.Drive.clampedPullback x ρ χ) z)) volume) :
    Work.Drive.PairIntegrable x ρ σ W f χ := by
  obtain ⟨C, _, hC⟩ :=
    gradient_clampedPullback_le_of_logExpansion hρ hr hM htgt hsupppr hH hHb hueq
  exact Work.Drive.pairIntegrable_of_gradient_bounds hWc hWcs hC hχ hmeas

/-- **The support of any clamped chart pullback is in the closed `ρ`-ball** — hypothesis-free: the
clamping indicator does it, with no condition on `f`.  (This is the containment that was proved inline
inside `hasCompactSupport_clampedPullback` and `gradient_clampedPullback_le_of_contDiffOn`; it is worth
having once.) -/
theorem tsupport_clampedPullback_subset_closedBall_general {x : X} {ρ : ℝ} {f : X → ℝ} :
    tsupport (Work.Drive.clampedPullback x ρ f) ⊆ Metric.closedBall ((chartAt ℂ x) x) ρ := by
  refine closure_minimal (fun z hz => ?_) Metric.isClosed_closedBall
  rw [Function.mem_support] at hz
  refine Metric.ball_subset_closedBall ?_
  by_contra hzball
  exact hz (Work.Drive.clampedPullback_apply_of_notMem hzball)

/-- **Item 2 of the pole-index assembly**: the `hsupppr` hypothesis of
`Work.Kernel.pairIntegrable_of_logExpansion` for a chart **centred at the pole** (`hp`), as soon as the
expansion radius `r` exceeds the clamped radius `ρ`.  No support condition on `f` is needed, because
the clamped pullback is supported in the closed `ρ`-ball and `ρ < r`. -/
theorem tsupport_clampedPullback_subset_ball {x : X} {ρ r : ℝ} {f : X → ℝ} {p : ℂ}
    (hp : p = (chartAt ℂ x) x) (hρr : ρ < r) :
    ∀ z ∈ tsupport (Work.Drive.clampedPullback x ρ f), z ∈ Metric.ball p r := by
  intro z hz
  rw [hp]
  exact Metric.closedBall_subset_ball hρr (tsupport_clampedPullback_subset_closedBall_general hz)

/-- **Item 3 of the pole-index assembly**: the `hχ` hypothesis of
`Work.Kernel.pairIntegrable_of_logExpansion` for the test function `η * Ψ`.

The only inputs are obligation (ii)'s conclusion (`C¹` of the product's chart representative, e.g.
`Work.Kernel.chartDiff_and_contDiffAt_mul_mul_comp`) and the bump's support radius: the product is
supported in the bump, so it is supported in the small chart ball, and §22's tool then bounds the
gradient. -/
theorem exists_gradient_le_mul_of_contDiffAt {x : X} {ρ s : ℝ} {η u : X → ℝ}
    (hρ : 0 < ρ) (hs : 0 ≤ s) (hsρ : s < ρ)
    (htgt : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target)
    (hu : ∀ y ∈ (chartAt ℂ x).source,
      ContDiffAt ℝ 1 ((η * u) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y))
    (hηsupp : tsupport η ⊆ Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) s) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᵐ z ∂(volume : Measure ℂ),
      ‖gradient (Work.Drive.clampedPullback x ρ (η * u)) z‖ ≤ K := by
  refine gradient_clampedPullback_le_of_contDiffOn hρ hs hsρ htgt hu ?_
  refine (show tsupport (η * u) ⊆ tsupport η from ?_).trans hηsupp
  refine closure_minimal ?_ (isClosed_tsupport η)
  intro w hw
  rw [Function.mem_support] at hw
  exact subset_tsupport η (Function.mem_support.mpr
    (fun h => hw (by rw [Pi.mul_apply, h, zero_mul])))

section LogExpansion

variable [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Item 4 of the pole-index assembly: the logarithmic expansion of `gA` in the pole chart.**

This converts `Work.SimplyConnected.ABS.localPoleExpansion_of_hasLogPoleOn` — whose conclusion is
*conditional on `x ∈ Ω`* — into the `z`-form that `Work.Kernel.pairIntegrable_of_logExpansion`
consumes.  The radius is shrunk so that the chart ball lies inside the chart target and maps into `Ω`;
after that the membership condition drops out of `OpenPartialHomeomorph.right_inv`, and no case split
on `z = p` is needed. -/
theorem exists_logExpansion_poleChart {x : X} {Ω : Set X} {f : X → ℝ}
    (hΩo : IsOpen Ω) (hxΩ : x ∈ Ω) (hf : Submission.HarmonicOnX f (Ω \ {x}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn Ω x f) :
    ∃ r : ℝ, 0 < r ∧ ∃ H : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd H (Metric.ball ((chartAt ℂ x) x) r) ∧
      ∀ z ∈ Metric.ball ((chartAt ℂ x) x) r, z ≠ (chartAt ℂ x) x →
        f ((chartAt ℂ x).symm z) = -Real.log ‖z - (chartAt ℂ x) x‖ + H z := by
  obtain ⟨ρ, hρ, H, hH, hexp⟩ :=
    Work.SimplyConnected.ABS.localPoleExpansion_of_hasLogPoleOn (U := Ω)
      (hΩo.mem_nhds hxΩ) hf hpole
  have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hxtgt : (chartAt ℂ x) x ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hxsrc
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem
    ((chartAt ℂ x).open_target.mem_nhds hxtgt)
    (((chartAt ℂ x).continuousAt_symm hxtgt).preimage_mem_nhds
      (hΩo.mem_nhds (by rw [(chartAt ℂ x).left_inv hxsrc]; exact hxΩ))))
  refine ⟨min ρ ε, lt_min hρ hε, H, ?_, ?_⟩
  · exact hH.mono (Metric.ball_subset_ball (min_le_left _ _))
  · intro z hz hzp
    have hzρ : z ∈ Metric.ball ((chartAt ℂ x) x) ρ := Metric.ball_subset_ball (min_le_left _ _) hz
    have hzε : z ∈ Metric.ball ((chartAt ℂ x) x) ε := Metric.ball_subset_ball (min_le_right _ _) hz
    have hztgt : z ∈ (chartAt ℂ x).target := (hεsub hzε).1
    have hzU : (chartAt ℂ x).symm z ∈ Ω := (hεsub hzε).2
    have hsrc : (chartAt ℂ x).symm z ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hztgt
    have hri : (chartAt ℂ x) ((chartAt ℂ x).symm z) = z := (chartAt ℂ x).right_inv hztgt
    have hmem : (chartAt ℂ x).symm z ∈
        Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) ρ :=
      ⟨hsrc, by
        show (chartAt ℂ x) ((chartAt ℂ x).symm z) ∈ Metric.ball ((chartAt ℂ x) x) ρ
        rw [hri]
        exact hzρ⟩
    have hne : (chartAt ℂ x).symm z ≠ x := fun h =>
      hzp (hri.symm.trans (congrArg (chartAt ℂ x) h))
    have := hexp ((chartAt ℂ x).symm z) hzU hmem hne
    rw [hri] at this
    exact this

end LogExpansion

end Work.Kernel

end
