import Mathlib
import Submission.Work.SimplyConnected.ABS.Defs
import Submission.Work.Drive.greenSymmetryCutoff
import Submission.Work.Kernel.pairing_pole_smooth
import Submission.Work.Kernel.exists_greenCover_centred
import Submission.Work.Drive.poleIdentityInterface
import Submission.Work.Drive.greenPoleValue
import Submission.Work.Kernel.LevelDecay
import Submission.Work.Drive.pairing_leibniz
import Submission.Work.Drive.lastMileTools
import Submission.Work.Drive.energyGreenRung
import Submission.Work.Kernel.pairingPoleTools
import Submission.Work.Drive.greenSymmetryCutoffTools
import Submission.Work.Kernel.pairing_pole_singular_a
import Submission.Work.Kernel.greenCoverPairingAux

/-!
# The two-cutoff proof of the symmetry of the Green function — assembly

This file assembles the route of `NOTES_greenSymmetryAtPoles_cutoff_route.md` under fresh names, so
that the target `Work.Drive.greenSymmetryRegion` can rest on it.
-/

open MeasureTheory Set Metric Filter
open scoped Manifold Topology Gradient ContDiff

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-! ## 0. Elementary facts -/

theorem deriv_stepCutoff_nonneg {σ : ℝ} (hσ : 0 < σ) (t : ℝ) : 0 ≤ deriv (stepCutoff σ) t :=
  Monotone.deriv_nonneg (x := t) (monotone_stepCutoff hσ)

/-- **The support of the logarithmic bump lies in the closed chart ball**, provided the closed ball
lies in the chart target (so that no junk value of `chartAt ℂ x₀` can be met). -/
theorem tsupport_logBump_subset_chartClosedBall {x₀ : X} {h : ℝ → ℝ} {τ : ℝ}
    (htgt : Metric.closedBall ((chartAt ℂ x₀) x₀) τ ⊆ (chartAt ℂ x₀).target) :
    tsupport (logBump x₀ h τ) ⊆ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) τ := by
  refine Subset.trans (closure_mono ?_)
    (Submission.closure_chartBall_subset_chartClosedBall htgt)
  intro y hy
  by_contra hcon
  exact hy (logBump_eq_zero_of_notMem hcon)

/-- Inside its chart ball the logarithmic bump is the chart formula. -/
theorem logBump_apply_of_mem {x₀ : X} {h : ℝ → ℝ} {τ : ℝ} {x : X}
    (hx : x ∈ Submission.chartBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) τ) :
    logBump x₀ h τ x = h ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖ *
      Real.log ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖ := by
  classical
  rw [logBump]; exact if_pos hx

/-! ## 1. A Green function with a prescribed pole value, vanishing off `Ω` -/

/-- Harmonicity at a point is local. -/
private theorem harmonicOnXAt_congr_nhds' {u v : X → ℝ} {x : X}
    (h : Submission.HarmonicOnXAt u x) (huv : u =ᶠ[𝓝 x] v) : Submission.HarmonicOnXAt v x := by
  rw [Submission.HarmonicOnXAt] at h ⊢
  have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hpre : (fun z : ℂ => u ((chartAt ℂ x).symm z)) =ᶠ[𝓝 ((chartAt ℂ x) x)]
      (fun z : ℂ => v ((chartAt ℂ x).symm z)) := by
    have h1 : Filter.Tendsto (chartAt ℂ x).symm (𝓝 ((chartAt ℂ x) x)) (𝓝 x) := by
      have h2 := ((chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source hxsrc)).tendsto
      rwa [(chartAt ℂ x).left_inv hxsrc] at h2
    exact h1.eventually huv
  exact (InnerProductSpace.harmonicAt_congr_nhds hpre).mp h

/-- **`IsGreenOn` is insensitive to the values at the pole and off `Ω`.** -/
theorem isGreenOn_offΩ_update {Ω : Set X} (hΩo : IsOpen Ω) {b : X} {gB gB' : X → ℝ}
    (hgB : Work.SimplyConnected.ABS.IsGreenOn Ω b gB)
    (hΩ : ∀ x ∈ Ω, x ≠ b → gB' x = gB x) (hout : ∀ x ∉ Ω, gB' x = 0) (hb : 0 < gB' b) :
    Work.SimplyConnected.ABS.IsGreenOn Ω b gB' := by
  classical
  obtain ⟨hpos, hharm, hdecay, hpole⟩ := hgB
  have hbΩ : b ∈ Ω := by
    by_contra hbnot
    have h0 := hout b hbnot
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hxΩ hxne
    rw [hΩ x hxΩ hxne]
    exact hpos x hxΩ hxne
  · intro x hx
    obtain ⟨hxΩ, hxne⟩ := (Set.mem_sdiff x).mp hx
    have hxne' : x ≠ b := by simpa using hxne
    have hxmem : x ∈ Ω \ {b} := (Set.mem_sdiff x).mpr ⟨hxΩ, by simpa using hxne'⟩
    refine harmonicOnXAt_congr_nhds' (hharm x hxmem) ?_
    filter_upwards [IsOpen.mem_nhds (hΩo.sdiff isClosed_singleton) hxmem] with y hy
    exact (hΩ y hy.1 (by simpa using hy.2)).symm
  · intro ε hε
    obtain ⟨K, hKc, hKΩ, hK⟩ := hdecay ε hε
    refine ⟨K ∪ {b}, hKc.union isCompact_singleton, Set.union_subset hKΩ ?_, ?_⟩
    · exact Set.singleton_subset_iff.mpr hbΩ
    · intro x hxΩ hxK
      have hxK' : x ∉ K := fun h => hxK (Set.mem_union_left _ h)
      have hxb : x ≠ b := by
        intro h
        exact hxK (h ▸ Set.mem_union_right K (by simp))
      rw [hΩ x hxΩ hxb]
      exact hK x hxΩ hxK'
  · obtain ⟨C, V, hV, hCV⟩ := hpole
    refine ⟨C, V, hV, fun x hxV hxΩ hxne => ?_⟩
    rw [hΩ x hxΩ hxne]
    exact hCV x hxV hxΩ hxne

/-- **Admissible modification of a Green function.**  A Green function of the open set `Ω` with pole
`p` can be replaced by one which agrees with it on `Ω \ {p}`, vanishes outside `Ω`, and takes any
prescribed value at `p`. -/
theorem exists_isGreenOn_eq_off_pole {Ω : Set X} (hΩo : IsOpen Ω) {p : X} (hp : p ∈ Ω)
    {g : X → ℝ} (hg : Work.SimplyConnected.ABS.IsGreenOn Ω p g) (M : ℝ) :
    ∃ g' : X → ℝ, Work.SimplyConnected.ABS.IsGreenOn Ω p g' ∧ g' p = M ∧
      (∀ x ∈ Ω, x ≠ p → g' x = g x) ∧ (∀ x ∉ Ω, g' x = 0) := by
  classical
  haveI : DecidableEq X := Classical.decEq X
  set G : X → ℝ := fun x => if x = p then |M| + 1 else if x ∈ Ω then g x else 0 with hG
  have hnotMeq : ∀ {x : X}, x ∉ Ω → x ≠ p := fun {x} hx hcon => hx (by rw [hcon]; exact hp)
  have hGon : Work.SimplyConnected.ABS.IsGreenOn Ω p G := by
    refine isGreenOn_offΩ_update hΩo hg ?_ ?_ ?_
    · intro x hx hxp
      rw [hG]; simp only [if_neg hxp, if_pos hx]
    · intro x hx
      rw [hG]; simp only [if_neg (hnotMeq hx), if_neg hx]
    · rw [hG]
      show 0 < (if p = p then |M| + 1 else (if p ∈ Ω then g p else 0))
      rw [if_pos rfl]; positivity
  refine ⟨Function.update G p M, Work.SimplyConnected.ABS.IsGreenOn.update hp M hGon,
    Function.update_self p M G, ?_, ?_⟩
  · intro x hx hxp
    rw [Function.update_of_ne hxp, hG]; simp only [if_neg hxp, if_pos hx]
  · intro x hx
    have hxp : x ≠ p := hnotMeq hx
    rw [Function.update_of_ne hxp, hG]
    simp only [if_neg hxp, if_neg hx]

/-! ## 5. Smoothness of the logarithmic bump away from its pole -/

/-- If the chart representative of `g` has the logarithmic expansion `-log‖· - c b‖ + H` off the
centre, then setting the value of `g` at `b` to `H (c b)` makes the expansion hold *at the centre*
too (where `-log 0 = 0` in Mathlib). -/
theorem expansion_of_update [DecidableEq X] {g : X → ℝ} {b : X} {R : ℝ} {H : ℂ → ℝ}
    (hexp : ∀ z ∈ Metric.ball ((chartAt ℂ b) b) R, z ≠ (chartAt ℂ b) b →
      g ((chartAt ℂ b).symm z) = -Real.log ‖z - (chartAt ℂ b) b‖ + H z)
    (htgt : Metric.ball ((chartAt ℂ b) b) R ⊆ (chartAt ℂ b).target) :
    ∀ z ∈ Metric.ball ((chartAt ℂ b) b) R,
      Function.update g b (H ((chartAt ℂ b) b)) ((chartAt ℂ b).symm z)
        = -Real.log ‖z - (chartAt ℂ b) b‖ + H z := by
  classical
  intro z hz
  by_cases hz0 : z = (chartAt ℂ b) b
  · subst hz0
    have hsymm_b : (↑(chartAt ℂ b).symm : ℂ → X) ((chartAt ℂ b) b) = b :=
      (chartAt ℂ b).left_inv (mem_chart_source ℂ b)
    rw [hsymm_b, Function.update_self]
    simp
  · have hsymm : (chartAt ℂ b).symm z ≠ b := by
      intro hcon
      have h1 : (chartAt ℂ b) ((chartAt ℂ b).symm z) = (chartAt ℂ b) b := by rw [hcon]
      rw [(chartAt ℂ b).right_inv (htgt hz)] at h1
      exact hz0 h1
    simp only [Function.update_of_ne (a := (↑(chartAt ℂ b).symm : ℂ → X) z) (a' := b) hsymm]
    exact hexp z hz hz0

/-- The radial function `w ↦ h ‖w - q‖ * log ‖w - q‖` is `C¹` away from `q`. -/
theorem contDiffAt_radial_mul_log {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h) {q z : ℂ} (hz : z ≠ q) :
    ContDiffAt ℝ 1 (fun w : ℂ => h ‖w - q‖ * Real.log ‖w - q‖) z := by
  have h1 : ContDiffAt ℝ 1 (fun w : ℂ => ‖w - q‖) z :=
    ContDiffAt.norm ℝ (contDiffAt_id.sub contDiffAt_const) (sub_ne_zero.mpr hz)
  have h2 : ContDiffAt ℝ 1 (fun w : ℂ => h ‖w - q‖) z := hh.contDiffAt.comp z h1
  have h3 : ContDiffAt ℝ 1 (fun w : ℂ => Real.log ‖w - q‖) z := by
    refine h1.log ?_
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz)
  exact h2.mul h3

/-- The radial function `w ↦ h ‖w - q‖ * log ‖w - q‖`, clamped (as an indicator) to the ball of
radius `τ` around `q`, is `C¹` at every point different from `q`, provided `h` is `C¹`, vanishes for
`t ≥ 2R`, and `2R < τ` (so that the clamp at the sphere `‖w - q‖ = τ` happens where `h` already
vanishes). -/
theorem contDiffAt_clamped_radial_mul_log {h : ℝ → ℝ} {q : ℂ} {R τ : ℝ}
    (hh : ContDiff ℝ 1 h) (hR : 0 < R) (hRτ : 2 * R < τ)
    (hh0 : ∀ t : ℝ, 2 * R ≤ t → h t = 0) {z : ℂ} (hz : z ≠ q) :
    ContDiffAt ℝ 1
      ((Metric.ball q τ).indicator (fun w : ℂ => h ‖w - q‖ * Real.log ‖w - q‖)) z := by
  have hglob : (Metric.ball q τ).indicator (fun w : ℂ => h ‖w - q‖ * Real.log ‖w - q‖)
      = fun w : ℂ => h ‖w - q‖ * Real.log ‖w - q‖ := by
    funext w
    by_cases hw : w ∈ Metric.ball q τ
    · rw [Set.indicator_of_mem hw]
    · rw [Set.indicator_of_notMem hw]
      rw [Metric.mem_ball, not_lt, dist_eq_norm] at hw
      rw [hh0 _ (le_trans (le_of_lt hRτ) hw), zero_mul]
  rw [hglob]
  exact contDiffAt_radial_mul_log hh hz

/-- **The chart representative of the logarithmic bump is `C¹` away from its pole.** -/
theorem logBump_contDiffAt_chart [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {x₀ : X} {h : ℝ → ℝ} {R τ : ℝ}
    (hh : ContDiff ℝ 1 h) (hR : 0 < R) (hRτ : 2 * R < τ)
    (hh0 : ∀ t : ℝ, 2 * R ≤ t → h t = 0)
    (htgt : Metric.closedBall ((chartAt ℂ x₀) x₀) (2 * R) ⊆ (chartAt ℂ x₀).target)
    {y : X} {x : X} (hx : x ∈ (chartAt ℂ y).source) (hxne : x ≠ x₀) :
    ContDiffAt ℝ 1 (logBump x₀ h τ ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) := by
  classical
  have hsymm : (chartAt ℂ y).symm ((chartAt ℂ y) x) = x := (chartAt ℂ y).left_inv hx
  have hxtgt : (chartAt ℂ y) x ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hx
  by_cases hxsrc : x ∈ (chartAt ℂ x₀).source
  · have hsrc' : (chartAt ℂ y).symm ((chartAt ℂ y) x) ∈ (chartAt ℂ x₀).source := by
      rw [hsymm]; exact hxsrc
    have hφan : AnalyticAt ℂ (fun w : ℂ => (chartAt ℂ x₀) ((chartAt ℂ y).symm w))
        ((chartAt ℂ y) x) :=
      Submission.analyticAt_transition_of_mem_atlas (chart_mem_atlas ℂ x₀) (chart_mem_atlas ℂ y)
        ((chartAt ℂ y) x) hxtgt hsrc'
    have hφne : (chartAt ℂ x₀) ((chartAt ℂ y).symm ((chartAt ℂ y) x)) ≠ (chartAt ℂ x₀) x₀ := by
      rw [hsymm]
      exact fun hcon => hxne ((chartAt ℂ x₀).injOn hxsrc (mem_chart_source ℂ x₀) hcon)
    have hev : (logBump x₀ h τ ∘ (chartAt ℂ y).symm) =ᶠ[𝓝 ((chartAt ℂ y) x)]
        (fun w : ℂ => h ‖(chartAt ℂ x₀) ((chartAt ℂ y).symm w) - (chartAt ℂ x₀) x₀‖ *
          Real.log ‖(chartAt ℂ x₀) ((chartAt ℂ y).symm w) - (chartAt ℂ x₀) x₀‖) := by
      have hsrcnear : ∀ᶠ w in 𝓝 ((chartAt ℂ y) x),
          (chartAt ℂ y).symm w ∈ (chartAt ℂ x₀).source :=
        ((chartAt ℂ y).continuousAt_symm hxtgt).eventually
          ((chartAt ℂ x₀).open_source.mem_nhds hsrc')
      filter_upwards [hsrcnear] with w hw
      have hmem : (chartAt ℂ y).symm w ∈
            Submission.chartBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) τ
          ↔ (chartAt ℂ x₀) ((chartAt ℂ y).symm w) ∈ Metric.ball ((chartAt ℂ x₀) x₀) τ :=
        ⟨fun h => h.2, fun h => ⟨hw, h⟩⟩
      rw [Function.comp_apply, logBump]
      by_cases hb : (chartAt ℂ x₀) ((chartAt ℂ y).symm w) ∈ Metric.ball ((chartAt ℂ x₀) x₀) τ
      · rw [if_pos (hmem.mpr hb)]
      · rw [if_neg (fun h => hb (hmem.mp h))]
        have h2R : 2 * R ≤ ‖(chartAt ℂ x₀) ((chartAt ℂ y).symm w) - (chartAt ℂ x₀) x₀‖ := by
          rw [Metric.mem_ball, not_lt, dist_eq_norm] at hb
          exact le_trans (le_of_lt hRτ) hb
        rw [hh0 _ h2R, zero_mul]
    have hcd : ContDiffAt ℝ 1 (fun w : ℂ => h ‖(chartAt ℂ x₀) ((chartAt ℂ y).symm w)
        - (chartAt ℂ x₀) x₀‖ * Real.log ‖(chartAt ℂ x₀) ((chartAt ℂ y).symm w)
        - (chartAt ℂ x₀) x₀‖) ((chartAt ℂ y) x) :=
      (contDiffAt_radial_mul_log hh (q := (chartAt ℂ x₀) x₀) hφne).comp ((chartAt ℂ y) x)
        (hφan.contDiffAt.restrict_scalars ℝ)
    exact hcd.congr_of_eventuallyEq hev
  · have hnotmem : x ∉ (chartAt ℂ x₀).symm '' Metric.closedBall ((chartAt ℂ x₀) x₀) (2 * R) := by
      rintro ⟨z, hz, hzx⟩
      have hztgt : z ∈ (chartAt ℂ x₀).target := htgt hz
      exact hxsrc (hzx ▸ (chartAt ℂ x₀).map_target hztgt)
    have hclosed : IsCompact
        ((chartAt ℂ x₀).symm '' Metric.closedBall ((chartAt ℂ x₀) x₀) (2 * R)) :=
      (isCompact_closedBall _ _).image_of_continuousOn
        ((chartAt ℂ x₀).continuousOn_symm.mono htgt)
    have hnm' : (chartAt ℂ y).symm ((chartAt ℂ y) x) ∉
        (chartAt ℂ x₀).symm '' Metric.closedBall ((chartAt ℂ x₀) x₀) (2 * R) := by
      rw [hsymm]; exact hnotmem
    have hcompl : ∀ᶠ w in 𝓝 ((chartAt ℂ y) x), (chartAt ℂ y).symm w ∉
        (chartAt ℂ x₀).symm '' Metric.closedBall ((chartAt ℂ x₀) x₀) (2 * R) :=
      ((chartAt ℂ y).continuousAt_symm hxtgt).eventually
        (hclosed.isClosed.isOpen_compl.mem_nhds hnm')
    have hev : (logBump x₀ h τ ∘ (chartAt ℂ y).symm) =ᶠ[𝓝 ((chartAt ℂ y) x)]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [hcompl] with w hw
      rw [Function.comp_apply]
      by_cases hmem : (chartAt ℂ y).symm w ∈
          Submission.chartBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) τ
      · rw [logBump, if_pos hmem]
        have h2R : 2 * R ≤ ‖(chartAt ℂ x₀) ((chartAt ℂ y).symm w) - (chartAt ℂ x₀) x₀‖ := by
          by_contra hcon
          rw [not_le] at hcon
          refine hw ⟨(chartAt ℂ x₀) ((chartAt ℂ y).symm w), ?_, (chartAt ℂ x₀).left_inv hmem.1⟩
          rw [Metric.mem_closedBall, dist_eq_norm]
          exact le_of_lt hcon
        rw [hh0 _ h2R, zero_mul]
      · rw [logBump, if_neg hmem]
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev


/-! ## 6. The two-cutoff assembly -/

open scoped BigOperators

variable [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The logarithmic pole of a Green function is cancelled by the logarithmic bump.**  If the
chart representative of `g` has the expansion `-log‖· - c b‖ + H` on the ball of radius `r` around
`c b`, then `g + logBump b h τ` agrees with the harmonic part `H ∘ (chart b)` in a neighbourhood of
`b` (as a function, *including* at `b`, where `Real.log 0 = 0` and both sides equal `H (c b)`). -/
theorem green_add_logBump_eventuallyEq {b : X} {g : X → ℝ} {H : ℂ → ℝ} {r : ℝ} (hr : 0 < r)
    (hexp : ∀ z ∈ Metric.ball ((chartAt ℂ b) b) r,
      g ((chartAt ℂ b).symm z) = -Real.log ‖z - (chartAt ℂ b) b‖ + H z)
    {h : ℝ → ℝ} {R τ : ℝ} (hR : 0 < R) (hRτ : R < τ)
    (hh1 : ∀ t ∈ Set.Icc (0 : ℝ) R, h t = 1) :
    (fun x => g x + logBump b h τ x) =ᶠ[𝓝 b] (fun x => H ((chartAt ℂ b) x)) := by
  classical
  set φ : X → ℝ := fun x => ‖(chartAt ℂ b) x - (chartAt ℂ b) b‖ with hφdef
  have hφcont : ContinuousAt φ b := by
    rw [hφdef]
    exact ((chartAt ℂ b).continuousAt (mem_chart_source ℂ b)).sub continuousAt_const |>.norm
  have hφb : φ b = 0 := by
    rw [hφdef]
    simp
  have hsrc : (chartAt ℂ b).source ∈ 𝓝 b :=
    (chartAt ℂ b).open_source.mem_nhds (mem_chart_source ℂ b)
  have h1 : ∀ᶠ x in 𝓝 b, φ x < min r τ := by
    have hlt : φ b < min r τ := by rw [hφb]; exact lt_min hr (by linarith)
    exact hφcont.eventually (isOpen_Iio.mem_nhds hlt)
  have h2 : ∀ᶠ x in 𝓝 b, φ x < R := by
    have hlt : φ b < R := by rw [hφb]; exact hR
    exact hφcont.eventually (isOpen_Iio.mem_nhds hlt)
  filter_upwards [h1, h2, hsrc] with x hx1 hx2 hxsrc
  have hxball : x ∈ Submission.chartBall (chartAt ℂ b) ((chartAt ℂ b) b) τ := by
    refine ⟨hxsrc, ?_⟩
    show (chartAt ℂ b) x ∈ Metric.ball ((chartAt ℂ b) b) τ
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_lt_of_le hx1 (min_le_right _ _)
  rw [logBump, if_pos hxball]
  have hφxr : ‖(chartAt ℂ b) x - (chartAt ℂ b) b‖ < r := lt_of_lt_of_le hx1 (min_le_left _ _)
  have hφxR : ‖(chartAt ℂ b) x - (chartAt ℂ b) b‖ < R := by
    rw [hφdef] at hx2; exact hx2
  have hs : (chartAt ℂ b).symm ((chartAt ℂ b) x) = x := (chartAt ℂ b).left_inv hxsrc
  have hgx : g x = -Real.log ‖(chartAt ℂ b) x - (chartAt ℂ b) b‖ + H ((chartAt ℂ b) x) := by
    have h := hexp ((chartAt ℂ b) x) (by rw [Metric.mem_ball, dist_eq_norm]; exact hφxr)
    rwa [hs] at h
  rw [hgx, hh1 _ (Set.mem_Icc.mpr ⟨norm_nonneg _, le_of_lt hφxR⟩)]
  ring

/-- **A `C¹`-function which agrees with a `C¹`-function near a point has `C¹` chart
representatives there.** -/
theorem contDiffAt_chart_of_eventuallyEq_at {Ψ Φ : X → ℝ} {p : X}
    (hΦ : ∀ y : X, ContDiffAt ℝ 1 (Φ ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) p))
    (hΨ : ∀ y : X, ∀ x ∈ (chartAt ℂ y).source, x ≠ p →
      ContDiffAt ℝ 1 (Ψ ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x))
    (hev : Ψ =ᶠ[𝓝 p] Φ) (y : X) :
    ∀ x ∈ (chartAt ℂ y).source,
      ContDiffAt ℝ 1 (Ψ ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) := by
  intro x hx
  by_cases hxp : x = p
  · subst hxp
    have hxtgt : (chartAt ℂ y) x ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hx
    have hsymm : (chartAt ℂ y).symm ((chartAt ℂ y) x) = x := (chartAt ℂ y).left_inv hx
    have hcont : Filter.Tendsto (↑(chartAt ℂ y).symm : ℂ → X) (𝓝 ((chartAt ℂ y) x)) (𝓝 x) := by
      have h1 := ((chartAt ℂ y).continuousAt_symm hxtgt).tendsto
      rwa [hsymm] at h1
    exact (hΦ y).congr_of_eventuallyEq (hcont.eventually hev)
  · exact hΨ y x hx hxp



/-! ## 8. Generic certificate tools (for the final assembly) -/

/-- The `pairTerm` only depends on the weight up to almost-everywhere equality of its clamped
pullback. -/
theorem pairTerm_congr_weight_ae {x : X} {ρ σ : ℝ} {W W' f χ : X → ℝ}
    (h : clampedPullback x σ W =ᵐ[volume] clampedPullback x σ W') :
    pairTerm x ρ σ W f χ = pairTerm x ρ σ W' f χ := by
  rw [pairTerm, pairTerm]
  exact integral_congr_ae (h.mono fun z hz => by simp only [hz])

/-- The `pairing` only depends on the weight up to almost-everywhere equality of its clamped
pullbacks. -/
theorem pairing_congr_weight_ae {ι : Type*} [Fintype ι] {y : ι → X} {ρ σ : ι → ℝ}
    {ψ ψ' : ι → X → ℝ} {f χ : X → ℝ}
    (h : ∀ i, clampedPullback (y i) (σ i) (ψ i) =ᵐ[volume] clampedPullback (y i) (σ i) (ψ' i)) :
    pairing y ρ σ ψ f χ = pairing y ρ σ ψ' f χ := by
  simp only [pairing]
  exact Finset.sum_congr rfl fun i _ => pairTerm_congr_weight_ae (h i)

/-- `PairIntegrable` is symmetric in its two function arguments. -/
theorem PairIntegrable.comm {x : X} {ρ σ : ℝ} {W f χ : X → ℝ}
    (h : PairIntegrable x ρ σ W f χ) : PairIntegrable x ρ σ W χ f := by
  rw [PairIntegrable] at h ⊢
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [real_inner_comm]

/-- `PairIntegrable` is insensitive to almost-everywhere changes of the clamped weight. -/
theorem PairIntegrable.congr_ae {x : X} {ρ σ : ℝ} {W W' f χ : X → ℝ}
    (h : PairIntegrable x ρ σ W' f χ)
    (heq : clampedPullback x σ W =ᵐ[volume] clampedPullback x σ W') :
    PairIntegrable x ρ σ W f χ :=
  h.congr (heq.mono fun z hz => by simp only [hz])

/-- **Boundedness of the gradient of a clamped pullback from chart-wise `C¹` on the closed ball
only** (the version of `Work.Drive.GreenRung.gradient_clampedPullback_le` in which the hypothesis
only has to hold on the closed ball of radius `σ < ρ`, which is all the bound needs). -/
theorem exists_bound_gradient_clampedPullback_of_c1_on_closedBall {y : X} {ρ σ : ℝ} {Φ : X → ℝ}
    (hσρ : σ < ρ) (htgt : Metric.ball ((chartAt ℂ y) y) ρ ⊆ (chartAt ℂ y).target)
    (hΦ : ∀ z ∈ Metric.closedBall ((chartAt ℂ y) y) σ,
      ContDiffAt ℝ 1 (Φ ∘ (chartAt ℂ y).symm) z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Metric.ball ((chartAt ℂ y) y) σ,
      ‖gradient (clampedPullback y ρ Φ) z‖ ≤ C := by
  have hA : ContinuousOn (fun z : ℂ => gradient (fun w : ℂ => Φ ((chartAt ℂ y).symm w)) z)
      (Metric.closedBall ((chartAt ℂ y) y) σ) := by
    intro z hz
    have hF : ContDiffAt ℝ 1 (fun w : ℂ => Φ ((chartAt ℂ y).symm w)) z := hΦ z hz
    have h1 : ContinuousAt
        (fun w : ℂ => fderiv ℝ (fun u : ℂ => Φ ((chartAt ℂ y).symm u)) w) z :=
      hF.continuousAt_fderiv (by norm_num)
    have h2 : ContinuousAt (fun w : ℂ => gradient (fun u : ℂ => Φ ((chartAt ℂ y).symm u)) w) z := by
      simpa only [gradient, Function.comp_def] using
        (InnerProductSpace.toDual ℝ ℂ).symm.continuous.continuousAt.comp h1
    exact h2.continuousWithinAt
  have hB : ∀ z ∈ Metric.closedBall ((chartAt ℂ y) y) σ,
      gradient (clampedPullback y ρ Φ) z
        = gradient (fun w : ℂ => Φ ((chartAt ℂ y).symm w)) z := by
    intro z hz
    refine Filter.EventuallyEq.gradient_eq ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds
      (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hσρ)] with w hw
    rw [clampedPullback_apply_of_mem hw]
  have hcont : ContinuousOn (fun z : ℂ => gradient (clampedPullback y ρ Φ) z)
      (Metric.closedBall ((chartAt ℂ y) y) σ) := hA.congr hB
  obtain ⟨C, hC⟩ := (isCompact_closedBall ((chartAt ℂ y) y) σ).exists_bound_of_continuousOn hcont
  exact ⟨max C 0, le_max_right _ _, fun z hz =>
    le_trans (hC z (Metric.ball_subset_closedBall hz)) (le_max_left _ _)⟩

theorem deriv_thetaCutoff_eq {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    deriv (thetaCutoff σ) t = t * deriv (stepCutoff σ) t :=
  (hasDerivAt_thetaCutoff hσ t).deriv


/-- **A Green function exceeds any level on a punctured chart ball around its pole.** -/
theorem exists_chartBall_le_of_hasLogPoleOn {Ω : Set X} (hΩo : IsOpen Ω) {b : X} (hbΩ : b ∈ Ω)
    {G : X → ℝ} (h : Work.SimplyConnected.ABS.HasLogPoleOn Ω b G) (M : ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball ((chartAt ℂ b) b) ρ ⊆ (chartAt ℂ b).target ∧
      ∀ x ∈ Submission.chartBall (chartAt ℂ b) ((chartAt ℂ b) b) ρ, x ≠ b → M ≤ G x := by
  obtain ⟨C, V, hV, hCV⟩ := h
  obtain ⟨U, hUV, hUopen, hbU⟩ := mem_nhds_iff.mp hV
  set rc : ℝ := Real.exp (-(M + C)) / 2 with hrc
  have hrcpos : 0 < rc := by rw [hrc]; positivity
  have hrcb : b ∈ Submission.chartBall (chartAt ℂ b) ((chartAt ℂ b) b) rc := by
    rw [Submission.mem_chartBall]
    exact ⟨mem_chart_source ℂ b, by rw [Metric.mem_ball, dist_self]; exact hrcpos⟩
  have hrcΩ : b ∈ Ω := hbΩ
  have hOopen : IsOpen (Ω ∩ U ∩ Submission.chartBall (chartAt ℂ b) ((chartAt ℂ b) b) rc) :=
    (hΩo.inter hUopen).inter (Submission.chartBall_isOpen _ _ _)
  obtain ⟨ρ, hρ, htgtρ, hsubρ⟩ :=
    Work.Kernel.exists_chartBall_subset hOopen ⟨⟨hrcΩ, hbU⟩, hrcb⟩
  refine ⟨ρ, hρ, htgtρ, fun x hx hxb => ?_⟩
  obtain ⟨hxΩU, hxball⟩ := hsubρ hx
  obtain ⟨hxΩ, hxU⟩ := hxΩU
  have hxV : x ∈ V := hUV hxU
  have hle := hCV x hxV hxΩ hxb
  have hlog : Real.log ‖(chartAt ℂ b) x - (chartAt ℂ b) b‖ < -(M + C) := by
    obtain ⟨hxsrc, hxmem⟩ := Submission.mem_chartBall.mp hxball
    have h1 : ‖(chartAt ℂ b) x - (chartAt ℂ b) b‖ < rc := by
      rw [Metric.mem_ball, dist_eq_norm] at hxmem
      exact hxmem
    have h2 : 0 < ‖(chartAt ℂ b) x - (chartAt ℂ b) b‖ := by
      rw [norm_pos_iff]
      exact sub_ne_zero.mpr (fun hcon => hxb ((chartAt ℂ b).injOn hxsrc (mem_chart_source ℂ b) hcon))
    have h3 : Real.log rc < -(M + C) := by
      rw [hrc, Real.log_div (Real.exp_ne_zero _) (by norm_num : (2:ℝ) ≠ 0),
        Real.log_exp]
      rw [sub_lt_iff_lt_add']
      have h5 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      linarith
    exact lt_trans (Real.log_lt_log h2 h1) h3
  have h1 : -C ≤ G x + Real.log ‖(chartAt ℂ b) x - (chartAt ℂ b) b‖ := (abs_le.mp hle).1
  linarith

/-- **The support of the logarithmic bump at `ib` is so small that all other weights vanish on
it.** -/
theorem exists_chartClosedBall_psi_eq_zero_of_ne_ib {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X}
    (E : Work.Kernel.GreenCover ι Ω K a b) (hEyb : E.y E.ib = b) (hia : E.ia ≠ E.ib) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Metric.closedBall ((chartAt ℂ (E.y E.ib)) (E.y E.ib)) ρ ⊆ (chartAt ℂ (E.y E.ib)).target ∧
      ∀ i, i ≠ E.ib → ∀ x ∈ Submission.chartClosedBall (chartAt ℂ (E.y E.ib))
        ((chartAt ℂ (E.y E.ib)) (E.y E.ib)) ρ, E.ψ i x = 0 := by
  classical
  have hev : ∀ᶠ x in 𝓝 (E.y E.ib), ∀ i, i ≠ E.ib → E.ψ i x = 0 := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : i = E.ib
    · subst hi
      exact Filter.Eventually.of_forall (fun x hx => absurd rfl hx)
    · have h0 : E.ψ i =ᶠ[𝓝 (E.y E.ib)] 0 := by
        rw [show E.y E.ib = b from hEyb]   -- hmm
        exact E.ψ_eq_zero_nhds_b i hi
      exact h0.mono (fun x hx _ => hx)
  obtain ⟨U, hUsub, hUopen, hbU⟩ := mem_nhds_iff.mp hev
  obtain ⟨ε, hε, htgtε, hsubε⟩ := Work.Kernel.exists_chartBall_subset (O := U) hUopen hbU
  refine ⟨ε / 2, by positivity, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ Metric.ball ((chartAt ℂ (E.y E.ib)) (E.y E.ib)) ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      have h2 := Metric.mem_closedBall.mp hx
      rw [dist_eq_norm] at h2
      linarith
    exact htgtε hx'
  · intro i hi x hx
    have hx' : x ∈ Submission.chartBall (chartAt ℂ (E.y E.ib))
        ((chartAt ℂ (E.y E.ib)) (E.y E.ib)) ε := by
      obtain ⟨hxs, hxb⟩ := Submission.mem_chartClosedBall.mp hx
      refine Submission.mem_chartBall.mpr ⟨hxs, ?_⟩
      rw [Metric.mem_ball, dist_eq_norm]
      have h2 := Metric.mem_closedBall.mp hxb
      rw [dist_eq_norm] at h2
      linarith
    exact hUsub (hsubε hx') i hi

/-- **Per-chart growth data of a Green function in a cover.** -/
theorem exists_growth_data_clampedPullback_of_isGreenOn {ι : Type*} [Fintype ι] {Ω K : Set X}
    {a b c : X} (E : Work.Kernel.GreenCover ι Ω K a b) (ip : ι) (hia : E.y ip = c)
    (havoid : ∀ i, i ≠ ip → c ∉ Submission.chartClosedBall
      (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)) (E.y i)) (E.σ i))
    {gC : X → ℝ} (hgC : Work.SimplyConnected.ABS.IsGreenOn Ω c gC)
    {H : ℂ → ℝ} {r : ℝ} (hr : 0 < r)
    (hH : InnerProductSpace.HarmonicOnNhd H (Metric.ball ((chartAt ℂ c) c) r))
    (hueq : ∀ z ∈ Metric.ball ((chartAt ℂ c) c) r, z ≠ (chartAt ℂ c) c →
      gC ((chartAt ℂ c).symm z) = -Real.log ‖z - (chartAt ℂ c) c‖ + H z) :
    ∀ i : ι, ∃ (q : ℂ) (C : ℝ), 0 < C ∧
      ∀ z ∈ Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.s i), z ≠ q →
        ‖gradient (clampedPullback (E.y i) (E.ρ i) gC) z‖ ≤ C / ‖z - q‖ := by
  intro i
  by_cases hi : i = ip
  · rw [hi]
    have hH' : InnerProductSpace.HarmonicOnNhd H
        (Metric.ball ((chartAt ℂ (E.y ip)) c) r) := by rw [hia]; exact hH
    have hueq' : ∀ z ∈ Metric.ball ((chartAt ℂ (E.y ip)) c) r,
        z ≠ (chartAt ℂ (E.y ip)) c →
        gC ((chartAt ℂ (E.y ip)).symm z) = -Real.log ‖z - (chartAt ℂ (E.y ip)) c‖ + H z := by
      rw [hia]; exact hueq
    obtain ⟨C, hCpos, hC⟩ := Work.Kernel.PS.exists_growth_clampedPullback_le_of_logExpansion
      (Ω := Ω) (a := c) (gA := gC) (y := E.y ip) (ρ := E.ρ ip) (σ := E.s ip)
      (δ := r) (H := H) hgC (lt_trans (E.hsσ ip) (E.hσρ ip)) (E.htgt ip)
      (E.hballΩ ip) hr hH' hueq'
    exact ⟨(chartAt ℂ (E.y ip)) c, C, hCpos, hC⟩
  · obtain ⟨C, hCpos, hC⟩ := Work.Kernel.PS.exists_bound_clampedPullback_le_of_notMem
      (Ω := Ω) (a := c) (gA := gC) (y := E.y i) (ρ := E.ρ i) (σ := E.σ i)
      hgC (E.hσρ i) (E.htgt i) (E.hballΩ i) (havoid i hi)
    refine ⟨(chartAt ℂ (E.y i)) (E.y i), C * E.s i + 1, by nlinarith [hCpos, E.hspos i], ?_⟩
    intro z hz hzq
    have hzb : ‖gradient (clampedPullback (E.y i) (E.ρ i) gC) z‖ ≤ C :=
      hC z (Metric.closedBall_subset_closedBall (le_of_lt (E.hsσ i)) hz)
    refine le_trans hzb ?_
    have hnorm : ‖z - (chartAt ℂ (E.y i)) (E.y i)‖ ≤ E.s i := by
      rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hz
    have hpos : 0 < ‖z - (chartAt ℂ (E.y i)) (E.y i)‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hzq)
    rw [le_div_iff₀ hpos]
    nlinarith [hCpos, E.hspos i, hnorm]

/-- Chart-wise `C¹` of a harmonic function off a pole, on a chart ball inside the domain of
harmonicity. -/
theorem contDiffAt_chart_of_harmonic_off {Ω : Set X} {p : X} {u : X → ℝ}
    (hu : Submission.HarmonicOnX u (Ω \ {p})) {y : X} {ρ : ℝ}
    (hballΩ : Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) ρ ⊆ Ω)
    {x : X} (hx : x ∈ Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) ρ) (hxp : x ≠ p) :
    ContDiffAt ℝ 1 (u ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) := by
  have hharm : Submission.HarmonicOnXAt u x := hu x ⟨hballΩ hx, hxp⟩
  have h := (Submission.HarmonicOnXAt_iff_chart (u := u) (x := x) (y := y) hx.1).mp hharm
  exact h.1.of_le (by norm_num)

/-- Chart-wise `C¹` of a `C¹` function of a harmonic function. -/
theorem contDiffAt_chart_comp_of_contDiffAt {u : X → ℝ} {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    {y x : X} (h : ContDiffAt ℝ 1 (u ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x)) :
    ContDiffAt ℝ 1 ((Φ ∘ u) ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) := by
  have h' : (Φ ∘ u) ∘ (chartAt ℂ y).symm
      = Φ ∘ (u ∘ (chartAt ℂ y).symm) := rfl
  rw [h']
  exact hΦ.contDiffAt.comp _ h


/-! ## 9. Integrability certificates: bounds on a support, and transfer rules -/

/-- Pointwise version of the multiplicativity of the clamped pullback. -/
theorem clampedPullback_mul_apply {x : X} {ρ : ℝ} {u v : X → ℝ} {z : ℂ} :
    clampedPullback x ρ (fun y => u y * v y) z = clampedPullback x ρ u z * clampedPullback x ρ v z :=
  congrFun (Work.Drive.GreenRung.clampedPullback_mul x ρ u v) z

/-- Function version of the multiplicativity of the clamped pullback. -/
theorem clampedPullback_mul_fun {x : X} {ρ : ℝ} {u v : X → ℝ} :
    clampedPullback x ρ (fun y => u y * v y) = clampedPullback x ρ u * clampedPullback x ρ v :=
  funext fun z => clampedPullback_mul_apply

/-- Function version of the additivity of the clamped pullback. -/
theorem clampedPullback_add_fun {x : X} {ρ : ℝ} {u v : X → ℝ} :
    clampedPullback x ρ (fun y => u y + v y) = clampedPullback x ρ u + clampedPullback x ρ v :=
  funext fun z => congrFun (clampedPullback_add x ρ u v) z

/-- Almost-everywhere differentiability of a clamped pullback whose chart expression is
differentiable off a single point (local copy of `Work.Drive.clampedPullback_differentiableAt_ae_of_off`,
whose module pulls in a broken dependency). -/
theorem clampedPullback_differentiableAt_ae_of_off' {x : X} {ρ : ℝ} {u : X → ℝ} {z₀ : ℂ}
    (htgt : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target)
    (hu : ∀ z ∈ Metric.ball ((chartAt ℂ x) x) ρ, z ≠ z₀ →
      DifferentiableAt ℝ (fun w : ℂ => u ((chartAt ℂ x).symm w)) z) :
    ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ (clampedPullback x ρ u) z := by
  rw [ae_iff]
  have hnull : volume ({z₀} ∪ Metric.sphere ((chartAt ℂ x) x) ρ) = 0 :=
    measure_union_null (measure_singleton _)
      (MeasureTheory.Measure.addHaar_sphere (MeasureTheory.volume : MeasureTheory.Measure ℂ) _ ρ)
  refine measure_mono_null (fun z hz => ?_) hnull
  by_cases hb : z ∈ Metric.ball ((chartAt ℂ x) x) ρ
  · by_cases hz0 : z = z₀
    · exact Or.inl hz0
    · refine Or.inr ?_
      by_contra hnot
      have hev : (fun w : ℂ => u ((chartAt ℂ x).symm w)) =ᶠ[𝓝 z] clampedPullback x ρ u := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hb] with w hw
        exact (clampedPullback_apply_of_mem (x₀ := x) (ρ := ρ) (u := u) hw).symm
      exact hz ((hev.differentiableAt_iff).mp (hu z hb hz0))
  · by_cases hc : z ∈ Metric.closedBall ((chartAt ℂ x) x) ρ
    · refine Or.inr ?_
      rw [Metric.mem_sphere]
      exact le_antisymm hc (not_lt.mp hb)
    · have hev : clampedPullback x ρ u =ᶠ[𝓝 z] 0 := by
        filter_upwards [(Metric.isClosed_closedBall.isOpen_compl).mem_nhds hc] with w hw
        exact clampedPullback_eq_zero_of_notMem_ball (x := x) (ρ := ρ) (u := u)
          (fun hmem => hw (Metric.ball_subset_closedBall hmem))
      exact absurd ((hev.differentiableAt_iff).mpr (differentiableAt_const 0)) hz

/-- `PairIntegrable` from an explicit integrable majorant. -/
theorem pairIntegrable_of_majorant {x : X} {ρ σ : ℝ} {W f χ : X → ℝ} {Φ : ℂ → ℝ}
    (hmaj : Integrable Φ volume)
    (hmeas : AEStronglyMeasurable (fun z : ℂ => clampedPullback x σ W z *
      inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z)
        (gradient (clampedPullback x ρ χ) z)) volume)
    (hbd : ∀ᵐ z ∂(volume : Measure ℂ), ‖clampedPullback x σ W z *
      inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z)
        (gradient (clampedPullback x ρ χ) z)‖ ≤ Φ z) :
    PairIntegrable x ρ σ W f χ :=
  Integrable.mono' hmaj hmeas hbd

/-- **Bound on the gradient of the clamped pullback of a Green function on a compact set of the
chart avoiding the pole.** -/
theorem exists_bound_gradient_clampedPullback_on_compact {Ω : Set X} {c : X} {G : X → ℝ}
    (hcΩ : c ∈ Ω) (hG : Work.SimplyConnected.ABS.IsGreenOn Ω c G)
    {y : X} {ρ : ℝ} (htgt : Metric.ball ((chartAt ℂ y) y) ρ ⊆ (chartAt ℂ y).target)
    {T : Set ℂ} (hT : IsCompact T) (hTρ : T ⊆ Metric.ball ((chartAt ℂ y) y) ρ)
    (hTΩ : ∀ z ∈ T, (chartAt ℂ y).symm z ∈ Ω) (hTc : ∀ z ∈ T, (chartAt ℂ y).symm z ≠ c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ T, ‖gradient (clampedPullback y ρ G) z‖ ≤ B := by
  have hcont : ContinuousOn (fun z : ℂ => gradient (clampedPullback y ρ G) z) T := by
    intro z hz
    have hzρ : z ∈ Metric.ball ((chartAt ℂ y) y) ρ := hTρ hz
    set x : X := (chartAt ℂ y).symm z with hx
    have hxsrc : x ∈ (chartAt ℂ y).source := (chartAt ℂ y).map_target (htgt hzρ)
    have hright : (chartAt ℂ y) x = z := (chartAt ℂ y).right_inv (htgt hzρ)
    have hharm : Submission.HarmonicOnXAt G x := hG.2.1 x ⟨hTΩ z hz, hTc z hz⟩
    have hH := (Submission.HarmonicOnXAt_iff_chart (u := G) (x := x) (y := y) hxsrc).mp hharm
    have hc1 : ContDiffAt ℝ 1 (fun w : ℂ => G ((chartAt ℂ y).symm w)) z := by
      have hH' : ContDiffAt ℝ 1 (G ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) :=
        hH.1.of_le (by norm_num)
      rwa [hright] at hH'
    have h1 : ContinuousAt (fun w : ℂ => fderiv ℝ (fun u : ℂ => G ((chartAt ℂ y).symm u)) w) z :=
      hc1.continuousAt_fderiv (by norm_num)
    have h2 : ContinuousAt (fun w : ℂ => gradient (fun u : ℂ => G ((chartAt ℂ y).symm u)) w) z := by
      simpa only [gradient, Function.comp_def] using
        (InnerProductSpace.toDual ℝ ℂ).symm.continuous.continuousAt.comp h1
    have hev : (fun w : ℂ => gradient (clampedPullback y ρ G) w) =ᶠ[𝓝 z]
        (fun w : ℂ => gradient (fun u : ℂ => G ((chartAt ℂ y).symm u)) w) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hzρ] with w hw
      refine Filter.EventuallyEq.gradient_eq ?_
      filter_upwards [Metric.isOpen_ball.mem_nhds hw] with w' hw'
      exact clampedPullback_apply_of_mem hw'
    exact (h2.congr hev.symm).continuousWithinAt
  obtain ⟨B, hB⟩ := hT.exists_bound_of_continuousOn hcont
  exact ⟨max B 0, le_max_right _ _, fun z hz => le_trans (hB z hz) (le_max_left _ _)⟩

/-- **Bound on the gradient of the clamped pullback of a Green function in a chart avoiding its
pole.** -/
theorem exists_bound_gradient_clampedPullback_of_avoid {Ω : Set X} {c : X} {G : X → ℝ}
    (hΩo : IsOpen Ω) (hcΩ : c ∈ Ω) (hG : Work.SimplyConnected.ABS.IsGreenOn Ω c G)
    {y : X} {ρ σ : ℝ} (hσρ : σ < ρ)
    (htgt : Metric.ball ((chartAt ℂ y) y) ρ ⊆ (chartAt ℂ y).target)
    (hballΩ : Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) ρ ⊆ Ω)
    (havoid : c ∉ Submission.chartClosedBall (chartAt ℂ y) ((chartAt ℂ y) y) σ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ Metric.ball ((chartAt ℂ y) y) σ,
      ‖gradient (clampedPullback y ρ G) z‖ ≤ K := by
  refine exists_bound_gradient_clampedPullback_of_c1_on_closedBall hσρ htgt (fun z hz => ?_)
  have hzρ : z ∈ Metric.ball ((chartAt ℂ y) y) ρ :=
    lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hσρ
  have hsrcy : (chartAt ℂ y).symm z ∈ (chartAt ℂ y).source :=
    (chartAt ℂ y).map_target (htgt hzρ)
  have hright : (chartAt ℂ y) ((chartAt ℂ y).symm z) = z :=
    (chartAt ℂ y).right_inv (htgt hzρ)
  have hne : (chartAt ℂ y).symm z ≠ c := by
    intro hcon
    have h1 : (chartAt ℂ y) c = z := by rw [← hcon, hright]
    refine havoid ⟨by rw [← hcon]; exact hsrcy, ?_⟩
    show (chartAt ℂ y) c ∈ Metric.closedBall ((chartAt ℂ y) y) σ
    rw [h1]
    exact Metric.mem_closedBall.mp hz
  have hxΩ : (chartAt ℂ y).symm z ∈ Ω :=
    hballΩ ⟨hsrcy, by
      show (chartAt ℂ y) ((chartAt ℂ y).symm z) ∈ Metric.ball ((chartAt ℂ y) y) ρ
      rw [hright]; exact hzρ⟩
  have hharm : Submission.HarmonicOnXAt G ((chartAt ℂ y).symm z) :=
    hG.2.1 _ ⟨hxΩ, hne⟩
  have hiff := (Submission.HarmonicOnXAt_iff_chart (u := G)
    (x := (chartAt ℂ y).symm z) (y := y) hsrcy).mp hharm
  have h2 : ContDiffAt ℝ 1 (G ∘ (chartAt ℂ y).symm)
      ((chartAt ℂ y) ((chartAt ℂ y).symm z)) := hiff.1.of_le (by norm_num)
  rwa [hright] at h2

/-- **Almost-everywhere bound on the gradient of the clamped pullback of a Green function, on the
support of a weight whose support avoids the pole and lies in the chart ball.** -/
theorem exists_bound_gradient_clampedPullback_on_support {Ω : Set X} {c : X} {G : X → ℝ}
    (hcΩ : c ∈ Ω) (hG : Work.SimplyConnected.ABS.IsGreenOn Ω c G)
    {y : X} {ρ : ℝ} (htgt : Metric.ball ((chartAt ℂ y) y) ρ ⊆ (chartAt ℂ y).target)
    {W : X → ℝ} (hWcs : HasCompactSupport W) (hWsrc : tsupport W ⊆ (chartAt ℂ y).source)
    (hWΩ : tsupport W ⊆ Ω) (hWc' : c ∉ tsupport W)
    (hWρ : tsupport W ⊆ Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) ρ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ z ∂(volume : Measure ℂ),
      z ∈ tsupport (clampedPullback y ρ W) →
        ‖gradient (clampedPullback y ρ G) z‖ ≤ B := by
  set T : Set ℂ := (chartAt ℂ y) '' tsupport W with hTdef
  have hcontOn : ContinuousOn (chartAt ℂ y) (tsupport W) :=
    (chartAt ℂ y).continuousOn.mono (fun x hx => hWsrc hx)
  have hT : IsCompact T := hWcs.image_of_continuousOn hcontOn
  have hTρ : T ⊆ Metric.ball ((chartAt ℂ y) y) ρ := by
    rintro z ⟨x, hx, rfl⟩
    exact (hWρ hx).2
  have hTΩ : ∀ z ∈ T, (chartAt ℂ y).symm z ∈ Ω := by
    rintro z ⟨x, hx, rfl⟩
    rw [(chartAt ℂ y).left_inv (hWsrc hx)]
    exact hWΩ hx
  have hTc : ∀ z ∈ T, (chartAt ℂ y).symm z ≠ c := by
    rintro z ⟨x, hx, rfl⟩
    rw [(chartAt ℂ y).left_inv (hWsrc hx)]
    exact fun h => hWc' (h ▸ hx)
  obtain ⟨B, hBnn, hB⟩ :=
    exists_bound_gradient_clampedPullback_on_compact hcΩ hG htgt hT hTρ hTΩ hTc
  refine ⟨B, hBnn, ?_⟩
  rw [ae_iff]
  refine measure_mono_null (fun z hz => ?_)
    (MeasureTheory.Measure.addHaar_sphere volume ((chartAt ℂ y) y) ρ)
  rw [Set.mem_ofPred_eq, Classical.not_imp] at hz
  obtain ⟨hzs, hznb⟩ := hz
  have hsuppClosed : tsupport (clampedPullback y ρ W) ⊆ Metric.closedBall ((chartAt ℂ y) y) ρ :=
    Work.Kernel.PS.tsupport_clampedPullback_subset_closedBall' htgt hWρ
  by_cases hb : z ∈ Metric.ball ((chartAt ℂ y) y) ρ
  · have hsub : {s : ℂ | clampedPullback y ρ W s ≠ 0} ⊆ T := by
      intro s hs
      have hsρ : s ∈ Metric.ball ((chartAt ℂ y) y) ρ := by
        by_contra hcon
        exact hs (clampedPullback_eq_zero_of_notMem_ball hcon)
      have hWs : W ((chartAt ℂ y).symm s) ≠ 0 := by
        intro h0
        exact hs (by rw [clampedPullback_apply_of_mem hsρ, h0])
      exact ⟨(chartAt ℂ y).symm s, subset_tsupport _ (Function.mem_support.mpr hWs),
        (chartAt ℂ y).right_inv (htgt hsρ)⟩
    exact absurd (hB z (closure_minimal hsub hT.isClosed hzs)) hznb
  · have hmem : z ∈ Metric.closedBall ((chartAt ℂ y) y) ρ := hsuppClosed hzs
    rw [Metric.mem_sphere]
    exact le_antisymm hmem (not_lt.mp hb)

/-! ### 9b. Transfer rules for `PairIntegrable` -/

/-- The chain rule for `PairIntegrable`: the integrand of `W` against `(f, Φ ∘ g)` is almost
everywhere the integrand of `W · (Φ' ∘ g)` against `(f, g)`. -/
theorem pairIntegrand_comp_ae {x : X} {ρ σ : ℝ} {W f g : X → ℝ} {Φ : ℝ → ℝ}
    (hσρ : σ < ρ) (hΦ0 : Φ 0 = 0) (hΦd : Differentiable ℝ Φ)
    (hdiff : ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ (clampedPullback x ρ g) z) :
    (fun z : ℂ => clampedPullback x σ W z *
        inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z)
          (gradient (clampedPullback x ρ (fun y => Φ (g y))) z)) =ᵐ[volume]
      (fun z : ℂ => clampedPullback x σ (fun y => W y * deriv Φ (g y)) z *
        inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z)
          (gradient (clampedPullback x ρ g) z)) := by
  filter_upwards [hdiff] with z hzd
  by_cases hz : z ∈ Metric.ball ((chartAt ℂ x) x) σ
  · have hzρ : z ∈ Metric.ball ((chartAt ℂ x) x) ρ :=
      Metric.ball_subset_ball (le_of_lt hσρ) hz
    have hgz : clampedPullback x ρ g z = g ((chartAt ℂ x).symm z) :=
      clampedPullback_apply_of_mem hzρ
    have h1 : clampedPullback x σ (fun y => W y * deriv Φ (g y)) z
        = clampedPullback x σ W z * deriv Φ (g ((chartAt ℂ x).symm z)) := by
      rw [clampedPullback_mul_apply, clampedPullback_apply_of_mem (u := W) hz,
        clampedPullback_apply_of_mem (u := fun y => deriv Φ (g y)) hz]
    have hgr : gradient (clampedPullback x ρ (fun y => Φ (g y))) z
        = deriv Φ (g ((chartAt ℂ x).symm z)) • gradient (clampedPullback x ρ g) z := by
      have hfun : clampedPullback x ρ (fun y => Φ (g y))
          = fun w => Φ (clampedPullback x ρ g w) :=
        clampedPullback_comp (x := x) (ρ := ρ) (g := g) hΦ0
      rw [hfun, gradient_comp_of_differentiableAt hΦd.differentiableAt hzd, hgz]
    rw [hgr, inner_smul_right, h1]
    ring
  · rw [clampedPullback_eq_zero_of_notMem_ball (x := x) (ρ := σ) (u := W) hz,
      clampedPullback_eq_zero_of_notMem_ball (x := x) (ρ := σ)
        (u := fun y => W y * deriv Φ (g y)) hz]
    ring

/-- The chain rule for `PairIntegrable` (both directions). -/
theorem PairIntegrable.comp_iff {x : X} {ρ σ : ℝ} {W f g : X → ℝ} {Φ : ℝ → ℝ}
    (hσρ : σ < ρ) (hΦ0 : Φ 0 = 0) (hΦd : Differentiable ℝ Φ)
    (hdiff : ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ (clampedPullback x ρ g) z) :
    PairIntegrable x ρ σ W f (fun y => Φ (g y))
      ↔ PairIntegrable x ρ σ (fun y => W y * deriv Φ (g y)) f g := by
  have hpt := pairIntegrand_comp_ae (x := x) (ρ := ρ) (σ := σ) (W := W) (f := f) (g := g)
    hσρ hΦ0 hΦd hdiff
  constructor
  · intro h
    rw [PairIntegrable] at h ⊢
    exact h.congr hpt
  · intro h
    rw [PairIntegrable] at h ⊢
    exact h.congr hpt.symm

/-- Additivity of the weight for `PairIntegrable`. -/
theorem PairIntegrable.weight_add {x : X} {ρ σ : ℝ} {W W' f g : X → ℝ}
    (h1 : PairIntegrable x ρ σ W f g) (h2 : PairIntegrable x ρ σ W' f g) :
    PairIntegrable x ρ σ (fun y => W y + W' y) f g := by
  rw [PairIntegrable] at h1 h2 ⊢
  have hpt : (fun z : ℂ => clampedPullback x σ (fun y => W y + W' y) z *
        inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z) (gradient (clampedPullback x ρ g) z))
      = fun z : ℂ => clampedPullback x σ W z *
          inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z) (gradient (clampedPullback x ρ g) z)
        + clampedPullback x σ W' z *
          inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z) (gradient (clampedPullback x ρ g) z) := by
    funext z
    rw [clampedPullback_add_fun, Pi.add_apply, add_mul]
  rw [hpt]
  exact h1.add h2

/-- The Leibniz rule for `PairIntegrable`: integrability of the two summands of the product rule
implies integrability of the product. -/
theorem PairIntegrable.leibniz {x : X} {ρ σ : ℝ} {W W' f g : X → ℝ}
    (hσρ : σ < ρ)
    (hf : ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ (clampedPullback x ρ f) z)
    (hg : ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ (clampedPullback x ρ g) z)
    (hW' : ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ (clampedPullback x ρ W') z)
    (h1 : PairIntegrable x ρ σ (fun y => W y * W' y) f g)
    (h2 : PairIntegrable x ρ σ (fun y => W y * g y) f W') :
    PairIntegrable x ρ σ W f (fun y => W' y * g y) := by
  rw [PairIntegrable] at h1 h2 ⊢
  have hpt : (fun z : ℂ => clampedPullback x σ (fun y => W y * W' y) z *
          inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z) (gradient (clampedPullback x ρ g) z)
        + clampedPullback x σ (fun y => W y * g y) z *
          inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z) (gradient (clampedPullback x ρ W') z))
      =ᵐ[volume]
      (fun z : ℂ => clampedPullback x σ W z *
        inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z)
          (gradient (clampedPullback x ρ (fun y => W' y * g y)) z)) := by
    filter_upwards [hf, hg, hW'] with z hfz hgz hWz
    by_cases hz : z ∈ Metric.ball ((chartAt ℂ x) x) σ
    · have hzρ : z ∈ Metric.ball ((chartAt ℂ x) x) ρ :=
        Metric.ball_subset_ball (le_of_lt hσρ) hz
      have hW : clampedPullback x σ (fun y => W y * W' y) z
          = clampedPullback x σ W z * clampedPullback x σ W' z := clampedPullback_mul_apply
      have hW2 : clampedPullback x σ (fun y => W y * g y) z
          = clampedPullback x σ W z * clampedPullback x σ g z := clampedPullback_mul_apply
      have hWa : clampedPullback x σ W z = clampedPullback x ρ W z := by
        rw [clampedPullback_apply_of_mem (u := W) hz, clampedPullback_apply_of_mem (u := W) hzρ]
      have hW'a : clampedPullback x σ W' z = clampedPullback x ρ W' z := by
        rw [clampedPullback_apply_of_mem (u := W') hz, clampedPullback_apply_of_mem (u := W') hzρ]
      have hga : clampedPullback x σ g z = clampedPullback x ρ g z := by
        rw [clampedPullback_apply_of_mem (u := g) hz, clampedPullback_apply_of_mem (u := g) hzρ]
      have hgrad : gradient (clampedPullback x ρ (fun y => W' y * g y)) z
          = clampedPullback x ρ W' z • gradient (clampedPullback x ρ g) z
            + clampedPullback x ρ g z • gradient (clampedPullback x ρ W') z := by
        rw [clampedPullback_mul_fun]
        exact Work.Drive.GreenRung.gradient_mul_real hWz hgz
      rw [hW, hW2, hgrad, hWa, hW'a, hga]
      simp only [inner_add_right, inner_smul_right]
      ring
    · rw [clampedPullback_eq_zero_of_notMem_ball (x := x) (ρ := σ)
          (u := fun y => W y * W' y) hz,
        clampedPullback_eq_zero_of_notMem_ball (x := x) (ρ := σ)
          (u := fun y => W y * g y) hz,
        clampedPullback_eq_zero_of_notMem_ball (x := x) (ρ := σ) (u := W) hz]
      ring
  exact (h1.add h2).congr hpt



/-! ## 7. The main theorem -/

open scoped BigOperators

/-- The composition of a `C¹` function of the chart at `b` with the inverse of a chart whose source
contains `b` is `C¹` at the image of `b` (the transition map is analytic there). -/
theorem contDiffAt_comp_chart_at {b : X} {H : ℂ → ℝ} (hH : ContDiffAt ℝ 1 H ((chartAt ℂ b) b))
    {y : X} (hy : b ∈ (chartAt ℂ y).source) :
    ContDiffAt ℝ 1 ((fun x => H ((chartAt ℂ b) x)) ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) b) := by
  have hbtgt : (chartAt ℂ y) b ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hy
  have hsrc : (↑(chartAt ℂ y).symm : ℂ → X) ((chartAt ℂ y) b) ∈ (chartAt ℂ b).source := by
    rw [(chartAt ℂ y).left_inv hy]; exact mem_chart_source ℂ b
  have hφ : AnalyticAt ℂ (fun w : ℂ => (chartAt ℂ b) ((chartAt ℂ y).symm w)) ((chartAt ℂ y) b) :=
    Submission.analyticAt_transition_of_mem_atlas (chart_mem_atlas ℂ b) (chart_mem_atlas ℂ y)
      ((chartAt ℂ y) b) hbtgt hsrc
  have hg : ContDiffAt ℝ 1 (fun w : ℂ => (chartAt ℂ b) ((chartAt ℂ y).symm w)) ((chartAt ℂ y) b) :=
    hφ.contDiffAt.restrict_scalars ℝ
  have hH' : ContDiffAt ℝ 1 H ((fun w : ℂ => (chartAt ℂ b) ((chartAt ℂ y).symm w))
      ((chartAt ℂ y) b)) := by
    change ContDiffAt ℝ 1 H ((chartAt ℂ b) ((chartAt ℂ y).symm ((chartAt ℂ y) b)))
    rw [(chartAt ℂ y).left_inv hy]; exact hH
  have hmain : ContDiffAt ℝ 1 (H ∘ fun w : ℂ => (chartAt ℂ b) ((chartAt ℂ y).symm w))
      ((chartAt ℂ y) b) := ContDiffAt.comp ((chartAt ℂ y) b) hH' hg
  exact hmain

/-- **Regularity of a test function supported in a compact set, given regularity off one point and an
eventual equality with a smooth function there.** -/
theorem contDiffAt_chart_of_support_and_pole {Ω K : Set X} (hKc : IsCompact K) (hKΩ : K ⊆ Ω)
    {Ψ Φ : X → ℝ} {p : X} (hpK : p ∈ K)
    (hΦ : ∀ y : X, p ∈ (chartAt ℂ y).source →
      ContDiffAt ℝ 1 (Φ ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) p))
    (hΨ : ∀ y : X, ∀ x ∈ (chartAt ℂ y).source, x ∈ K → x ≠ p →
      ContDiffAt ℝ 1 (Ψ ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x))
    (hev : Ψ =ᶠ[𝓝 p] Φ) (hsupp : tsupport Ψ ⊆ K) (y : X) :
    ∀ x ∈ (chartAt ℂ y).source,
      ContDiffAt ℝ 1 (Ψ ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) := by
  intro x hx
  by_cases hxK : x ∈ K
  · by_cases hxp : x = p
    · rw [hxp] at hx ⊢
      have hxtgt : (chartAt ℂ y) p ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hx
      have hsymm : (↑(chartAt ℂ y).symm : ℂ → X) ((chartAt ℂ y) p) = p := (chartAt ℂ y).left_inv hx
      have hcont : Filter.Tendsto (↑(chartAt ℂ y).symm : ℂ → X) (𝓝 ((chartAt ℂ y) p)) (𝓝 p) := by
        have h1 := ((chartAt ℂ y).continuousAt_symm hxtgt).tendsto
        rwa [hsymm] at h1
      exact (hΦ y hx).congr_of_eventuallyEq (hcont.eventually hev)
    · exact hΨ y x hx hxK hxp
  · -- outside `K` the function vanishes near `x`
    have hnot : x ∉ tsupport Ψ := fun h => hxK (hsupp h)
    have hzero : ∀ᶠ z in 𝓝 x, Ψ z = 0 := by
      filter_upwards [(isClosed_tsupport Ψ).isOpen_compl.mem_nhds hnot] with z hz
      exact image_eq_zero_of_notMem_tsupport hz
    have hxtgt : (chartAt ℂ y) x ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hx
    have hsymm : (↑(chartAt ℂ y).symm : ℂ → X) ((chartAt ℂ y) x) = x := (chartAt ℂ y).left_inv hx
    have hcont : Filter.Tendsto (↑(chartAt ℂ y).symm : ℂ → X) (𝓝 ((chartAt ℂ y) x)) (𝓝 x) := by
      simpa [hsymm] using ((chartAt ℂ y).continuousAt_symm hxtgt).tendsto
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq (hcont.eventually hzero)

set_option maxHeartbeats 1000000

/-- **The symmetry of the Green function of a precompact region** (the two-cutoff argument). -/
theorem cutoffReciprocity {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω : Set X} (hΩo : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {a b : X} (hab : a ≠ b) (ha : a ∈ Ω) (hb : b ∈ Ω)
    {gA gB : X → ℝ} (hgA : Work.SimplyConnected.ABS.IsGreenOn Ω a gA)
    (hgB : Work.SimplyConnected.ABS.IsGreenOn Ω b gB) : gA b = gB a := by
  classical
  haveI : DecidableEq X := Classical.decEq X
  -- ## Step 1: normalised Green functions with matched logarithmic expansions
  obtain ⟨g₁, hg₁, -, hag₁, hout₁⟩ := exists_isGreenOn_eq_off_pole hΩo ha hgA 1
  obtain ⟨G₁, hG₁, -, haG₁, houtG₁⟩ := exists_isGreenOn_eq_off_pole hΩo hb hgB 1
  obtain ⟨rA₀, hrA₀, HA₀, htgtA₀, hHA₀, hexpA₀⟩ :=
    Work.Kernel.greenExpansion_chart (y := a) hΩo ha hg₁ (mem_chart_source ℂ a)
  obtain ⟨rB₀, hrB₀, HB₀, htgtB₀, hHB₀, hexpB₀⟩ :=
    Work.Kernel.greenExpansion_chart (y := b) hΩo hb hG₁ (mem_chart_source ℂ b)
  set g : X → ℝ := Function.update g₁ a (HA₀ ((chartAt ℂ a) a)) with hgdef
  set G : X → ℝ := Function.update G₁ b (HB₀ ((chartAt ℂ b) b)) with hGdef
  have hg : Work.SimplyConnected.ABS.IsGreenOn Ω a g :=
    Work.SimplyConnected.ABS.IsGreenOn.update ha _ hg₁
  have hG : Work.SimplyConnected.ABS.IsGreenOn Ω b G :=
    Work.SimplyConnected.ABS.IsGreenOn.update hb _ hG₁
  have hexpA : ∀ z ∈ Metric.ball ((chartAt ℂ a) a) rA₀,
      g ((chartAt ℂ a).symm z) = -Real.log ‖z - (chartAt ℂ a) a‖ + HA₀ z :=
    expansion_of_update hexpA₀ htgtA₀
  have hexpB : ∀ z ∈ Metric.ball ((chartAt ℂ b) b) rB₀,
      G ((chartAt ℂ b).symm z) = -Real.log ‖z - (chartAt ℂ b) b‖ + HB₀ z :=
    expansion_of_update hexpB₀ htgtB₀
  have hgb : g b = gA b := by
    rw [hgdef, Function.update_of_ne (Ne.symm hab)]; exact hag₁ b hb (Ne.symm hab)
  have hGa : G a = gB a := by
    rw [hGdef, Function.update_of_ne hab]; exact haG₁ a ha hab
  suffices hmain : g b = G a by rw [hgb, hGa] at hmain; exact hmain
  -- ## Step 2: for every `ε > 0`, `|G a - g b| ≤ ε`
  have key : ∀ ε > 0, |G a - g b| ≤ ε := by
    intro ε hε
    have hga_pos : 0 < G a := hG.1 a ha hab
    -- the uniform decay of `g` on the level regions of `G`
    obtain ⟨δ, hδpos, hδ⟩ := Work.Kernel.sup_lt_of_level_lt_symm hg hG hε
    set σ : ℝ := min (δ / 4) (min (G a / 4) (ε / 2)) with hσdef
    have hσpos : 0 < σ := lt_min (by linarith) (lt_min (by linarith) (by linarith))
    have hσδ : 2 * σ ≤ δ := by
      have h1 : σ ≤ δ / 4 := min_le_left _ _
      linarith
    have hσG : 2 * σ < G a := by
      have h1 : σ ≤ G a / 4 := le_trans (min_le_right _ _) (min_le_left _ _)
      linarith
    have hσε : 2 * σ ≤ ε := by
      have h1 : σ ≤ ε / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
      linarith
    have hsup : ∀ x ∈ Ω, x ≠ a → x ≠ b → G x ≤ 2 * σ → g x < ε := by
      intro x hxΩ hxa hxb hxle
      exact hδ x hxΩ hxb hxa (le_trans hxle hσδ)
    -- ## Step 3: the compact summation region and the cover
    obtain ⟨K₀, hK₀c, hK₀Ω, hK₀⟩ := hG.2.2.1 σ hσpos
    obtain ⟨ra, hrapos, hratgt, hraΩ⟩ := Work.Kernel.exists_chartBall_subset
      (O := Ω \ {b}) (hΩo.sdiff isClosed_singleton) ⟨ha, by simpa using hab⟩
    obtain ⟨rb, hrbpos, hrbtgt, hrbΩ⟩ := Work.Kernel.exists_chartBall_subset
      (O := Ω \ {a}) (hΩo.sdiff isClosed_singleton) ⟨hb, by simpa using Ne.symm hab⟩
    set ra' : ℝ := min (rA₀ / 2) (ra / 2) with hra'
    set rb' : ℝ := min (rB₀ / 2) (rb / 2) with hrb'
    have hra'pos : 0 < ra' := lt_min (by linarith) (by linarith)
    have hrb'pos : 0 < rb' := lt_min (by linarith) (by linarith)
    have hra'le : ra' < rA₀ := by
      have h2 : rA₀ / 2 < rA₀ := by linarith
      exact lt_of_le_of_lt (min_le_left _ _) h2
    have hrb'le : rb' < rB₀ := by
      have h2 : rB₀ / 2 < rB₀ := by linarith
      exact lt_of_le_of_lt (min_le_left _ _) h2
    have hra'tgt : Metric.closedBall ((chartAt ℂ a) a) ra' ⊆ (chartAt ℂ a).target :=
      Subset.trans (Metric.closedBall_subset_ball hra'le) htgtA₀
    have hrb'tgt : Metric.closedBall ((chartAt ℂ b) b) rb' ⊆ (chartAt ℂ b).target :=
      Subset.trans (Metric.closedBall_subset_ball hrb'le) htgtB₀
    have hra'Ω : Submission.chartClosedBall (chartAt ℂ a) ((chartAt ℂ a) a) ra' ⊆ Ω := by
      refine Subset.trans ?_ (Subset.trans hraΩ (Set.sdiff_subset))
      intro x hx
      rw [Submission.mem_chartBall, Submission.mem_chartClosedBall] at *
      refine ⟨hx.1, ?_⟩
      exact Metric.closedBall_subset_ball
        (lt_of_le_of_lt (min_le_right _ _) (by linarith)) (Metric.mem_closedBall.mp hx.2)
    have hrb'Ω : Submission.chartClosedBall (chartAt ℂ b) ((chartAt ℂ b) b) rb' ⊆ Ω := by
      refine Subset.trans ?_ (Subset.trans hrbΩ (Set.sdiff_subset))
      intro x hx
      rw [Submission.mem_chartBall, Submission.mem_chartClosedBall] at *
      refine ⟨hx.1, ?_⟩
      exact Metric.closedBall_subset_ball
        (lt_of_le_of_lt (min_le_right _ _) (by linarith)) (Metric.mem_closedBall.mp hx.2)
    set K : Set X := K₀ ∪ Submission.chartClosedBall (chartAt ℂ a) ((chartAt ℂ a) a) ra'
      ∪ Submission.chartClosedBall (chartAt ℂ b) ((chartAt ℂ b) b) rb' with hK
    have hKc : IsCompact K := by
      refine (hK₀c.union (Submission.isCompact_chartClosedBall hra'tgt)).union
        (Submission.isCompact_chartClosedBall hrb'tgt)
    have hKΩ : K ⊆ Ω := by
      rw [hK]
      exact Set.union_subset (Set.union_subset hK₀Ω hra'Ω) hrb'Ω
    have ha_in : a ∈ Submission.chartClosedBall (chartAt ℂ a) ((chartAt ℂ a) a) ra' := by
      rw [Submission.mem_chartClosedBall]
      refine ⟨mem_chart_source ℂ a, ?_⟩
      rw [Metric.mem_closedBall, dist_self]
      exact le_of_lt hra'pos
    have hb_in : b ∈ Submission.chartClosedBall (chartAt ℂ b) ((chartAt ℂ b) b) rb' := by
      rw [Submission.mem_chartClosedBall]
      refine ⟨mem_chart_source ℂ b, ?_⟩
      rw [Metric.mem_closedBall, dist_self]
      exact le_of_lt hrb'pos
    have haK : a ∈ K := by
      simp only [hK, Set.mem_union]
      exact Or.inl (Or.inr ha_in)
    have hbK : b ∈ K := by
      simp only [hK, Set.mem_union]
      exact Or.inr hb_in
    obtain ⟨ι, hι, E, hEya, hEyb, hEρa, hEρb, hψc1, hβc1⟩ :=
      Work.Kernel.exists_greenCover_centred hΩo hKc hKΩ hab haK hbK ra' rb' hra'pos hrb'pos
    -- ## Step 4: the cutoffs and the test functions
    set Ξ : ℝ → ℝ := stepCutoff σ with hΞdef
    set θ : ℝ → ℝ := thetaCutoff σ with hθdef
    set cσ : ℝ := thetaCutoff σ (2 * σ) with hcσdef
    -- the updated level cutoffs
    set Ξg : X → ℝ := Function.update (fun x => Ξ (G x)) b (Ξ (2 * σ)) with hΞgdef
    set Th : X → ℝ := Function.update (fun x => θ (G x)) b (θ (2 * σ)) with hThdef
    have hΞ2σ : Ξ (2 * σ) = 1 := stepCutoff_eq_one_of_two_mul_le hσpos le_rfl
    have hθ2σ : θ (2 * σ) = cσ := rfl
    have hθ2σc : θ (2 * σ) = 2 * σ - ∫ s in (0 : ℝ)..(2 * σ), Ξ s := thetaCutoff_eq_of_two_mul_le hσpos le_rfl
    -- ## Step 5: the data of the two level cutoffs
    have hiaib : E.ia ≠ E.ib := fun h => hab (hEya.symm.trans ((by rw [h] : E.y E.ia = E.y E.ib).trans hEyb))
    -- the punctured lower bound of `G` near its pole (with a strict inequality)
    obtain ⟨ρG, hρGpos, htgtG, hGρ⟩ :=
      exists_chartBall_le_of_hasLogPoleOn hΩo hb hG.2.2.2 (2 * σ + 1)
    have hGρ2 : ∀ x ∈ Submission.chartBall (chartAt ℂ b) ((chartAt ℂ b) b) ρG, x ≠ b → 2 * σ ≤ G x :=
      fun x hx hxb => le_trans (by linarith) (hGρ x hx hxb)
    have hb_ball : b ∈ Submission.chartBall (chartAt ℂ b) ((chartAt ℂ b) b) ρG := by
      rw [Submission.mem_chartBall]
      exact ⟨mem_chart_source ℂ b, by rw [Metric.mem_ball, dist_self]; exact hρGpos⟩
    have hΞg_of_ne : ∀ x : X, x ≠ b → Ξg x = Ξ (G x) := by
      intro x hx
      simp only [hΞgdef, Function.update_of_ne hx]
    have hΞg_b : Ξg b = 1 := by
      simp only [hΞgdef, Function.update_self]
      exact hΞ2σ
    have hΞg_eq_one : Ξg =ᶠ[𝓝 b] 1 := by
      refine Filter.mem_of_superset
        ((Submission.chartBall_isOpen (chartAt ℂ b) ((chartAt ℂ b) b) ρG).mem_nhds hb_ball)
        (fun x hx => ?_)
      show Ξg x = 1
      by_cases hxb : x = b
      · rw [hxb]; exact hΞg_b
      · rw [hΞg_of_ne x hxb]
        exact stepCutoff_eq_one_of_two_mul_le hσpos (hGρ2 x hx hxb)
    have hΞg_a : Ξg a = 1 := by
      rw [hΞg_of_ne a hab]
      exact stepCutoff_eq_one_of_two_mul_le hσpos hσG.le
    have hΞg_eq_one_a : Ξg =ᶠ[𝓝 a] 1 := by
      have hcont : ContinuousAt G a := (hG.2.1 a ⟨ha, hab⟩).continuousAt
      have hmem : {x : X | 2 * σ < G x} ∈ 𝓝 a :=
        hcont.eventually (isOpen_Ioi.mem_nhds hσG)
      filter_upwards [hmem, isOpen_compl_singleton.mem_nhds (show a ∈ ({b} : Set X)ᶜ from hab)]
        with x hx hxb
      rw [hΞg_of_ne x hxb]
      exact stepCutoff_eq_one_of_two_mul_le hσpos hx.le
    have hTh_of_ne : ∀ x : X, x ≠ b → Th x = θ (G x) := by
      intro x hx
      simp only [hThdef, Function.update_of_ne hx]
    have hTh_b : Th b = cσ := by
      simp only [hThdef, Function.update_self]
      exact hθ2σ
    have hTh_eq : Th =ᶠ[𝓝 b] (fun _ => cσ) := by
      refine Filter.mem_of_superset
        ((Submission.chartBall_isOpen (chartAt ℂ b) ((chartAt ℂ b) b) ρG).mem_nhds hb_ball)
        (fun x hx => ?_)
      show Th x = cσ
      by_cases hxb : x = b
      · rw [hxb]; exact hTh_b
      · rw [hTh_of_ne x hxb]
        exact (thetaCutoff_eq_of_two_mul_le hσpos (hGρ2 x hx hxb)).trans hθ2σc.symm
    have hTh_a : Th a = cσ := by
      rw [hTh_of_ne a hab]
      exact (thetaCutoff_eq_of_two_mul_le hσpos hσG.le).trans hθ2σc.symm
    -- the support bounds
    have hGoff : ∀ x ∉ Ω, G x = 0 := by
      intro x hx
      have hxb : x ≠ b := fun h => hx (by rw [h]; exact hb)
      rw [hGdef, Function.update_of_ne hxb]
      exact houtG₁ x hx
    have hsupp_mem_K : ∀ x ∈ Ω, σ < G x → x ∈ K := by
      intro x hx hlt
      by_cases hxK : x ∈ K₀
      · rw [hK]; exact Set.mem_union_left _ (Set.mem_union_left _ hxK)
      · exact absurd (hK₀ x hx hxK) (not_lt.mpr hlt.le)
    have hΞgsupp : tsupport Ξg ⊆ K := by
      refine closure_minimal (fun x hx => ?_) hKc.isClosed
      rw [Function.mem_support] at hx
      by_cases hxb : x = b
      · rw [hxb]; exact hbK
      · have h2 : Ξ (G x) ≠ 0 := by rwa [hΞg_of_ne x hxb] at hx
        have hxG : σ < G x := by
          by_contra hcon
          exact h2 (stepCutoff_eq_zero_of_le hσpos (not_lt.mp hcon))
        have hxΩ : x ∈ Ω := by
          by_contra hcon
          rw [hGoff x hcon] at hxG
          exact absurd hxG (not_lt.mpr hσpos.le)
        exact hsupp_mem_K x hxΩ hxG
    have hThsupp : tsupport Th ⊆ K := by
      refine closure_minimal (fun x hx => ?_) hKc.isClosed
      rw [Function.mem_support] at hx
      by_cases hxb : x = b
      · rw [hxb]; exact hbK
      · have h2 : θ (G x) ≠ 0 := by rwa [hTh_of_ne x hxb] at hx
        have hxG : σ < G x := by
          by_contra hcon
          exact h2 (thetaCutoff_eq_zero_of_le hσpos (not_lt.mp hcon))
        have hxΩ : x ∈ Ω := by
          by_contra hcon
          rw [hGoff x hcon] at hxG
          exact absurd hxG (not_lt.mpr hσpos.le)
        exact hsupp_mem_K x hxΩ hxG
    -- the auxiliary level functions
    set Y_G : X → ℝ := Function.update (fun x => G x * deriv Ξ (G x)) b 0 with hY_Gdef
    set Y_V : X → ℝ := Function.update (fun x => deriv Ξ (G x)) b 0 with hY_Vdef
    set Y_g : X → ℝ := Function.update (fun x => g x * deriv Ξ (G x)) b 0 with hY_gdef
    have hderivΞ : ContDiff ℝ 1 (deriv Ξ) := (contDiff_stepCutoff σ (n := 2)).deriv'
    have deriv_zero_of_gt : ∀ t : ℝ, 2 * σ < t → deriv Ξ t = 0 := by
      intro t ht
      have hconst : Ξ =ᶠ[𝓝 t] (fun _ => 1) := by
        filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
        exact stepCutoff_eq_one_of_two_mul_le hσpos hs.le
      have hd := hconst.deriv_eq
      simpa using hd
    have deriv_zero_of_lt : ∀ t : ℝ, t < σ → deriv Ξ t = 0 := by
      intro t ht
      have hconst : Ξ =ᶠ[𝓝 t] (fun _ => 0) := by
        filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
        exact stepCutoff_eq_zero_of_le hσpos hs.le
      have hd := hconst.deriv_eq
      simpa using hd
    have hY_G_of_ne : ∀ x : X, x ≠ b → Y_G x = G x * deriv Ξ (G x) := by
      intro x hx; simp only [hY_Gdef, Function.update_of_ne hx]
    have hY_V_of_ne : ∀ x : X, x ≠ b → Y_V x = deriv Ξ (G x) := by
      intro x hx; simp only [hY_Vdef, Function.update_of_ne hx]
    have hY_g_of_ne : ∀ x : X, x ≠ b → Y_g x = g x * deriv Ξ (G x) := by
      intro x hx; simp only [hY_gdef, Function.update_of_ne hx]
    have hY_G_eq_zero : Y_G =ᶠ[𝓝 b] 0 := by
      refine Filter.mem_of_superset
        ((Submission.chartBall_isOpen (chartAt ℂ b) ((chartAt ℂ b) b) ρG).mem_nhds hb_ball)
        (fun x hx => ?_)
      show Y_G x = 0
      by_cases hxb : x = b
      · rw [hxb]; simp only [hY_Gdef, Function.update_self]
      · rw [hY_G_of_ne x hxb, deriv_zero_of_gt (G x) (lt_of_lt_of_le (by linarith : 2 * σ < 2 * σ + 1) (hGρ x hx hxb)), mul_zero]
    have hY_V_eq_zero : Y_V =ᶠ[𝓝 b] 0 := by
      refine Filter.mem_of_superset
        ((Submission.chartBall_isOpen (chartAt ℂ b) ((chartAt ℂ b) b) ρG).mem_nhds hb_ball)
        (fun x hx => ?_)
      show Y_V x = 0
      by_cases hxb : x = b
      · rw [hxb]; simp only [hY_Vdef, Function.update_self]
      · rw [hY_V_of_ne x hxb, deriv_zero_of_gt (G x) (lt_of_lt_of_le (by linarith : 2 * σ < 2 * σ + 1) (hGρ x hx hxb))]
    have hY_g_eq_zero : Y_g =ᶠ[𝓝 b] 0 := by
      refine Filter.mem_of_superset
        ((Submission.chartBall_isOpen (chartAt ℂ b) ((chartAt ℂ b) b) ρG).mem_nhds hb_ball)
        (fun x hx => ?_)
      show Y_g x = 0
      by_cases hxb : x = b
      · rw [hxb]; simp only [hY_gdef, Function.update_self]
      · rw [hY_g_of_ne x hxb, deriv_zero_of_gt (G x) (lt_of_lt_of_le (by linarith : 2 * σ < 2 * σ + 1) (hGρ x hx hxb)), mul_zero]
    have hY_g_zero_a : Y_g =ᶠ[𝓝 a] 0 := by
      have hmem : {x : X | 2 * σ < G x} ∈ 𝓝 a :=
        (hG.2.1 a ⟨ha, hab⟩).continuousAt.eventually (isOpen_Ioi.mem_nhds hσG)
      filter_upwards [hmem, isOpen_compl_singleton.mem_nhds (show a ∈ ({b} : Set X)ᶜ from hab)]
        with x hx hxb
      show Y_g x = 0
      rw [hY_g_of_ne x hxb, deriv_zero_of_gt (G x) hx, mul_zero]
    have hsupp_of_ge : ∀ {Y : X → ℝ}, (∀ x, x ≠ b → Y x ≠ 0 → σ ≤ G x) →
        tsupport Y ⊆ K := by
      intro Y hY
      refine closure_minimal (fun x hx => ?_) hKc.isClosed
      rw [Function.mem_support] at hx
      by_cases hxb : x = b
      · rw [hxb]; exact hbK
      · have hxG : σ ≤ G x := hY x hxb hx
        have hxΩ : x ∈ Ω := by
          by_contra hcon
          rw [hGoff x hcon] at hxG
          exact absurd hxG (not_le.mpr hσpos)
        by_cases hxK : x ∈ K₀
        · rw [hK]; exact Set.mem_union_left _ (Set.mem_union_left _ hxK)
        · exact absurd (hK₀ x hxΩ hxK) (not_lt.mpr hxG)
    have hY_V_supp : tsupport Y_V ⊆ K :=
      hsupp_of_ge (fun x hxb hx => by
        by_contra hcon
        exact hx (by rw [hY_V_of_ne x hxb, deriv_zero_of_lt (G x) (not_le.mp hcon)]))
    have hY_G_supp : tsupport Y_G ⊆ K :=
      hsupp_of_ge (fun x hxb hx => by
        by_contra hcon
        have h3 : deriv Ξ (G x) = 0 := deriv_zero_of_lt (G x) (not_le.mp hcon)
        exact hx (by rw [hY_G_of_ne x hxb, h3, mul_zero]))
    have hY_g_supp : tsupport Y_g ⊆ K :=
      hsupp_of_ge (fun x hxb hx => by
        by_contra hcon
        have h3 : deriv Ξ (G x) = 0 := deriv_zero_of_lt (G x) (not_le.mp hcon)
        exact hx (by rw [hY_g_of_ne x hxb, h3, mul_zero]))
    -- chart-wise `C¹`
    have chart_c1_comp : ∀ {Y : X → ℝ} (hY : ∀ x, x ≠ b → Y x = deriv Ξ (G x)) {y x : X}
        (hx : x ∈ (chartAt ℂ y).source) (hxb : x ≠ b) (hxΩ : x ∈ Ω),
        ContDiffAt ℝ 1 (Y ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) := by
      intro Y hY y x hx hxb hxΩ
      have hGc1 : ContDiffAt ℝ 1 (G ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) :=
        (Submission.HarmonicOnXAt_iff_chart (u := G) (x := x) (y := y) hx).mp
          (hG.2.1 x ⟨hxΩ, hxb⟩) |>.1.of_le (by norm_num)
      have hcomp := contDiffAt_chart_comp_of_contDiffAt hderivΞ hGc1
      refine hcomp.congr_of_eventuallyEq ?_
      have hcont : Filter.Tendsto (↑(chartAt ℂ y).symm : ℂ → X) (𝓝 ((chartAt ℂ y) x)) (𝓝 x) := by
        have h2 := ((chartAt ℂ y).continuousAt_symm ((chartAt ℂ y).map_source hx)).tendsto
        rwa [(chartAt ℂ y).left_inv hx] at h2
      filter_upwards [hcont.eventually (isOpen_compl_singleton.mem_nhds hxb)] with w hw
      show Y ((chartAt ℂ y).symm w) = deriv Ξ (G ((chartAt ℂ y).symm w))
      exact hY _ hw
    have hΞgc1 : ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
        ContDiffAt ℝ 1 (Ξg ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x) := by
      intro k
      refine contDiffAt_chart_of_support_and_pole hKc hKΩ hbK
        (fun y _ => contDiffAt_const) ?_ hΞg_eq_one hΞgsupp (E.y k)
      intro y x hx hxK hxb
      have hxΩ : x ∈ Ω := hKΩ hxK
      have hGc1 : ContDiffAt ℝ 1 (G ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) :=
        (Submission.HarmonicOnXAt_iff_chart (u := G) (x := x) (y := y) hx).mp
          (hG.2.1 x ⟨hxΩ, hxb⟩) |>.1.of_le (by norm_num)
      have hcomp := contDiffAt_chart_comp_of_contDiffAt (contDiff_stepCutoff σ (n := 1)) hGc1
      refine hcomp.congr_of_eventuallyEq ?_
      have hcont : Filter.Tendsto (↑(chartAt ℂ y).symm : ℂ → X) (𝓝 ((chartAt ℂ y) x)) (𝓝 x) := by
        have h2 := ((chartAt ℂ y).continuousAt_symm ((chartAt ℂ y).map_source hx)).tendsto
        rwa [(chartAt ℂ y).left_inv hx] at h2
      filter_upwards [hcont.eventually (isOpen_compl_singleton.mem_nhds hxb)] with w hw
      show Ξg ((chartAt ℂ y).symm w) = Ξ (G ((chartAt ℂ y).symm w))
      exact hΞg_of_ne _ hw
    have hThc1 : ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
        ContDiffAt ℝ 1 (Th ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x) := by
      intro k
      refine contDiffAt_chart_of_support_and_pole hKc hKΩ hbK
        (Φ := fun _ => cσ) (fun y _ => contDiffAt_const) ?_ hTh_eq hThsupp (E.y k)
      intro y x hx hxK hxb
      have hxΩ : x ∈ Ω := hKΩ hxK
      have hGc1 : ContDiffAt ℝ 1 (G ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) :=
        (Submission.HarmonicOnXAt_iff_chart (u := G) (x := x) (y := y) hx).mp
          (hG.2.1 x ⟨hxΩ, hxb⟩) |>.1.of_le (by norm_num)
      have hcomp := contDiffAt_chart_comp_of_contDiffAt (contDiff_thetaCutoff hσpos) hGc1
      refine hcomp.congr_of_eventuallyEq ?_
      have hcont : Filter.Tendsto (↑(chartAt ℂ y).symm : ℂ → X) (𝓝 ((chartAt ℂ y) x)) (𝓝 x) := by
        have h2 := ((chartAt ℂ y).continuousAt_symm ((chartAt ℂ y).map_source hx)).tendsto
        rwa [(chartAt ℂ y).left_inv hx] at h2
      filter_upwards [hcont.eventually (isOpen_compl_singleton.mem_nhds hxb)] with w hw
      show Th ((chartAt ℂ y).symm w) = θ (G ((chartAt ℂ y).symm w))
      exact hTh_of_ne _ hw
    have hY_V_c1 : ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
        ContDiffAt ℝ 1 (Y_V ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x) := by
      intro k
      refine contDiffAt_chart_of_support_and_pole hKc hKΩ hbK
        (Φ := fun _ => 0) (fun y _ => contDiffAt_const) ?_ hY_V_eq_zero hY_V_supp (E.y k)
      intro y x hx hxK hxb
      exact chart_c1_comp (Y := Y_V) hY_V_of_ne hx hxb (hKΩ hxK)
    have hY_G_c1 : ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
        ContDiffAt ℝ 1 (Y_G ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x) := by
      intro k
      refine contDiffAt_chart_of_support_and_pole hKc hKΩ hbK
        (Φ := fun _ => 0) (fun y _ => contDiffAt_const) ?_ hY_G_eq_zero hY_G_supp (E.y k)
      intro y x hx hxK hxb
      have hxΩ : x ∈ Ω := hKΩ hxK
      have hGc1 : ContDiffAt ℝ 1 (G ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) :=
        (Submission.HarmonicOnXAt_iff_chart (u := G) (x := x) (y := y) hx).mp
          (hG.2.1 x ⟨hxΩ, hxb⟩) |>.1.of_le (by norm_num)
      have hcomp := chart_c1_comp (Y := Y_V) hY_V_of_ne hx hxb hxΩ
      have hprod := hGc1.mul hcomp
      refine hprod.congr_of_eventuallyEq ?_
      have hcont : Filter.Tendsto (↑(chartAt ℂ y).symm : ℂ → X) (𝓝 ((chartAt ℂ y) x)) (𝓝 x) := by
        have h2 := ((chartAt ℂ y).continuousAt_symm ((chartAt ℂ y).map_source hx)).tendsto
        rwa [(chartAt ℂ y).left_inv hx] at h2
      filter_upwards [hcont.eventually (isOpen_compl_singleton.mem_nhds hxb)] with w hw
      simp only [Function.comp_apply, hY_G_of_ne _ hw, hY_V_of_ne _ hw]
    have hY_g_c1 : ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
        ContDiffAt ℝ 1 (Y_g ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x) := by
      intro k
      refine contDiffAt_chart_of_support_and_pole hKc hKΩ hbK
        (Φ := fun _ => 0) (fun y _ => contDiffAt_const) ?_ hY_g_eq_zero hY_g_supp (E.y k)
      intro y x hx hxK hxb
      by_cases hxa : x = a
      · have hev : (Y_g ∘ (chartAt ℂ y).symm) =ᶠ[𝓝 ((chartAt ℂ y) x)] 0 := by
          have hcont : Filter.Tendsto (↑(chartAt ℂ y).symm : ℂ → X) (𝓝 ((chartAt ℂ y) x)) (𝓝 a) := by
            have h2 := ((chartAt ℂ y).continuousAt_symm ((chartAt ℂ y).map_source hx)).tendsto
            rw [(chartAt ℂ y).left_inv hx] at h2
            simpa only [hxa] using h2
          filter_upwards [hcont.eventually hY_g_zero_a] with w hw
          exact hw
        exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev
      · have hxΩ : x ∈ Ω := hKΩ hxK
        have hxmem : x ∈ Ω \ {a} := ⟨hxΩ, by simpa using hxa⟩
        have hgc1 : ContDiffAt ℝ 1 (g ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) :=
          (Submission.HarmonicOnXAt_iff_chart (u := g) (x := x) (y := y) hx).mp
            (hg.2.1 x hxmem) |>.1.of_le (by norm_num)
        have hcomp := chart_c1_comp (Y := Y_V) hY_V_of_ne hx hxb hxΩ
        have hprod := hgc1.mul hcomp
        refine hprod.congr_of_eventuallyEq ?_
        have hcont : Filter.Tendsto (↑(chartAt ℂ y).symm : ℂ → X) (𝓝 ((chartAt ℂ y) x)) (𝓝 x) := by
          have h2 := ((chartAt ℂ y).continuousAt_symm ((chartAt ℂ y).map_source hx)).tendsto
          rwa [(chartAt ℂ y).left_inv hx] at h2
        filter_upwards [hcont.eventually (isOpen_compl_singleton.mem_nhds hxb)] with w hw
        simp only [Function.comp_apply, hY_g_of_ne _ hw, hY_V_of_ne _ hw]
    -- the growth data of the two Green functions
    have hgr_g : ∀ i : ι, ∃ (q : ℂ) (C : ℝ), 0 < C ∧
        ∀ z ∈ Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.s i), z ≠ q →
          ‖gradient (clampedPullback (E.y i) (E.ρ i) g) z‖ ≤ C / ‖z - q‖ :=
      exists_growth_data_clampedPullback_of_isGreenOn (E := E) E.ia hEya
        (fun i hi => E.ha_nmem i hi) hg hrA₀ hHA₀ (fun z hz _ => hexpA z hz)
    have hgr_G : ∀ i : ι, ∃ (q : ℂ) (C : ℝ), 0 < C ∧
        ∀ z ∈ Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.s i), z ≠ q →
          ‖gradient (clampedPullback (E.y i) (E.ρ i) G) z‖ ≤ C / ‖z - q‖ :=
      exists_growth_data_clampedPullback_of_isGreenOn (E := E) E.ib hEyb
        (fun i hi => E.hb_nmem i hi) hG hrB₀ hHB₀ (fun z hz _ => hexpB z hz)
    have hb_g : ∀ i : ι, i ≠ E.ia → ∃ K : ℝ, 0 ≤ K ∧
        ∀ z ∈ Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.σ i),
          ‖gradient (clampedPullback (E.y i) (E.ρ i) g) z‖ ≤ K := fun i hi =>
      exists_bound_gradient_clampedPullback_of_avoid hΩo ha hg (E.hσρ i) (E.htgt i) (E.hballΩ i)
        (E.ha_nmem i hi)
    have hb_G : ∀ i : ι, i ≠ E.ib → ∃ K : ℝ, 0 ≤ K ∧
        ∀ z ∈ Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.σ i),
          ‖gradient (clampedPullback (E.y i) (E.ρ i) G) z‖ ≤ K := fun i hi =>
      exists_bound_gradient_clampedPullback_of_avoid hΩo hb hG (E.hσρ i) (E.htgt i) (E.hballΩ i)
        (E.hb_nmem i hi)

    -- ## Step 6: the integrability certificates
    have mul_c1 : ∀ (i : ι) {Y : X → ℝ}, (∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
        ContDiffAt ℝ 1 (Y ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x)) →
        ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
          ContDiffAt ℝ 1 ((fun y => E.ψ i y * Y y) ∘ (chartAt ℂ (E.y k)).symm)
            ((chartAt ℂ (E.y k)) x) := by
      intro i Y hY k x hx
      have h1 : ContDiffAt ℝ 1 ((E.ψ i) ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x) :=
        hψc1 k i x hx
      have h2 : ContDiffAt ℝ 1 (Y ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x) := hY k x hx
      have hfun : ((fun y => E.ψ i y * Y y) ∘ (chartAt ℂ (E.y k)).symm)
          = ((E.ψ i) ∘ (chartAt ℂ (E.y k)).symm) * (Y ∘ (chartAt ℂ (E.y k)).symm) := rfl
      rw [hfun]
      exact h1.mul h2
    have supp_prod : ∀ (i : ι) {Y : X → ℝ}, tsupport (fun y => E.ψ i y * Y y) ⊆
        Submission.chartBall (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)) (E.y i)) (E.s i) :=
      fun i Y x hx => E.hψsupp i (tsupport_mul_subset_left hx)
    have weight_hW : ∀ (i : ι) {Y : X → ℝ}, (∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
        ContDiffAt ℝ 1 (Y ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x)) →
        Continuous (clampedPullback (E.y i) (E.σ i) (fun y => E.ψ i y * Y y)) ∧
        HasCompactSupport (clampedPullback (E.y i) (E.σ i) (fun y => E.ψ i y * Y y)) := by
      intro i Y hY
      obtain ⟨h1, h2⟩ := Work.Drive.GreenRung.contDiff_clampedPullback_hasCompactSupport
        (x₀ := E.y i) (u := fun y => E.ψ i y * Y y) (ρ := E.σ i) (ρ₀ := E.s i)
        (lt_trans (E.hspos i) (E.hsσ i)) (le_of_lt (E.hspos i)) (E.hsσ i)
        ((Metric.ball_subset_ball (le_of_lt (E.hσρ i))).trans (E.htgt i))
        (mul_c1 i hY i) (fun x hx => (E.hψsupp i (tsupport_mul_subset_left hx)).2)
      exact ⟨h1.continuous, h2⟩
    have hae_g : ∀ i : ι, ∀ᵐ z ∂(volume : Measure ℂ),
        DifferentiableAt ℝ (clampedPullback (E.y i) (E.ρ i) g) z := by
      intro i
      refine clampedPullback_differentiableAt_ae_of_off' (E.htgt i)
        (z₀ := (chartAt ℂ (E.y i)) a) ?_
      intro z hz hz0
      have hright : (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)).symm z) = z :=
        (chartAt ℂ (E.y i)).right_inv (E.htgt i hz)
      have hsrc : (chartAt ℂ (E.y i)).symm z ∈ (chartAt ℂ (E.y i)).source :=
        (chartAt ℂ (E.y i)).map_target (E.htgt i hz)
      have hxΩ : (chartAt ℂ (E.y i)).symm z ∈ Ω :=
        E.hballΩ i ⟨hsrc, by
          show (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)).symm z) ∈
            Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.ρ i)
          rw [hright]; exact hz⟩
      have hxa : (chartAt ℂ (E.y i)).symm z ≠ a := by
        intro hcon
        exact hz0 (by rw [← hright, hcon])
      have hiff := (Submission.HarmonicOnXAt_iff_chart (u := g) (x := (chartAt ℂ (E.y i)).symm z)
        (y := E.y i) hsrc).mp (hg.2.1 _ ⟨hxΩ, hxa⟩)
      have h2 : DifferentiableAt ℝ (fun w : ℂ => g ((chartAt ℂ (E.y i)).symm w))
          ((chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)).symm z)) := by
        have hc : ContDiffAt ℝ 1 (fun w : ℂ => g ((chartAt ℂ (E.y i)).symm w))
            ((chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)).symm z)) := hiff.1.of_le (by norm_num)
        exact hc.differentiableAt (by norm_num)
      rwa [hright] at h2
    have hae_G : ∀ i : ι, ∀ᵐ z ∂(volume : Measure ℂ),
        DifferentiableAt ℝ (clampedPullback (E.y i) (E.ρ i) G) z := by
      intro i
      refine clampedPullback_differentiableAt_ae_of_off' (E.htgt i)
        (z₀ := (chartAt ℂ (E.y i)) b) ?_
      intro z hz hz0
      have hright : (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)).symm z) = z :=
        (chartAt ℂ (E.y i)).right_inv (E.htgt i hz)
      have hsrc : (chartAt ℂ (E.y i)).symm z ∈ (chartAt ℂ (E.y i)).source :=
        (chartAt ℂ (E.y i)).map_target (E.htgt i hz)
      have hxΩ : (chartAt ℂ (E.y i)).symm z ∈ Ω :=
        E.hballΩ i ⟨hsrc, by
          show (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)).symm z) ∈
            Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.ρ i)
          rw [hright]; exact hz⟩
      have hxb : (chartAt ℂ (E.y i)).symm z ≠ b := by
        intro hcon
        exact hz0 (by rw [← hright, hcon])
      have hiff := (Submission.HarmonicOnXAt_iff_chart (u := G) (x := (chartAt ℂ (E.y i)).symm z)
        (y := E.y i) hsrc).mp (hG.2.1 _ ⟨hxΩ, hxb⟩)
      have h2 : DifferentiableAt ℝ (fun w : ℂ => G ((chartAt ℂ (E.y i)).symm w))
          ((chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)).symm z)) := by
        have hc : ContDiffAt ℝ 1 (fun w : ℂ => G ((chartAt ℂ (E.y i)).symm w))
            ((chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)).symm z)) := hiff.1.of_le (by norm_num)
        exact hc.differentiableAt (by norm_num)
      rwa [hright] at h2
    have hae_Ξg : ∀ i : ι, ∀ᵐ z ∂(volume : Measure ℂ),
        DifferentiableAt ℝ (clampedPullback (E.y i) (E.ρ i) Ξg) z := by
      intro i
      refine Work.Kernel.clampedPullback_differentiableAt_ae_of_differentiableOn (E.htgt i) ?_
      intro z hz
      have hright : (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)).symm z) = z :=
        (chartAt ℂ (E.y i)).right_inv (E.htgt i hz)
      have hsrc : (chartAt ℂ (E.y i)).symm z ∈ (chartAt ℂ (E.y i)).source :=
        (chartAt ℂ (E.y i)).map_target (E.htgt i hz)
      have h2 : ContDiffAt ℝ 1 (Ξg ∘ (chartAt ℂ (E.y i)).symm)
          ((chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)).symm z)) := hΞgc1 i _ hsrc
      have h3 : ContDiffAt ℝ 1 (Ξg ∘ (chartAt ℂ (E.y i)).symm) z := by rwa [hright] at h2
      exact h3.differentiableAt (by norm_num)
    -- cert1 : `ψᵢ Ξg` against `(g, G)`
    have cert1 : ∀ i : ι, PairIntegrable (E.y i) (E.ρ i) (E.σ i) (fun y => E.ψ i y * Ξg y) g G := by
      intro i
      obtain ⟨q, C, hCpos, hC⟩ := hgr_g i
      have hW := weight_hW i hΞgc1
      have hsupp := supp_prod i (Y := Ξg)
      by_cases hi : i = E.ia
      · obtain ⟨Kg, hKgnn, hKg⟩ := hb_G i (by rw [hi]; exact hiaib)
        refine Work.Kernel.PS.pairIntegrable_of_support_growth' (x := E.y i) (ρ := E.ρ i)
          (σ := E.σ i) (W := fun y => E.ψ i y * Ξg y) (f := g) (χ := G) (p := q) (C := C) (K := Kg)
          hCpos.le hKgnn hW.1 hW.2 ?_ ?_ ?_
        · filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton q)] with z hzq hz
          have hzball : z ∈ Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.s i) :=
            Work.Kernel.PS.tsupport_clampedPullback_subset_closedBall' ((Metric.ball_subset_ball (le_of_lt (E.hσρ i))).trans (E.htgt i)) hsupp hz
          exact hC z hzball (by simpa using hzq)
        · filter_upwards with z hz
          have hzball : z ∈ Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.s i) :=
            Work.Kernel.PS.tsupport_clampedPullback_subset_closedBall' ((Metric.ball_subset_ball (le_of_lt (E.hσρ i))).trans (E.htgt i)) hsupp hz
          exact hKg z (Metric.closedBall_subset_ball (E.hsσ i) hzball)
        · exact (Work.Kernel.PS.aeStronglyMeasurable_gradient_clampedPullback' (E.htgt i)
            (u := g) (x₀ := a) (fun x hx hxa =>
              (Submission.HarmonicOnXAt_iff_chart (u := g) (x := x) (y := E.y i) hx.1).mp
                (hg.2.1 x ⟨E.hballΩ i hx, hxa⟩) |>.1.of_le (by norm_num))).inner
            (Work.Kernel.PS.aeStronglyMeasurable_gradient_clampedPullback' (E.htgt i)
              (u := G) (x₀ := b) (fun x hx hxb =>
                (Submission.HarmonicOnXAt_iff_chart (u := G) (x := x) (y := E.y i) hx.1).mp
                  (hG.2.1 x ⟨E.hballΩ i hx, hxb⟩) |>.1.of_le (by norm_num)))
      · by_cases hib : i = E.ib
        · obtain ⟨q', C', hC'pos, hC'⟩ := hgr_G i
          obtain ⟨Kg, hKgnn, hKg⟩ := hb_g i (by rw [hib]; exact hiaib.symm)
          have hG1 : PairIntegrable (E.y i) (E.ρ i) (E.σ i) (fun y => E.ψ i y * Ξg y) G g := by
            refine Work.Kernel.PS.pairIntegrable_of_support_growth' (x := E.y i) (ρ := E.ρ i)
              (σ := E.σ i) (W := fun y => E.ψ i y * Ξg y) (f := G) (χ := g)
              (p := q') (C := C') (K := Kg) hC'pos.le hKgnn hW.1 hW.2 ?_ ?_ ?_
            · filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton q')] with z hzq hz
              have hzball : z ∈ Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.s i) :=
                Work.Kernel.PS.tsupport_clampedPullback_subset_closedBall' ((Metric.ball_subset_ball (le_of_lt (E.hσρ i))).trans (E.htgt i)) hsupp hz
              exact hC' z hzball (by simpa using hzq)
            · filter_upwards with z hz
              have hzball : z ∈ Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.s i) :=
                Work.Kernel.PS.tsupport_clampedPullback_subset_closedBall' ((Metric.ball_subset_ball (le_of_lt (E.hσρ i))).trans (E.htgt i)) hsupp hz
              exact hKg z (Metric.closedBall_subset_ball (E.hsσ i) hzball)
            · exact (Work.Kernel.PS.aeStronglyMeasurable_gradient_clampedPullback' (E.htgt i)
                (u := G) (x₀ := b) (fun x hx hxb =>
                  (Submission.HarmonicOnXAt_iff_chart (u := G) (x := x) (y := E.y i) hx.1).mp
                    (hG.2.1 x ⟨E.hballΩ i hx, hxb⟩) |>.1.of_le (by norm_num))).inner
                (Work.Kernel.PS.aeStronglyMeasurable_gradient_clampedPullback' (E.htgt i)
                  (u := g) (x₀ := a) (fun x hx hxa =>
                    (Submission.HarmonicOnXAt_iff_chart (u := g) (x := x) (y := E.y i) hx.1).mp
                      (hg.2.1 x ⟨E.hballΩ i hx, hxa⟩) |>.1.of_le (by norm_num)))
          exact hG1.comm
        · obtain ⟨Kg, hKgnn, hKg⟩ := hb_G i hib
          refine Work.Kernel.PS.pairIntegrable_of_support_growth' (x := E.y i) (ρ := E.ρ i)
            (σ := E.σ i) (W := fun y => E.ψ i y * Ξg y) (f := g) (χ := G) (p := q) (C := C) (K := Kg)
            hCpos.le hKgnn hW.1 hW.2 ?_ ?_ ?_
          · filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton q)] with z hzq hz
            have hzball : z ∈ Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.s i) :=
              Work.Kernel.PS.tsupport_clampedPullback_subset_closedBall' ((Metric.ball_subset_ball (le_of_lt (E.hσρ i))).trans (E.htgt i)) hsupp hz
            exact hC z hzball (by simpa using hzq)
          · filter_upwards with z hz
            have hzball : z ∈ Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.s i) :=
              Work.Kernel.PS.tsupport_clampedPullback_subset_closedBall' ((Metric.ball_subset_ball (le_of_lt (E.hσρ i))).trans (E.htgt i)) hsupp hz
            exact hKg z (Metric.closedBall_subset_ball (E.hsσ i) hzball)
          · exact (Work.Kernel.PS.aeStronglyMeasurable_gradient_clampedPullback' (E.htgt i)
              (u := g) (x₀ := a) (fun x hx hxa =>
                (Submission.HarmonicOnXAt_iff_chart (u := g) (x := x) (y := E.y i) hx.1).mp
                  (hg.2.1 x ⟨E.hballΩ i hx, hxa⟩) |>.1.of_le (by norm_num))).inner
              (Work.Kernel.PS.aeStronglyMeasurable_gradient_clampedPullback' (E.htgt i)
                (u := G) (x₀ := b) (fun x hx hxb =>
                  (Submission.HarmonicOnXAt_iff_chart (u := G) (x := x) (y := E.y i) hx.1).mp
                    (hG.2.1 x ⟨E.hballΩ i hx, hxb⟩) |>.1.of_le (by norm_num)))

    -- cert2 : `ψᵢ Y_G` against `(g, G)`
    have cert2 : ∀ i : ι, PairIntegrable (E.y i) (E.ρ i) (E.σ i) (fun y => E.ψ i y * Y_G y) g G := by
      intro i
      obtain ⟨q, C, hCpos, hC⟩ := hgr_g i
      have hW := weight_hW i hY_G_c1
      have hsupp := supp_prod i (Y := Y_G)
      by_cases hi : i = E.ia
      · obtain ⟨Kg, hKgnn, hKg⟩ := hb_G i (by rw [hi]; exact hiaib)
        refine Work.Kernel.PS.pairIntegrable_of_support_growth' (x := E.y i) (ρ := E.ρ i)
          (σ := E.σ i) (W := fun y => E.ψ i y * Y_G y) (f := g) (χ := G) (p := q) (C := C) (K := Kg)
          hCpos.le hKgnn hW.1 hW.2 ?_ ?_ ?_
        · filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton q)] with z hzq hz
          have hzball : z ∈ Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.s i) :=
            Work.Kernel.PS.tsupport_clampedPullback_subset_closedBall' ((Metric.ball_subset_ball (le_of_lt (E.hσρ i))).trans (E.htgt i)) hsupp hz
          exact hC z hzball (by simpa using hzq)
        · filter_upwards with z hz
          have hzball : z ∈ Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.s i) :=
            Work.Kernel.PS.tsupport_clampedPullback_subset_closedBall' ((Metric.ball_subset_ball (le_of_lt (E.hσρ i))).trans (E.htgt i)) hsupp hz
          exact hKg z (Metric.closedBall_subset_ball (E.hsσ i) hzball)
        · exact (Work.Kernel.PS.aeStronglyMeasurable_gradient_clampedPullback' (E.htgt i)
            (u := g) (x₀ := a) (fun x hx hxa =>
              (Submission.HarmonicOnXAt_iff_chart (u := g) (x := x) (y := E.y i) hx.1).mp
                (hg.2.1 x ⟨E.hballΩ i hx, hxa⟩) |>.1.of_le (by norm_num))).inner
            (Work.Kernel.PS.aeStronglyMeasurable_gradient_clampedPullback' (E.htgt i)
              (u := G) (x₀ := b) (fun x hx hxb =>
                (Submission.HarmonicOnXAt_iff_chart (u := G) (x := x) (y := E.y i) hx.1).mp
                  (hG.2.1 x ⟨E.hballΩ i hx, hxb⟩) |>.1.of_le (by norm_num)))
      · by_cases hib : i = E.ib
        · obtain ⟨q', C', hC'pos, hC'⟩ := hgr_G i
          obtain ⟨Kg, hKgnn, hKg⟩ := hb_g i (by rw [hib]; exact hiaib.symm)
          have hG1 : PairIntegrable (E.y i) (E.ρ i) (E.σ i) (fun y => E.ψ i y * Y_G y) G g := by
            refine Work.Kernel.PS.pairIntegrable_of_support_growth' (x := E.y i) (ρ := E.ρ i)
              (σ := E.σ i) (W := fun y => E.ψ i y * Y_G y) (f := G) (χ := g)
              (p := q') (C := C') (K := Kg) hC'pos.le hKgnn hW.1 hW.2 ?_ ?_ ?_
            · filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton q')] with z hzq hz
              have hzball : z ∈ Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.s i) :=
                Work.Kernel.PS.tsupport_clampedPullback_subset_closedBall' ((Metric.ball_subset_ball (le_of_lt (E.hσρ i))).trans (E.htgt i)) hsupp hz
              exact hC' z hzball (by simpa using hzq)
            · filter_upwards with z hz
              have hzball : z ∈ Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.s i) :=
                Work.Kernel.PS.tsupport_clampedPullback_subset_closedBall' ((Metric.ball_subset_ball (le_of_lt (E.hσρ i))).trans (E.htgt i)) hsupp hz
              exact hKg z (Metric.closedBall_subset_ball (E.hsσ i) hzball)
            · exact (Work.Kernel.PS.aeStronglyMeasurable_gradient_clampedPullback' (E.htgt i)
                (u := G) (x₀ := b) (fun x hx hxb =>
                  (Submission.HarmonicOnXAt_iff_chart (u := G) (x := x) (y := E.y i) hx.1).mp
                    (hG.2.1 x ⟨E.hballΩ i hx, hxb⟩) |>.1.of_le (by norm_num))).inner
                (Work.Kernel.PS.aeStronglyMeasurable_gradient_clampedPullback' (E.htgt i)
                  (u := g) (x₀ := a) (fun x hx hxa =>
                    (Submission.HarmonicOnXAt_iff_chart (u := g) (x := x) (y := E.y i) hx.1).mp
                      (hg.2.1 x ⟨E.hballΩ i hx, hxa⟩) |>.1.of_le (by norm_num)))
          exact hG1.comm
        · obtain ⟨Kg, hKgnn, hKg⟩ := hb_G i hib
          refine Work.Kernel.PS.pairIntegrable_of_support_growth' (x := E.y i) (ρ := E.ρ i)
            (σ := E.σ i) (W := fun y => E.ψ i y * Y_G y) (f := g) (χ := G) (p := q) (C := C) (K := Kg)
            hCpos.le hKgnn hW.1 hW.2 ?_ ?_ ?_
          · filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton q)] with z hzq hz
            have hzball : z ∈ Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.s i) :=
              Work.Kernel.PS.tsupport_clampedPullback_subset_closedBall' ((Metric.ball_subset_ball (le_of_lt (E.hσρ i))).trans (E.htgt i)) hsupp hz
            exact hC z hzball (by simpa using hzq)
          · filter_upwards with z hz
            have hzball : z ∈ Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.s i) :=
              Work.Kernel.PS.tsupport_clampedPullback_subset_closedBall' ((Metric.ball_subset_ball (le_of_lt (E.hσρ i))).trans (E.htgt i)) hsupp hz
            exact hKg z (Metric.closedBall_subset_ball (E.hsσ i) hzball)
          · exact (Work.Kernel.PS.aeStronglyMeasurable_gradient_clampedPullback' (E.htgt i)
              (u := g) (x₀ := a) (fun x hx hxa =>
                (Submission.HarmonicOnXAt_iff_chart (u := g) (x := x) (y := E.y i) hx.1).mp
                  (hg.2.1 x ⟨E.hballΩ i hx, hxa⟩) |>.1.of_le (by norm_num))).inner
              (Work.Kernel.PS.aeStronglyMeasurable_gradient_clampedPullback' (E.htgt i)
                (u := G) (x₀ := b) (fun x hx hxb =>
                  (Submission.HarmonicOnXAt_iff_chart (u := G) (x := x) (y := E.y i) hx.1).mp
                    (hG.2.1 x ⟨E.hballΩ i hx, hxb⟩) |>.1.of_le (by norm_num)))

    -- cert3 : `ψᵢ Y_V` against `(G, G)` (the "level" certificate)
    have cert3 : ∀ i : ι, PairIntegrable (E.y i) (E.ρ i) (E.σ i) (fun y => E.ψ i y * Y_V y) G G := by
      intro i
      have hW := weight_hW i hY_V_c1
      have hsupp := supp_prod i (Y := Y_V)
      have hsrc : tsupport (fun y => E.ψ i y * Y_V y) ⊆ (chartAt ℂ (E.y i)).source :=
        fun x hx => (Submission.mem_chartBall.mp (hsupp hx)).1
      have hsuppΩ : tsupport (fun y => E.ψ i y * Y_V y) ⊆ Ω :=
        hsupp.trans (fun x hx =>
          E.hballΩ i (Submission.mem_chartBall.mpr
            ⟨(Submission.mem_chartBall.mp hx).1,
              Metric.ball_subset_ball (le_of_lt (lt_trans (E.hsσ i) (E.hσρ i)))
                (Submission.mem_chartBall.mp hx).2⟩))
      have hsuppρ : tsupport (fun y => E.ψ i y * Y_V y) ⊆
          Submission.chartBall (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)) (E.y i)) (E.ρ i) :=
        fun x hx => Submission.mem_chartBall.mpr
          ⟨(Submission.mem_chartBall.mp (hsupp hx)).1,
            Metric.ball_subset_ball (le_of_lt (lt_trans (E.hsσ i) (E.hσρ i)))
              (Submission.mem_chartBall.mp (hsupp hx)).2⟩
      have hsupp_b : b ∉ tsupport (fun y => E.ψ i y * Y_V y) := by
        intro hmem
        have h1 : (fun y => E.ψ i y * Y_V y) =ᶠ[𝓝 b] 0 := by
          filter_upwards [hY_V_eq_zero] with x hx
          rw [hx]
          simp
        obtain ⟨U, hUsub, hUopen, hbU⟩ := mem_nhds_iff.mp h1
        obtain ⟨x, hx, hxne⟩ := (mem_closure_iff_nhds.mp hmem) U (hUopen.mem_nhds hbU)
        exact hxne (hUsub hx)
      have hWcs : HasCompactSupport (fun y => E.ψ i y * Y_V y) :=
        IsCompact.of_isClosed_subset
          (Submission.isCompact_chartClosedBall
            (((Metric.closedBall_subset_ball (E.hsσ i)).trans
              (Metric.ball_subset_ball (le_of_lt (E.hσρ i)))).trans (E.htgt i)))
          (isClosed_tsupport _)
          (fun x hx => Submission.chartBall_subset_chartClosedBall _ _ _ (hsupp hx))
      obtain ⟨B, hBnn, hB⟩ := exists_bound_gradient_clampedPullback_on_support hb hG (E.htgt i)
        hWcs hsrc hsuppΩ hsupp_b hsuppρ
      have hmeasG : AEStronglyMeasurable (fun z : ℂ =>
          gradient (clampedPullback (E.y i) (E.ρ i) G) z) volume :=
        Work.Kernel.PS.aeStronglyMeasurable_gradient_clampedPullback' (E.htgt i) (u := G) (x₀ := b)
          (fun x hx hxb => (Submission.HarmonicOnXAt_iff_chart (u := G) (x := x) (y := E.y i) hx.1).mp
            (hG.2.1 x ⟨E.hballΩ i hx, hxb⟩) |>.1.of_le (by norm_num))
      refine pairIntegrable_of_majorant (Φ := fun z => B * B * ‖clampedPullback (E.y i) (E.σ i)
        (fun y => E.ψ i y * Y_V y) z‖) ?_ ?_ ?_
      · have hint : Integrable (fun z : ℂ =>
            ‖clampedPullback (E.y i) (E.σ i) (fun y => E.ψ i y * Y_V y) z‖) :=
          hW.1.norm.integrable_of_hasCompactSupport hW.2.norm
        exact hint.const_mul (B * B)
      · exact hW.1.aestronglyMeasurable.mul
          (AEStronglyMeasurable.inner (𝕜 := ℝ) hmeasG hmeasG)
      · filter_upwards [hB] with z hzB
        by_cases hz0 : clampedPullback (E.y i) (E.σ i) (fun y => E.ψ i y * Y_V y) z = 0
        · simp [hz0]
        · have hzs : z ∈ tsupport (clampedPullback (E.y i) (E.σ i) (fun y => E.ψ i y * Y_V y)) :=
            subset_tsupport _ (Function.mem_support.mpr hz0)
          have hsub : ∀ z, clampedPullback (E.y i) (E.σ i) (fun y => E.ψ i y * Y_V y) z ≠ 0 →
              clampedPullback (E.y i) (E.ρ i) (fun y => E.ψ i y * Y_V y) z ≠ 0 := by
            intro z hz
            have hzball : z ∈ Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.σ i) := by
              by_contra hc
              exact hz (clampedPullback_eq_zero_of_notMem_ball hc)
            rw [clampedPullback_apply_of_mem
              (Metric.ball_subset_ball (le_of_lt (E.hσρ i)) hzball)]
            rwa [clampedPullback_apply_of_mem hzball] at hz
          have h2 : ‖gradient (clampedPullback (E.y i) (E.ρ i) G) z‖ ≤ B :=
            hzB (closure_mono hsub hzs)
          calc ‖clampedPullback (E.y i) (E.σ i) (fun y => E.ψ i y * Y_V y) z *
                inner (𝕜 := ℝ) (gradient (clampedPullback (E.y i) (E.ρ i) G) z)
                  (gradient (clampedPullback (E.y i) (E.ρ i) G) z)‖
              = ‖clampedPullback (E.y i) (E.σ i) (fun y => E.ψ i y * Y_V y) z‖ *
                ‖gradient (clampedPullback (E.y i) (E.ρ i) G) z‖ ^ 2 := by
                rw [norm_mul, real_inner_self_eq_norm_sq, norm_pow, norm_norm]
            _ ≤ ‖clampedPullback (E.y i) (E.σ i) (fun y => E.ψ i y * Y_V y) z‖ * (B * B) := by
                refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
                simpa only [pow_two] using pow_le_pow_left₀ (norm_nonneg _) h2 2
            _ = B * B * ‖clampedPullback (E.y i) (E.σ i) (fun y => E.ψ i y * Y_V y) z‖ := by ring
    -- cert4 : `ψᵢ Y_g` against `(G, G)` (the "collar" certificate)
    have cert4 : ∀ i : ι, PairIntegrable (E.y i) (E.ρ i) (E.σ i) (fun y => E.ψ i y * Y_g y) G G := by
      intro i
      have hW := weight_hW i hY_g_c1
      have hsupp := supp_prod i (Y := Y_g)
      have hsrc : tsupport (fun y => E.ψ i y * Y_g y) ⊆ (chartAt ℂ (E.y i)).source :=
        fun x hx => (Submission.mem_chartBall.mp (hsupp hx)).1
      have hsuppΩ : tsupport (fun y => E.ψ i y * Y_g y) ⊆ Ω :=
        hsupp.trans (fun x hx =>
          E.hballΩ i (Submission.mem_chartBall.mpr
            ⟨(Submission.mem_chartBall.mp hx).1,
              Metric.ball_subset_ball (le_of_lt (lt_trans (E.hsσ i) (E.hσρ i)))
                (Submission.mem_chartBall.mp hx).2⟩))
      have hsuppρ : tsupport (fun y => E.ψ i y * Y_g y) ⊆
          Submission.chartBall (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)) (E.y i)) (E.ρ i) :=
        fun x hx => Submission.mem_chartBall.mpr
          ⟨(Submission.mem_chartBall.mp (hsupp hx)).1,
            Metric.ball_subset_ball (le_of_lt (lt_trans (E.hsσ i) (E.hσρ i)))
              (Submission.mem_chartBall.mp (hsupp hx)).2⟩
      have hsupp_b : b ∉ tsupport (fun y => E.ψ i y * Y_g y) := by
        intro hmem
        have h1 : (fun y => E.ψ i y * Y_g y) =ᶠ[𝓝 b] 0 := by
          filter_upwards [hY_g_eq_zero] with x hx
          rw [hx]
          simp
        obtain ⟨U, hUsub, hUopen, hbU⟩ := mem_nhds_iff.mp h1
        obtain ⟨x, hx, hxne⟩ := (mem_closure_iff_nhds.mp hmem) U (hUopen.mem_nhds hbU)
        exact hxne (hUsub hx)
      have hWcs : HasCompactSupport (fun y => E.ψ i y * Y_g y) :=
        IsCompact.of_isClosed_subset
          (Submission.isCompact_chartClosedBall
            (((Metric.closedBall_subset_ball (E.hsσ i)).trans
              (Metric.ball_subset_ball (le_of_lt (E.hσρ i)))).trans (E.htgt i)))
          (isClosed_tsupport _)
          (fun x hx => Submission.chartBall_subset_chartClosedBall _ _ _ (hsupp hx))
      obtain ⟨B, hBnn, hB⟩ := exists_bound_gradient_clampedPullback_on_support hb hG (E.htgt i)
        hWcs hsrc hsuppΩ hsupp_b hsuppρ
      have hmeasG : AEStronglyMeasurable (fun z : ℂ =>
          gradient (clampedPullback (E.y i) (E.ρ i) G) z) volume :=
        Work.Kernel.PS.aeStronglyMeasurable_gradient_clampedPullback' (E.htgt i) (u := G) (x₀ := b)
          (fun x hx hxb => (Submission.HarmonicOnXAt_iff_chart (u := G) (x := x) (y := E.y i) hx.1).mp
            (hG.2.1 x ⟨E.hballΩ i hx, hxb⟩) |>.1.of_le (by norm_num))
      refine pairIntegrable_of_majorant (Φ := fun z => B * B * ‖clampedPullback (E.y i) (E.σ i)
        (fun y => E.ψ i y * Y_g y) z‖) ?_ ?_ ?_
      · have hint : Integrable (fun z : ℂ =>
            ‖clampedPullback (E.y i) (E.σ i) (fun y => E.ψ i y * Y_g y) z‖) :=
          hW.1.norm.integrable_of_hasCompactSupport hW.2.norm
        exact hint.const_mul (B * B)
      · exact hW.1.aestronglyMeasurable.mul
          (AEStronglyMeasurable.inner (𝕜 := ℝ) hmeasG hmeasG)
      · filter_upwards [hB] with z hzB
        by_cases hz0 : clampedPullback (E.y i) (E.σ i) (fun y => E.ψ i y * Y_g y) z = 0
        · simp [hz0]
        · have hzs : z ∈ tsupport (clampedPullback (E.y i) (E.σ i) (fun y => E.ψ i y * Y_g y)) :=
            subset_tsupport _ (Function.mem_support.mpr hz0)
          have hsub : ∀ z, clampedPullback (E.y i) (E.σ i) (fun y => E.ψ i y * Y_g y) z ≠ 0 →
              clampedPullback (E.y i) (E.ρ i) (fun y => E.ψ i y * Y_g y) z ≠ 0 := by
            intro z hz
            have hzball : z ∈ Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.σ i) := by
              by_contra hc
              exact hz (clampedPullback_eq_zero_of_notMem_ball hc)
            rw [clampedPullback_apply_of_mem
              (Metric.ball_subset_ball (le_of_lt (E.hσρ i)) hzball)]
            rwa [clampedPullback_apply_of_mem hzball] at hz
          have h2 : ‖gradient (clampedPullback (E.y i) (E.ρ i) G) z‖ ≤ B :=
            hzB (closure_mono hsub hzs)
          calc ‖clampedPullback (E.y i) (E.σ i) (fun y => E.ψ i y * Y_g y) z *
                inner (𝕜 := ℝ) (gradient (clampedPullback (E.y i) (E.ρ i) G) z)
                  (gradient (clampedPullback (E.y i) (E.ρ i) G) z)‖
              = ‖clampedPullback (E.y i) (E.σ i) (fun y => E.ψ i y * Y_g y) z‖ *
                ‖gradient (clampedPullback (E.y i) (E.ρ i) G) z‖ ^ 2 := by
                rw [norm_mul, real_inner_self_eq_norm_sq, norm_pow, norm_norm]
            _ ≤ ‖clampedPullback (E.y i) (E.σ i) (fun y => E.ψ i y * Y_g y) z‖ * (B * B) := by
                refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
                simpa only [pow_two] using pow_le_pow_left₀ (norm_nonneg _) h2 2
            _ = B * B * ‖clampedPullback (E.y i) (E.σ i) (fun y => E.ψ i y * Y_g y) z‖ := by ring

    -- ## Step 7: the four pole identities and the expansions of `A` and `B`
    have pairing_weight_add' : ∀ {W W' : ι → X → ℝ} {f g : X → ℝ},
        (∀ i, PairIntegrable (E.y i) (E.ρ i) (E.σ i) (W i) f g) →
        (∀ i, PairIntegrable (E.y i) (E.ρ i) (E.σ i) (W' i) f g) →
        pairing E.y E.ρ E.σ (fun i => W i + W' i) f g
          = pairing E.y E.ρ E.σ W f g + pairing E.y E.ρ E.σ W' f g := by
      intro W W' f g h1 h2
      simp only [pairing]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => pairTerm_weight_add (h1 i) (h2 i)
    have pairing_comp_right' : ∀ {ψ : ι → X → ℝ} {f g : X → ℝ} {Φ : ℝ → ℝ},
        Φ 0 = 0 → Differentiable ℝ Φ →
        (∀ i, ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ (clampedPullback (E.y i) (E.ρ i) g) z) →
        pairing E.y E.ρ E.σ ψ f (fun x => Φ (g x))
          = pairing E.y E.ρ E.σ (fun i x => ψ i x * deriv Φ (g x)) f g := by
      intro ψ f g Φ hΦ0 hΦd hd
      simp only [pairing]
      exact Finset.sum_congr rfl fun i _ => pairTerm_comp_right (E.hσρ i) hΦ0 hΦd (hd i)
    have pairing_leibniz'' : ∀ {W' f g : X → ℝ},
        (∀ i, PairIntegrable (E.y i) (E.ρ i) (E.σ i) (E.ψ i) f (W' * g)) →
        (∀ i, PairIntegrable (E.y i) (E.ρ i) (E.σ i) (fun x => E.ψ i x * W' x) f g) →
        (∀ i, PairIntegrable (E.y i) (E.ρ i) (E.σ i) (fun x => E.ψ i x * g x) f W') →
        (∀ i, ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ (clampedPullback (E.y i) (E.ρ i) f) z) →
        (∀ i, ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ (clampedPullback (E.y i) (E.ρ i) g) z) →
        (∀ i, ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ (clampedPullback (E.y i) (E.ρ i) W') z) →
        pairing E.y E.ρ E.σ E.ψ f (W' * g)
          = pairing E.y E.ρ E.σ (fun i x => E.ψ i x * W' x) f g
            + pairing E.y E.ρ E.σ (fun i x => E.ψ i x * g x) f W' := by
      intro W' f g h1 h2 h3 hf hg hW'
      simp only [pairing]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ =>
        pairTerm_leibniz (E.hσρ i) (E.htgt i) (h1 i) (h2 i) (h3 i) (hf i) (hg i) (hW' i)
    have weight_ae : ∀ {W W' : ι → X → ℝ} {q : X},
        (htgt : ∀ i, Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.σ i) ⊆ (chartAt ℂ (E.y i)).target) →
        (∀ i y, y ≠ q → W i y = W' i y) →
        ∀ i, clampedPullback (E.y i) (E.σ i) (W i)
          =ᵐ[volume] clampedPullback (E.y i) (E.σ i) (W' i) := by
      intro W W' q htgt h i
      have h1 : ∀ z, z ≠ (chartAt ℂ (E.y i)) q →
          clampedPullback (E.y i) (E.σ i) (W i) z = clampedPullback (E.y i) (E.σ i) (W' i) z := by
        intro z hz
        by_cases hb : z ∈ Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.σ i)
        · have hx : (chartAt ℂ (E.y i)).symm z ≠ q := by
            intro hcon
            exact hz (by rw [← hcon]; exact ((chartAt ℂ (E.y i)).right_inv (htgt i hb)).symm)
          rw [clampedPullback_apply_of_mem hb, clampedPullback_apply_of_mem hb, h i _ hx]
        · rw [clampedPullback_eq_zero_of_notMem_ball hb, clampedPullback_eq_zero_of_notMem_ball hb]
      filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr
        (measure_singleton ((chartAt ℂ (E.y i)) q))] with z hz
      exact h1 z (by simpa using hz)
    have hΞgdiff : ∀ k, Work.Drive.ChartDiff (chartAt ℂ (E.y k)) Ξg Ω :=
      fun k x hx => (hΞgc1 k x hx.2).differentiableAt (by norm_num)
    have hThdiff : ∀ k, Work.Drive.ChartDiff (chartAt ℂ (E.y k)) Th Ω :=
      fun k x hx => (hThc1 k x hx.2).differentiableAt (by norm_num)
    have hgAdiff : ∀ k, Work.Drive.ChartDiff (chartAt ℂ (E.y k)) g (Ω \ ({a, b} : Set X)) :=
      fun k => Work.Kernel.chartDiff_of_isGreenOn (b := b) hg (E.y k)
    have hGdiff : ∀ k, Work.Drive.ChartDiff (chartAt ℂ (E.y k)) G (Ω \ ({a, b} : Set X)) :=
      fun k => by
        have h := Work.Kernel.chartDiff_of_isGreenOn (b := a) hG (E.y k)
        rwa [show ({b, a} : Set X) = {a, b} from by
          ext x
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto] at h
    have htmpA : (chartAt ℂ (E.y E.ia)) a ∈
        Metric.ball ((chartAt ℂ (E.y E.ia)) (E.y E.ia)) (E.ρ E.ia) := by
      rw [hEya, Metric.mem_ball, dist_self]
      exact lt_trans (lt_trans (E.hspos E.ia) (E.hsσ E.ia)) (E.hσρ E.ia)
    have htmpB : (chartAt ℂ (E.y E.ib)) b ∈
        Metric.ball ((chartAt ℂ (E.y E.ib)) (E.y E.ib)) (E.ρ E.ib) := by
      rw [hEyb, Metric.mem_ball, dist_self]
      exact lt_trans (lt_trans (E.hspos E.ib) (E.hsσ E.ib)) (E.hσρ E.ib)
    have hHA : InnerProductSpace.HarmonicOnNhd HA₀
        (Metric.ball ((chartAt ℂ (E.y E.ia)) a) (min rA₀ (E.ρ E.ia))) := by
      rw [hEya]
      exact hHA₀.mono (Metric.ball_subset_ball (min_le_left _ _))
    have hueqA : ∀ z ∈ Metric.ball ((chartAt ℂ (E.y E.ia)) a) (min rA₀ (E.ρ E.ia)),
        g ((chartAt ℂ (E.y E.ia)).symm z)
          = -Real.log ‖z - (chartAt ℂ (E.y E.ia)) a‖ + HA₀ z := by
      rw [hEya]
      exact fun z hz => hexpA z (Metric.ball_subset_ball (min_le_left _ _) hz)
    have hHB : InnerProductSpace.HarmonicOnNhd HB₀
        (Metric.ball ((chartAt ℂ (E.y E.ib)) b) (min rB₀ (E.ρ E.ib))) := by
      rw [hEyb]
      exact hHB₀.mono (Metric.ball_subset_ball (min_le_left _ _))
    have hueqB : ∀ z ∈ Metric.ball ((chartAt ℂ (E.y E.ib)) b) (min rB₀ (E.ρ E.ib)),
        G ((chartAt ℂ (E.y E.ib)).symm z)
          = -Real.log ‖z - (chartAt ℂ (E.y E.ib)) b‖ + HB₀ z := by
      rw [hEyb]
      exact fun z hz => hexpB z (Metric.ball_subset_ball (min_le_left _ _) hz)
    have hP1 : pairing E.y E.ρ E.σ E.ψ g (fun x => Ξg x * G x) = 2 * Real.pi * G a := by
      have h := Work.Kernel.pairing_pole_singular_a (X := X) (ι := ι) (Ω := Ω) (K := K) hab E
        hKc haK hbK hΩo hKΩ hg hG
        (lt_min hrA₀ (lt_trans (lt_trans (E.hspos E.ia) (E.hsσ E.ia)) (E.hσρ E.ia))) (min_le_right _ _)
        htmpA hHA hueqA hgAdiff hψc1 hβc1 hΞgdiff hΞgc1 hΞgsupp (hΞgsupp.trans hKΩ) hΞg_eq_one
      rw [h, hΞg_a, one_mul]
    have hP2 : pairing E.y E.ρ E.σ E.ψ G (fun x => Ξg x * g x) = 2 * Real.pi * g b := by
      have h := Work.Kernel.pairing_pole_singular (X := X) (ι := ι) (Ω := Ω) (K := K) hab E
        hKc haK hbK hΩo hKΩ hg hG
        (lt_min hrB₀ (lt_trans (lt_trans (E.hspos E.ib) (E.hsσ E.ib)) (E.hσρ E.ib))) (min_le_right _ _)
        htmpB hHB hueqB hGdiff hψc1 hβc1 hΞgdiff hΞgc1 hΞgsupp (hΞgsupp.trans hKΩ) hΞg_eq_one_a
      rw [h, hΞg_b, one_mul]
    have hP3 : pairing E.y E.ρ E.σ E.ψ g Th = 2 * Real.pi * cσ := by
      have h := Work.Kernel.pairing_pole_of_isGreenOn (E := E) hEya hKc haK hΩo hKΩ hg ha
        hψc1 hβc1 hThdiff hThc1 hThsupp (hThsupp.trans hKΩ)
      rw [h, hTh_a]
    have hP4 : pairing E.y E.ρ E.σ E.ψ G Ξg = 2 * Real.pi := by
      have h := Work.Kernel.pairing_pole_of_isGreenOn (E := E.swap) hEyb hKc hbK hΩo hKΩ hG hb
        hψc1 hβc1 hΞgdiff hΞgc1 hΞgsupp (hΞgsupp.trans hKΩ)
      rw [Work.Kernel.pairing_swap_eq E G Ξg] at h
      rw [hΞg_b] at h
      simpa using h

    -- ## the expansions of `A` and `B`, the flux identity and the level identity
    have hae_ΞG : ∀ i : ι, ∀ᵐ z ∂(volume : Measure ℂ),
        DifferentiableAt ℝ (clampedPullback (E.y i) (E.ρ i) (fun x => Ξ (G x))) z := by
      intro i
      refine clampedPullback_differentiableAt_ae_of_off' (E.htgt i)
        (z₀ := (chartAt ℂ (E.y i)) b) ?_
      intro z hz hz0
      have hright : (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)).symm z) = z :=
        (chartAt ℂ (E.y i)).right_inv (E.htgt i hz)
      have hsrc : (chartAt ℂ (E.y i)).symm z ∈ (chartAt ℂ (E.y i)).source :=
        (chartAt ℂ (E.y i)).map_target (E.htgt i hz)
      have hxb : (chartAt ℂ (E.y i)).symm z ≠ b := by
        intro hcon
        exact hz0 (by rw [← hright, hcon])
      have hzball : (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)).symm z) ∈
          Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.ρ i) := by
        rw [hright]; exact hz
      have hxΩ : (chartAt ℂ (E.y i)).symm z ∈ Ω :=
        E.hballΩ i ⟨hsrc, hzball⟩
      have hiff := (Submission.HarmonicOnXAt_iff_chart (u := G) (x := (chartAt ℂ (E.y i)).symm z)
        (y := E.y i) hsrc).mp (hG.2.1 _ ⟨hxΩ, hxb⟩)
      have hGc1 : ContDiffAt ℝ 1 (G ∘ (chartAt ℂ (E.y i)).symm)
          ((chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)).symm z)) := hiff.1.of_le (by norm_num)
      have hc : ContDiffAt ℝ 1 (fun w : ℂ => Ξ (G ((chartAt ℂ (E.y i)).symm w))) z := by
        have h := contDiffAt_chart_comp_of_contDiffAt (contDiff_stepCutoff σ (n := 1)) hGc1
        rwa [hright] at h
      exact hc.differentiableAt (by norm_num)
    have hderivΦ : deriv (fun t : ℝ => Ξ t * t) = fun t => Ξ t + t * deriv Ξ t := by
      funext t
      have h1 : DifferentiableAt ℝ Ξ t :=
        (contDiff_stepCutoff σ (n := 1)).differentiable (by norm_num) t
      have hd : deriv (Ξ * id) t = deriv Ξ t * id t + Ξ t * 1 :=
        (h1.hasDerivAt.mul (hasDerivAt_id t)).deriv
      rw [show (Ξ * id : ℝ → ℝ) = (fun s : ℝ => Ξ s * s) from rfl] at hd
      rw [hd]
      simp only [id_eq, mul_one]
      ring
    have hΞ0 : Ξ 0 = 0 := by
      rw [hΞdef]; exact stepCutoff_eq_zero_of_le hσpos (by linarith)
    have hΦ0 : (fun t : ℝ => Ξ t * t) 0 = 0 := by
      show Ξ 0 * 0 = 0
      rw [hΞ0, zero_mul]
    have hΦd : Differentiable ℝ (fun t : ℝ => Ξ t * t) :=
      ((contDiff_stepCutoff σ (n := 1)).differentiable (by norm_num)).mul differentiable_id
    have hWtgt : ∀ i, Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.σ i) ⊆
        (chartAt ℂ (E.y i)).target :=
      fun i => (Metric.ball_subset_ball (le_of_lt (E.hσρ i))).trans (E.htgt i)
    have hA : pairing E.y E.ρ E.σ E.ψ g (fun x => Ξg x * G x)
        = pairing E.y E.ρ E.σ (fun i x => E.ψ i x * Ξg x) g G
          + pairing E.y E.ρ E.σ (fun i x => E.ψ i x * Y_G x) g G := by
      have e1 : pairing E.y E.ρ E.σ E.ψ g (fun x => Ξg x * G x)
          = pairing E.y E.ρ E.σ E.ψ g (fun x => Ξ (G x) * G x) :=
        Work.Drive.pairing_eq_of_eq_off_right E.htgt (q := b)
          (fun x hx => by rw [hΞg_of_ne x hx])
      have e2 : pairing E.y E.ρ E.σ E.ψ g (fun x => Ξ (G x) * G x)
          = pairing E.y E.ρ E.σ
              (fun i x => E.ψ i x * deriv (fun t : ℝ => Ξ t * t) (G x)) g G :=
        pairing_comp_right' (ψ := E.ψ) (f := g) (g := G) (Φ := fun t : ℝ => Ξ t * t)
          hΦ0 hΦd hae_G
      have e3 : pairing E.y E.ρ E.σ
            (fun i x => E.ψ i x * deriv (fun t : ℝ => Ξ t * t) (G x)) g G
          = pairing E.y E.ρ E.σ
              (fun i x => (E.ψ i x * Ξg x) + (E.ψ i x * Y_G x)) g G :=
        pairing_congr_weight_ae (weight_ae hWtgt (q := b)
          (W := fun i x => E.ψ i x * deriv (fun t : ℝ => Ξ t * t) (G x))
          (W' := fun i x => (E.ψ i x * Ξg x) + (E.ψ i x * Y_G x))
          (fun i y hy => by
            rw [hderivΦ, hΞg_of_ne y hy, hY_G_of_ne y hy]
            ring))
      have hsumA := pairing_weight_add' (W := fun i x => E.ψ i x * Ξg x)
        (W' := fun i x => E.ψ i x * Y_G x) cert1 cert2
      rw [e1, e2, e3]
      exact hsumA
    have certGg : ∀ i, PairIntegrable (E.y i) (E.ρ i) (E.σ i)
        (fun x => E.ψ i x * Ξg x) G g :=
      fun i => (cert1 i).comm
    have certGΞ : ∀ i, PairIntegrable (E.y i) (E.ρ i) (E.σ i) (fun x => E.ψ i x * g x) G
        (fun x => Ξ (G x)) := by
      intro i
      have h1 : PairIntegrable (E.y i) (E.ρ i) (E.σ i)
          (fun y => (E.ψ i y * g y) * deriv Ξ (G y)) G G :=
        (cert4 i).congr_ae ((weight_ae hWtgt (q := b)
          (W := fun _ y => (E.ψ i y * g y) * deriv Ξ (G y))
          (W' := fun _ y => E.ψ i y * Y_g y)
          (fun _ y hy => by rw [hY_g_of_ne y hy]; ring)) i)
      exact (PairIntegrable.comp_iff (x := E.y i) (ρ := E.ρ i) (σ := E.σ i)
        (W := fun y => E.ψ i y * g y) (f := G) (g := G) (Φ := Ξ) (E.hσρ i)
        (stepCutoff_eq_zero_of_le hσpos (le_of_lt hσpos))
        ((contDiff_stepCutoff σ (n := 1)).differentiable (by norm_num))
        (hae_G i)).mpr h1
    have certGgG : ∀ i, PairIntegrable (E.y i) (E.ρ i) (E.σ i) (E.ψ i) G
        (fun x => Ξ (G x) * g x) := by
      intro i
      exact PairIntegrable.leibniz (E.hσρ i) (hae_G i) (hae_g i) (hae_ΞG i)
        ((certGg i).congr_ae ((weight_ae hWtgt (q := b)
          (W := fun _ y => E.ψ i y * Ξ (G y))
          (W' := fun _ y => E.ψ i y * Ξg y)
          (fun _ y hy => by rw [hΞg_of_ne y hy])) i))
        (certGΞ i)
    have hB : pairing E.y E.ρ E.σ E.ψ G (fun x => Ξg x * g x)
        = pairing E.y E.ρ E.σ (fun i x => E.ψ i x * Ξg x) g G
          + pairing E.y E.ρ E.σ (fun i x => E.ψ i x * Y_g x) G G := by
      have e1 : pairing E.y E.ρ E.σ E.ψ G (fun x => Ξg x * g x)
          = pairing E.y E.ρ E.σ E.ψ G (fun x => Ξ (G x) * g x) :=
        Work.Drive.pairing_eq_of_eq_off_right E.htgt (q := b)
          (fun x hx => by rw [hΞg_of_ne x hx])
      have e2 : pairing E.y E.ρ E.σ E.ψ G (fun x => Ξ (G x) * g x)
          = pairing E.y E.ρ E.σ (fun i x => E.ψ i x * Ξ (G x)) G g
            + pairing E.y E.ρ E.σ (fun i x => E.ψ i x * g x) G (fun x => Ξ (G x)) :=
        pairing_leibniz'' (W' := fun x => Ξ (G x)) (f := G) (g := g) certGgG
          (fun i => (certGg i).congr_ae ((weight_ae hWtgt (q := b)
            (W := fun _ y => E.ψ i y * Ξ (G y)) (W' := fun _ y => E.ψ i y * Ξg y)
            (fun _ y hy => by rw [hΞg_of_ne y hy])) i))
          certGΞ hae_G hae_g hae_ΞG
      have e3 : pairing E.y E.ρ E.σ (fun i x => E.ψ i x * Ξ (G x)) G g
          = pairing E.y E.ρ E.σ (fun i x => E.ψ i x * Ξg x) G g :=
        pairing_congr_weight_ae (weight_ae hWtgt (q := b)
          (W := fun i y => E.ψ i y * Ξ (G y)) (W' := fun i y => E.ψ i y * Ξg y)
          (fun i y hy => by rw [hΞg_of_ne y hy]))
      have e4 : pairing E.y E.ρ E.σ (fun i x => E.ψ i x * Ξg x) G g
          = pairing E.y E.ρ E.σ (fun i x => E.ψ i x * Ξg x) g G := by
        simp only [pairing]
        exact Finset.sum_congr rfl fun i _ =>
          Work.Drive.GreenRung.pairTerm_symm (E.y i) (E.ρ i) (E.σ i)
            (fun x => E.ψ i x * Ξg x) G g
      have e5 : pairing E.y E.ρ E.σ (fun i x => E.ψ i x * g x) G (fun x => Ξ (G x))
          = pairing E.y E.ρ E.σ (fun i x => (E.ψ i x * g x) * deriv Ξ (G x)) G G :=
        pairing_comp_right' (ψ := fun i x => E.ψ i x * g x) (f := G) (g := G) (Φ := Ξ)
          (stepCutoff_eq_zero_of_le hσpos (le_of_lt hσpos))
          ((contDiff_stepCutoff σ (n := 1)).differentiable (by norm_num)) hae_G
      have e6 : pairing E.y E.ρ E.σ (fun i x => (E.ψ i x * g x) * deriv Ξ (G x)) G G
          = pairing E.y E.ρ E.σ (fun i x => E.ψ i x * Y_g x) G G :=
        pairing_congr_weight_ae (weight_ae hWtgt (q := b)
          (W := fun i y => (E.ψ i y * g y) * deriv Ξ (G y))
          (W' := fun i y => E.ψ i y * Y_g y)
          (fun i y hy => by rw [hY_g_of_ne y hy]; ring))
      rw [e1, e2, e3, e4, e5, e6]
    have hWG : pairing E.y E.ρ E.σ (fun i x => E.ψ i x * Y_G x) g G = 2 * Real.pi * cσ := by
      have hθ0 : θ 0 = 0 := thetaCutoff_eq_zero_of_le hσpos (le_of_lt hσpos)
      have hθd : Differentiable ℝ θ := (contDiff_thetaCutoff hσpos).differentiable (by norm_num)
      have hΞ0 : Ξ 0 = 0 := stepCutoff_eq_zero_of_le hσpos (le_of_lt hσpos)
      have hΞd : Differentiable ℝ Ξ := (contDiff_stepCutoff σ (n := 1)).differentiable (by norm_num)
      have e1 : pairing E.y E.ρ E.σ (fun i x => E.ψ i x * Y_G x) g G
          = pairing E.y E.ρ E.σ (fun i x => (E.ψ i x * G x) * deriv Ξ (G x)) g G :=
        pairing_congr_weight_ae (weight_ae hWtgt (q := b)
          (W := fun i y => E.ψ i y * Y_G y) (W' := fun i y => (E.ψ i y * G y) * deriv Ξ (G y))
          (fun i y hy => by rw [hY_G_of_ne y hy]; ring))
      have e2 : pairing E.y E.ρ E.σ (fun i x => (E.ψ i x * G x) * deriv Ξ (G x)) g G
          = pairing E.y E.ρ E.σ (fun i x => E.ψ i x * (G x * deriv Ξ (G x))) g G :=
        pairing_congr_weight_ae (weight_ae hWtgt (q := b)
          (W := fun i y => (E.ψ i y * G y) * deriv Ξ (G y))
          (W' := fun i y => E.ψ i y * (G y * deriv Ξ (G y)))
          (fun i y hy => by ring))
      have e3 : pairing E.y E.ρ E.σ (fun i x => E.ψ i x * (G x * deriv Ξ (G x))) g G
          = pairing E.y E.ρ E.σ (fun i x => E.ψ i x * deriv θ (G x)) g G :=
        pairing_congr_weight_ae (weight_ae hWtgt (q := b)
          (W := fun i y => E.ψ i y * (G y * deriv Ξ (G y)))
          (W' := fun i y => E.ψ i y * deriv θ (G y))
          (fun i y hy => by rw [deriv_thetaCutoff_eq hσpos (G y)]))
      have e4 : pairing E.y E.ρ E.σ (fun i x => E.ψ i x * deriv θ (G x)) g G
          = pairing E.y E.ρ E.σ E.ψ g (fun x => θ (G x)) :=
        (pairing_comp_right' (ψ := E.ψ) (f := g) (g := G) (Φ := θ) hθ0 hθd hae_G).symm
      have e5 : pairing E.y E.ρ E.σ E.ψ g (fun x => θ (G x))
          = pairing E.y E.ρ E.σ E.ψ g Th :=
        Work.Drive.pairing_eq_of_eq_off_right E.htgt (q := b)
          (fun x hx => by rw [hTh_of_ne x hx])
      rw [e1, e2, e3, e4, e5, hP3]
    have hlevel : pairing E.y E.ρ E.σ (fun i x => E.ψ i x * Y_V x) G G = 2 * Real.pi := by
      have hΞ0 : Ξ 0 = 0 := stepCutoff_eq_zero_of_le hσpos (le_of_lt hσpos)
      have hΞd : Differentiable ℝ Ξ := (contDiff_stepCutoff σ (n := 1)).differentiable (by norm_num)
      have e1 : pairing E.y E.ρ E.σ (fun i x => E.ψ i x * Y_V x) G G
          = pairing E.y E.ρ E.σ (fun i x => E.ψ i x * deriv Ξ (G x)) G G :=
        pairing_congr_weight_ae (weight_ae hWtgt (q := b)
          (W := fun i y => E.ψ i y * Y_V y) (W' := fun i y => E.ψ i y * deriv Ξ (G y))
          (fun i y hy => by rw [hY_V_of_ne y hy]))
      have e2 : pairing E.y E.ρ E.σ (fun i x => E.ψ i x * deriv Ξ (G x)) G G
          = pairing E.y E.ρ E.σ E.ψ G (fun x => Ξ (G x)) :=
        (pairing_comp_right' (ψ := E.ψ) (f := G) (g := G) (Φ := Ξ) hΞ0 hΞd hae_G).symm
      have e3 : pairing E.y E.ρ E.σ E.ψ G (fun x => Ξ (G x))
          = pairing E.y E.ρ E.σ E.ψ G Ξg :=
        Work.Drive.pairing_eq_of_eq_off_right E.htgt (q := b)
          (fun x hx => by rw [hΞg_of_ne x hx])
      rw [e1, e2, e3, hP4]

    -- ## the final algebra: `2π (G a - g b) = 2π c_σ - C`, with `0 ≤ C ≤ ε·2π`
    have hY_g_nonneg : ∀ y : X, 0 ≤ Y_g y := by
      intro y
      by_cases hyb : y = b
      · rw [hyb]
        have h0 : Y_g b = 0 := by rw [hY_gdef, Function.update_self]
        rw [h0]
      · rw [hY_g_of_ne y hyb]
        by_cases hya : y = a
        · rw [hya]
          have h0 : deriv Ξ (G a) = 0 := deriv_zero_of_gt (G a) hσG
          rw [h0, mul_zero]
        · by_cases hyΩ : y ∈ Ω
          · exact mul_nonneg (le_of_lt (hg.1 y hyΩ hya)) (deriv_stepCutoff_nonneg hσpos (G y))
          · have hgy : g y = 0 := by
              rw [hgdef, Function.update_of_ne hya]
              exact hout₁ y hyΩ
            rw [hgy, zero_mul]
    have hCnonneg : 0 ≤ pairing E.y E.ρ E.σ (fun i x => E.ψ i x * Y_g x) G G := by
      simp only [pairing]
      refine Finset.sum_nonneg (fun i _ => ?_)
      rw [pairTerm]
      exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun z =>
        mul_nonneg (clampedPullback_nonneg (fun y =>
          mul_nonneg (E.hψnonneg i y) (hY_g_nonneg y)) z) real_inner_self_nonneg)
    have hmono : ∀ i, pairTerm (E.y i) (E.ρ i) (E.σ i) (fun y => E.ψ i y * Y_g y) G G
        ≤ ε * pairTerm (E.y i) (E.ρ i) (E.σ i) (fun y => E.ψ i y * Y_V y) G G := by
      intro i
      refine pairTerm_mono_in_weight (W₁ := fun y => E.ψ i y * Y_g y)
        (W₂ := fun y => E.ψ i y * Y_V y) (f := G) (c := ε) ?_ ?_ (cert4 i) (cert3 i)
      · exact fun z => clampedPullback_nonneg (fun y =>
          mul_nonneg (E.hψnonneg i y) (hY_g_nonneg y)) z
      · intro z
        by_cases hz : z ∈ Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.σ i)
        · rw [clampedPullback_apply_of_mem hz, clampedPullback_apply_of_mem hz]
          set y : X := (chartAt ℂ (E.y i)).symm z with hydef
          have hzρ : z ∈ Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.ρ i) :=
            Metric.ball_subset_ball (le_of_lt (E.hσρ i)) hz
          have hright : (chartAt ℂ (E.y i)) y = z := (chartAt ℂ (E.y i)).right_inv (E.htgt i hzρ)
          have hysrc : y ∈ (chartAt ℂ (E.y i)).source :=
            (chartAt ℂ (E.y i)).map_target (E.htgt i hzρ)
          have hzρ : (chartAt ℂ (E.y i)) y ∈
              Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.ρ i) := by
            rw [hright]
            exact Metric.ball_subset_ball (le_of_lt (E.hσρ i)) hz
          have hyΩ : y ∈ Ω := E.hballΩ i ⟨hysrc, hzρ⟩
          have hkey : Y_g y ≤ ε * Y_V y := by
            by_cases hyb : y = b
            · rw [hyb]
              have h0 : Y_g b = 0 := by rw [hY_gdef, Function.update_self]
              have h1 : Y_V b = 0 := by rw [hY_Vdef, Function.update_self]
              rw [h0, h1, mul_zero]
            · rw [hY_g_of_ne y hyb, hY_V_of_ne y hyb]
              by_cases hya : y = a
              · rw [hya]
                have h0 : deriv Ξ (G a) = 0 := deriv_zero_of_gt (G a) hσG
                rw [h0, mul_zero, mul_zero]
              · by_cases hd0 : deriv Ξ (G y) = 0
                · rw [hd0, mul_zero, mul_zero]
                · have hGle : G y ≤ 2 * σ := by
                    by_contra hcon
                    exact hd0 (deriv_zero_of_gt (G y) (not_le.mp hcon))
                  have hle : g y ≤ ε := le_of_lt (hsup y hyΩ hya hyb hGle)
                  exact mul_le_mul_of_nonneg_right hle (deriv_stepCutoff_nonneg hσpos (G y))
          calc E.ψ i y * Y_g y ≤ E.ψ i y * (ε * Y_V y) :=
                mul_le_mul_of_nonneg_left hkey (E.hψnonneg i y)
            _ = ε * (E.ψ i y * Y_V y) := by ring
        · rw [clampedPullback_eq_zero_of_notMem_ball hz,
            clampedPullback_eq_zero_of_notMem_ball hz, mul_zero]
    have hCc_le : pairing E.y E.ρ E.σ (fun i x => E.ψ i x * Y_g x) G G
        ≤ ε * (2 * Real.pi) := by
      have h1 : pairing E.y E.ρ E.σ (fun i x => E.ψ i x * Y_g x) G G
          ≤ ∑ i, ε * pairTerm (E.y i) (E.ρ i) (E.σ i)
              (fun y => E.ψ i y * Y_V y) G G := by
        simp only [pairing]
        exact Finset.sum_le_sum (fun i _ => hmono i)
      have h2 : ∑ i, ε * pairTerm (E.y i) (E.ρ i) (E.σ i)
            (fun y => E.ψ i y * Y_V y) G G
          = ε * (∑ i, pairTerm (E.y i) (E.ρ i) (E.σ i)
              (fun y => E.ψ i y * Y_V y) G G) := by
        rw [Finset.mul_sum]
      have h3 : (∑ i, pairTerm (E.y i) (E.ρ i) (E.σ i)
            (fun y => E.ψ i y * Y_V y) G G) = 2 * Real.pi := by
        have h := hlevel
        simp only [pairing] at h
        exact h
      rw [h2, h3] at h1
      exact h1
    have hcσ_nonneg : 0 ≤ cσ := by
      rw [hcσdef]
      exact thetaCutoff_nonneg hσpos (by linarith)
    have hcσ_le : cσ ≤ 2 * σ := by
      rw [hcσdef]
      exact thetaCutoff_le_two_mul hσpos
    have hAB : 2 * Real.pi * (G a - g b)
        = 2 * Real.pi * cσ - pairing E.y E.ρ E.σ (fun i x => E.ψ i x * Y_g x) G G := by
      have h1 : pairing E.y E.ρ E.σ E.ψ g (fun x => Ξg x * G x)
          = pairing E.y E.ρ E.σ (fun i x => E.ψ i x * Ξg x) g G
            + 2 * Real.pi * cσ := by
        rw [hA, hWG]
      have h2 : pairing E.y E.ρ E.σ E.ψ G (fun x => Ξg x * g x)
          = pairing E.y E.ρ E.σ (fun i x => E.ψ i x * Ξg x) g G
            + pairing E.y E.ρ E.σ (fun i x => E.ψ i x * Y_g x) G G := hB
      have h3 : 2 * Real.pi * (G a - g b)
          = 2 * Real.pi * G a - 2 * Real.pi * g b := by ring
      rw [h3, ← hP1, ← hP2, h1, h2]
      ring
    have hfinal : |G a - g b| ≤ ε := by
      have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
      have habs : |2 * Real.pi * (G a - g b)| ≤ 2 * Real.pi * ε := by
        rw [hAB]
        have h1 : 0 ≤ 2 * Real.pi * cσ := mul_nonneg h2pi.le hcσ_nonneg
        have h2 : 2 * Real.pi * cσ ≤ 2 * Real.pi * ε :=
          mul_le_mul_of_nonneg_left (le_trans hcσ_le hσε) h2pi.le
        have h3 : pairing E.y E.ρ E.σ (fun i x => E.ψ i x * Y_g x) G G
            ≤ 2 * Real.pi * ε := by
          calc pairing E.y E.ρ E.σ (fun i x => E.ψ i x * Y_g x) G G
              ≤ ε * (2 * Real.pi) := hCc_le
            _ = 2 * Real.pi * ε := by ring
        rw [abs_le]
        exact ⟨by linarith, by linarith⟩
      rw [abs_mul, abs_of_pos h2pi] at habs
      exact (mul_le_mul_iff_right₀ h2pi).mp habs
    exact hfinal
  have hzero : |G a - g b| = 0 := by
    refine le_antisymm ?_ (abs_nonneg _)
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    exact le_trans (key (ε / 2) (by linarith)) (by linarith)
  exact (sub_eq_zero.mp (abs_eq_zero.mp hzero)).symm

end Work.Drive
