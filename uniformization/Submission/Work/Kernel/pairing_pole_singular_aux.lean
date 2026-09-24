import Mathlib
import Submission.Work.Kernel.pairing_pole_smooth
import Submission.Work.Kernel.exists_plateau_profile
import Submission.Work.Kernel.greenCoverPairingAux
import Submission.Work.Drive.pairing_tendsto
import Submission.Work.Analysis.integrable_inv_norm_mul
import Submission.Work.Analysis.integrable_inv_norm_mul_two
import Submission.Work.Analysis.tendsto_gradient_clampedPullback
import Submission.Work.Analysis.gradient_comp_scalar
import Submission.Work.Kernel.chartDiff_and_contDiffAt_of_plateau
import Submission.Work.Kernel.contDiffAt_chartPullback_mul_comp_of_harmonic
import Submission.Work.Drive.isGreenOn_le_of_subset
import Submission.Work.Kernel.pairingPoleTools
import Submission.Work.Kernel.exists_bound_gradient_plateau_test

/-!
# Auxiliary lemmas for the singular pole identity

The helpers used by `Work.Kernel.pairing_pole_singular`: the plateau profiles, the growth of a Green
function and of its gradient on the support of a weight of a `GreenCover`, the boundedness of the
`χ`-terms of the test-function gradient, the product rule for the gradient, and the two-pole
integrability input `Work.Analysis.integrable_inv_norm_mul_two`.
-/

open Set Metric MeasureTheory Filter
open scoped Manifold Topology Gradient ContDiff

noncomputable section

set_option linter.unusedSectionVars false

namespace Work.Kernel

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-! ## 1. The plateau profiles -/

/-- A plateau profile `Θ` supplied by `exists_plateau_profile` satisfies `|Θ w| ≤ |w|`. -/
lemma plateau_abs_le {M : ℝ} (hM : 0 < M) {Θ : ℝ → ℝ}
    (hΘ : ContDiff ℝ 1 Θ)
    (hΘ1 : ∀ w : ℝ, 0 ≤ w → w ≤ M / 4 → Θ w = w)
    (hd : ∀ w : ℝ, 0 ≤ deriv Θ w ∧ deriv Θ w ≤ 1) :
    ∀ w : ℝ, |Θ w| ≤ |w| := by
  have hdiff : Differentiable ℝ Θ := hΘ.differentiable (by norm_num)
  have h0 : Θ 0 = 0 := by
    have h := hΘ1 0 le_rfl (by positivity)
    simpa using h
  have hC : ∀ w ∈ (Set.univ : Set ℝ), ‖deriv Θ w‖ ≤ (1 : ℝ) := by
    intro w _
    rw [Real.norm_eq_abs, abs_of_nonneg (hd w).1]
    exact (hd w).2
  intro w
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := Θ) (s := Set.univ) (C := 1)
    (fun x _ => hdiff x) hC convex_univ (Set.mem_univ 0) (Set.mem_univ w)
  rw [h0, sub_zero, Real.norm_eq_abs] at h
  simpa using h

/-- A family of plateau profiles at the levels `M₀ + n`. -/
lemma exists_plateau_seq (M₀ : ℝ) (hM₀ : 0 < M₀) :
    ∃ Θ : ℕ → ℝ → ℝ,
      (∀ n : ℕ, ContDiff ℝ 1 (Θ n)) ∧
      (∀ n : ℕ, Monotone (Θ n)) ∧
      (∀ (n : ℕ) (w : ℝ), 0 ≤ w → w ≤ (M₀ + n) / 4 → Θ n w = w) ∧
      (∀ (n : ℕ) (w : ℝ), M₀ + n ≤ w → Θ n w = (M₀ + n) / 2) ∧
      (∀ (n : ℕ) (w : ℝ), 0 ≤ deriv (Θ n) w ∧ deriv (Θ n) w ≤ 1) ∧
      (∀ (n : ℕ) (w : ℝ), |Θ n w| ≤ |w|) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < M₀ + n := fun n => by positivity
  let Θ : ℕ → ℝ → ℝ := fun n =>
    Classical.choose (Work.Kernel.exists_plateau_profile (M₀ + n) (hpos n))
  have hspec : ∀ n, ContDiff ℝ 1 (Θ n) ∧ Monotone (Θ n) ∧
      (∀ w : ℝ, 0 ≤ w → w ≤ (M₀ + n) / 4 → Θ n w = w) ∧
      (∀ w : ℝ, M₀ + n ≤ w → Θ n w = (M₀ + n) / 2) ∧
      (∀ w : ℝ, 0 ≤ deriv (Θ n) w ∧ deriv (Θ n) w ≤ 1) := fun n =>
    Classical.choose_spec (Work.Kernel.exists_plateau_profile (M₀ + n) (hpos n))
  refine ⟨Θ, fun n => (hspec n).1, fun n => (hspec n).2.1,
    fun n => (hspec n).2.2.1, fun n => (hspec n).2.2.2.1, fun n => (hspec n).2.2.2.2, ?_⟩
  intro n
  exact plateau_abs_le (hpos n) (hspec n).1 (hspec n).2.2.1 (hspec n).2.2.2.2


/-! ## 2. Growth of a Green function at its pole, and growth/boundedness on a weight support -/

/-- A Green function tends to `+∞` at its pole: on a punctured neighbourhood of `a` it exceeds any
prescribed level. -/
lemma eventually_le_green_near_pole {Ω : Set X} (hΩo : IsOpen Ω) {a : X} (haΩ : a ∈ Ω)
    {gA : X → ℝ} (hgA : Work.SimplyConnected.ABS.IsGreenOn Ω a gA) (M : ℝ) :
    ∀ᶠ x in 𝓝 a, x ≠ a → M ≤ gA x := by
  obtain ⟨C, V, hV, hbnd⟩ := hgA.2.2.2
  have hV' : V ∩ Ω ∈ 𝓝 a := Filter.inter_mem hV (hΩo.mem_nhds haΩ)
  have hbnd' : ∀ x ∈ V ∩ Ω, x ≠ a →
      |gA x + Real.log ‖(chartAt ℂ a) x - (chartAt ℂ a) a‖| ≤ C :=
    fun x hx hxne => hbnd x hx.1 hx.2 hxne
  obtain ⟨W, hW, hWb⟩ := Work.Drive.growth_of_logPole (z₀ := a) (E := gA) hV' hbnd' M
  filter_upwards [hW] with x hx hxne
  exact le_of_lt (hWb x hx hxne)

/-- **Growth bound for the gradient of a clamped chart pullback, on the support of a weight**, in a
chart in which the Green function has a logarithmic expansion at its pole. -/
lemma growth_on_tsupport_of_logExpansion {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω : Set X} {a y : X} {g : X → ℝ} {ρ σ δ : ℝ} {H : ℂ → ℝ} {W : X → ℝ}
    (hg : Work.SimplyConnected.ABS.IsGreenOn Ω a g) (hσρ : σ < ρ)
    (htgt : Metric.ball ((chartAt ℂ y) y) ρ ⊆ (chartAt ℂ y).target)
    (hballΩ : Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) ρ ⊆ Ω)
    (hδ : 0 < δ) (hH : InnerProductSpace.HarmonicOnNhd H (Metric.ball ((chartAt ℂ y) a) δ))
    (hueq : ∀ z ∈ Metric.ball ((chartAt ℂ y) a) δ, z ≠ (chartAt ℂ y) a →
      g ((chartAt ℂ y).symm z) = -Real.log ‖z - (chartAt ℂ y) a‖ + H z) :
    ∃ C : ℝ, 0 < C ∧ ∀ᵐ z ∂(volume : Measure ℂ),
      z ∈ tsupport (Work.Drive.clampedPullback y σ W) →
        ‖gradient (Work.Drive.clampedPullback y ρ g) z‖
          ≤ C / ‖z - (chartAt ℂ y) a‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    Work.Kernel.PS.exists_growth_clampedPullback_le_of_logExpansion hg hσρ htgt hballΩ hδ hH hueq
  refine ⟨C, hC, ?_⟩
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton ((chartAt ℂ y) a))] with z hz
  intro hzs
  refine hbound z ?_ (by simpa using hz)
  exact (tsupport_clampedPullback_subset_closedBall_general (x := y) (ρ := σ) (f := W)) hzs

/-- **Boundedness of the gradient of a clamped chart pullback, on the support of a weight**, in a
chart whose closed ball of radius `σ` avoids the pole: the bound is written as `C / ‖z - p‖` for the
auxiliary point `p = (chartAt ℂ y) y + t` (used to put all the dominating functions in a common
shape). -/
lemma bound_on_tsupport_of_avoid {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω : Set X} {a y : X} {g : X → ℝ} {ρ σ t : ℝ} {W : X → ℝ}
    (hg : Work.SimplyConnected.ABS.IsGreenOn Ω a g) (hσρ : σ < ρ)
    (htgt : Metric.ball ((chartAt ℂ y) y) ρ ⊆ (chartAt ℂ y).target)
    (hballΩ : Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) ρ ⊆ Ω)
    (havoid : a ∉ Submission.chartClosedBall (chartAt ℂ y) ((chartAt ℂ y) y) σ)
    (hσpos : 0 ≤ σ) (ht : 0 < t) :
    ∃ C : ℝ, 0 < C ∧ ∀ᵐ z ∂(volume : Measure ℂ),
      z ∈ tsupport (Work.Drive.clampedPullback y σ W) →
        ‖gradient (Work.Drive.clampedPullback y ρ g) z‖
          ≤ C / ‖z - ((chartAt ℂ y) y + (t : ℂ))‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    Work.Kernel.PS.exists_bound_clampedPullback_le_of_notMem hg hσρ htgt hballΩ havoid
  refine ⟨C * (σ + t + 1), by positivity, ?_⟩
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton ((chartAt ℂ y) y + (t : ℂ)))] with z hzp hzs
  have hzs' : z ∈ Metric.closedBall ((chartAt ℂ y) y) σ :=
    (tsupport_clampedPullback_subset_closedBall_general (x := y) (ρ := σ) (f := W)) hzs
  have h1 : ‖gradient (Work.Drive.clampedPullback y ρ g) z‖ ≤ C := hbound z hzs'
  have h2 : ‖z - ((chartAt ℂ y) y + (t : ℂ))‖ ≤ σ + t + 1 := by
    have h3 : z - ((chartAt ℂ y) y + (t : ℂ)) = (z - (chartAt ℂ y) y) - (t : ℂ) := by ring
    rw [h3]
    calc ‖(z - (chartAt ℂ y) y) - (t : ℂ)‖
        ≤ ‖z - (chartAt ℂ y) y‖ + ‖(t : ℂ)‖ := norm_sub_le _ _
      _ ≤ σ + t + 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
          have := Metric.mem_closedBall.mp hzs'
          rw [dist_eq_norm] at this
          linarith
  have hpos : 0 < ‖z - ((chartAt ℂ y) y + (t : ℂ))‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzp)
  refine h1.trans ?_
  rw [le_div_iff₀ hpos]
  calc C * ‖z - ((chartAt ℂ y) y + (t : ℂ))‖ ≤ C * (σ + t + 1) :=
        mul_le_mul_of_nonneg_left h2 hC.le
    _ = C * (σ + t + 1) := rfl



/-- **The `χ`-terms of the test-function gradient are bounded on the support of a weight.**  The
weight `χ` of the test function is `1` on a neighbourhood of the pole `a`, so the gradient of its
chart representative vanishes there; the only other term of that gradient is `|gA|` times the
gradient, which is bounded on the compact support of the weight. -/
lemma exists_bound_chi_terms {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω : Set X} {a y : X} {gA χ : X → ℝ} {ρ σ : ℝ} {W : X → ℝ}
    (hχc1 : ∀ x ∈ (chartAt ℂ y).source,
      ContDiffAt ℝ 1 (χ ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x))
    (hχ1 : χ =ᶠ[𝓝 a] 1)
    (hgA : Work.SimplyConnected.ABS.IsGreenOn Ω a gA)
    (htgt : Metric.ball ((chartAt ℂ y) y) ρ ⊆ (chartAt ℂ y).target)
    (hballΩ : Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) ρ ⊆ Ω)
    (hσρ : σ < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ tsupport (Work.Drive.clampedPullback y σ W),
      |gA ((chartAt ℂ y).symm z)| *
        ‖gradient (fun w : ℂ => χ ((chartAt ℂ y).symm w)) z‖ ≤ C ∧
      |χ ((chartAt ℂ y).symm z)| ≤ C := by
  classical
  set c := chartAt ℂ y with hc
  obtain ⟨U, hU, hUχ⟩ := Filter.eventually_iff_exists_mem.mp hχ1
  obtain ⟨U₀, hU₀sub, hU₀open, haU₀⟩ := mem_nhds_iff.mp hU
  set O : Set ℂ := c '' (U₀ ∩ c.source) with hO
  have hOopen : IsOpen O :=
    c.isOpen_image_of_subset_source (hU₀open.inter c.open_source) inter_subset_right
  have hOeq : ∀ z ∈ O, χ (c.symm z) = 1 := by
    rintro z ⟨x, ⟨hxU, hxsrc⟩, rfl⟩
    rw [c.left_inv hxsrc]
    exact hUχ x (hU₀sub hxU)
  have hOgrad : ∀ z ∈ O, gradient (fun w : ℂ => χ (c.symm w)) z = 0 := by
    intro z hz
    have hev : (fun w : ℂ => χ (c.symm w)) =ᶠ[𝓝 z] (fun _ => (1 : ℝ)) := by
      filter_upwards [hOopen.mem_nhds hz] with w hw
      exact hOeq w hw
    rw [Filter.EventuallyEq.gradient_eq hev]
    simp [gradient]
  set F : ℂ → ℝ := fun z =>
    |gA (c.symm z)| * ‖gradient (fun w : ℂ => χ (c.symm w)) z‖ + |χ (c.symm z)| with hF
  have hScont : ContinuousOn F (tsupport (Work.Drive.clampedPullback y σ W)) := by
    intro z hzS
    -- basic chart facts about `z`
    have hzball : z ∈ Metric.ball (c y) ρ := by
      have h1 : z ∈ Metric.closedBall (c y) σ :=
        (tsupport_clampedPullback_subset_closedBall_general (x := y) (ρ := σ) (f := W)) hzS
      exact lt_of_le_of_lt (Metric.mem_closedBall.mp h1) hσρ
    have hztgt : z ∈ c.target := htgt hzball
    have hzsrc : c.symm z ∈ c.source := c.map_target hztgt
    have hzright : c (c.symm z) = z := c.right_inv hztgt
    have hχc1z : ContDiffAt ℝ 1 (fun w : ℂ => χ (c.symm w)) z := by
      have h := hχc1 (c.symm z) hzsrc
      rwa [hzright] at h
    by_cases hzO : z ∈ O
    · have hev : F =ᶠ[𝓝 z] (fun w => |χ (c.symm w)|) := by
        filter_upwards [hOopen.mem_nhds hzO] with w hw
        simp only [hF]
        rw [hOgrad w hw, norm_zero, mul_zero, zero_add]
      exact ((hχc1z.continuousAt.abs).congr_of_eventuallyEq hev).continuousWithinAt
    · have hxne : c.symm z ≠ a := by
        intro hcon
        refine hzO ⟨a, ⟨?_, ?_⟩, ?_⟩
        · exact haU₀
        · rw [← hcon]; exact hzsrc
        · rw [← hcon]; exact hzright
      have hxmem : c.symm z ∈ Submission.chartBall c (c y) ρ :=
        ⟨hzsrc, by rw [Set.mem_preimage, hzright]; exact hzball⟩
      have hxΩ : c.symm z ∈ Ω := hballΩ hxmem
      have hgAc : ContinuousAt (fun w : ℂ => gA (c.symm w)) z := by
        have hharm : Submission.HarmonicOnXAt gA (c.symm z) := hgA.2.1 _ ⟨hxΩ, hxne⟩
        have h2 := (Submission.HarmonicOnXAt_iff_chart (u := gA) (x := c.symm z) (y := y) hzsrc).mp
          hharm
        rw [hzright] at h2
        exact h2.1.continuousAt
      have hgc1 : ContinuousAt (fun w : ℂ => gradient (fun w : ℂ => χ (c.symm w)) w) z := by
        have h1 : ContinuousAt (fderiv ℝ (fun w : ℂ => χ (c.symm w))) z :=
          hχc1z.continuousAt_fderiv (by norm_num)
        simpa only [gradient, Function.comp_def] using
          (InnerProductSpace.toDual ℝ ℂ).symm.continuous.continuousAt.comp h1
      exact ((hgAc.abs.mul hgc1.norm).add hχc1z.continuousAt.abs).continuousWithinAt
  obtain ⟨C, hC⟩ := (Work.Kernel.hasCompactSupport_clampedPullback (x := y) (σ := σ) (W := W)).isCompact.exists_bound_of_continuousOn hScont
  refine ⟨max C 0, le_max_right _ _, fun z hz => ⟨?_, ?_⟩⟩
  · have h1 : F z ≤ C := le_trans (le_abs_self _) (hC z hz)
    have h2 : |gA (c.symm z)| * ‖gradient (fun w : ℂ => χ (c.symm w)) z‖ ≤ F z := by
      simp only [hF]
      exact le_add_of_nonneg_right (abs_nonneg _)
    exact le_trans h2 (le_trans h1 (le_max_left _ _))
  · have h1 : F z ≤ C := le_trans (le_abs_self _) (hC z hz)
    have h2 : |χ (c.symm z)| ≤ F z := by
      simp only [hF]
      exact le_add_of_nonneg_left (mul_nonneg (abs_nonneg _) (norm_nonneg _))
    exact le_trans h2 (le_trans h1 (le_max_left _ _))


/-! ## 3. Growth data for the two Green functions on the support of a weight -/

lemma growth_data [T2Space X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X}
    (E : Work.Kernel.GreenCover ι Ω K a b)
    (hab : a ≠ b) (hΩo : IsOpen Ω) (haK : a ∈ K) (hbK : b ∈ K) (hKΩ : K ⊆ Ω)
    {gA gB : X → ℝ} (hgA : Work.SimplyConnected.ABS.IsGreenOn Ω a gA)
    (hgB : Work.SimplyConnected.ABS.IsGreenOn Ω b gB)
    {H : ℂ → ℝ} {r : ℝ} (hrpos : 0 < r) (hrρ : r ≤ E.ρ E.ib)
    (hpmem : (chartAt ℂ (E.y E.ib)) b ∈
      Metric.ball ((chartAt ℂ (E.y E.ib)) (E.y E.ib)) (E.ρ E.ib))
    (hH : InnerProductSpace.HarmonicOnNhd H (Metric.ball ((chartAt ℂ (E.y E.ib)) b) r))
    (hueq : ∀ z ∈ Metric.ball ((chartAt ℂ (E.y E.ib)) b) r,
      gB ((chartAt ℂ (E.y E.ib)).symm z)
        = -Real.log ‖z - (chartAt ℂ (E.y E.ib)) b‖ + H z)
    (i : ι) :
    ∃ (p₁ p₂ : ℂ) (C₁ C₂ : ℝ), 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ p₁ ≠ p₂ ∧
      (∀ᵐ z ∂(volume : Measure ℂ), z ∈ tsupport (Work.Drive.clampedPullback (E.y i) (E.σ i) (E.ψ i)) →
        ‖gradient (Work.Drive.clampedPullback (E.y i) (E.ρ i) gA) z‖ ≤ C₁ / ‖z - p₁‖) ∧
      (∀ᵐ z ∂(volume : Measure ℂ), z ∈ tsupport (Work.Drive.clampedPullback (E.y i) (E.σ i) (E.ψ i)) →
        ‖gradient (Work.Drive.clampedPullback (E.y i) (E.ρ i) gB) z‖ ≤ C₂ / ‖z - p₂‖) := by
  classical
  have hσpos : ∀ j : ι, 0 ≤ E.σ j := fun j => le_of_lt (lt_trans (E.hspos j) (E.hsσ j))
  have hA_avoid : ∀ (j : ι), j ≠ E.ia → ∃ C : ℝ, 0 < C ∧ ∀ᵐ z ∂(volume : Measure ℂ),
      z ∈ tsupport (Work.Drive.clampedPullback (E.y j) (E.σ j) (E.ψ j)) →
        ‖gradient (Work.Drive.clampedPullback (E.y j) (E.ρ j) gA) z‖
          ≤ C / ‖z - ((chartAt ℂ (E.y j)) (E.y j) + ((E.σ j + 1 : ℝ) : ℂ))‖ := by
    intro j hj
    have ht : (0 : ℝ) < E.σ j + 1 := by linarith [hσpos j]
    exact bound_on_tsupport_of_avoid (Ω := Ω) (a := a) (y := E.y j) (g := gA)
      (ρ := E.ρ j) (σ := E.σ j) (t := E.σ j + 1) (W := E.ψ j)
      hgA (E.hσρ j) (E.htgt j) (E.hballΩ j) (E.ha_nmem j hj) (hσpos j) ht
  have hB_avoid : ∀ (j : ι), j ≠ E.ib → ∃ C : ℝ, 0 < C ∧ ∀ᵐ z ∂(volume : Measure ℂ),
      z ∈ tsupport (Work.Drive.clampedPullback (E.y j) (E.σ j) (E.ψ j)) →
        ‖gradient (Work.Drive.clampedPullback (E.y j) (E.ρ j) gB) z‖
          ≤ C / ‖z - ((chartAt ℂ (E.y j)) (E.y j) + ((E.σ j + 2 : ℝ) : ℂ))‖ := by
    intro j hj
    have ht : (0 : ℝ) < E.σ j + 2 := by linarith [hσpos j]
    exact bound_on_tsupport_of_avoid (Ω := Ω) (a := b) (y := E.y j) (g := gB)
      (ρ := E.ρ j) (σ := E.σ j) (t := E.σ j + 2) (W := E.ψ j)
      hgB (E.hσρ j) (E.htgt j) (E.hballΩ j) (E.hb_nmem j hj) (hσpos j) ht
  have hA_exp : ∃ C : ℝ, 0 < C ∧ ∀ᵐ z ∂(volume : Measure ℂ),
      z ∈ tsupport (Work.Drive.clampedPullback (E.y E.ia) (E.σ E.ia) (E.ψ E.ia)) →
        ‖gradient (Work.Drive.clampedPullback (E.y E.ia) (E.ρ E.ia) gA) z‖
          ≤ C / ‖z - (chartAt ℂ (E.y E.ia)) a‖ := by
    obtain ⟨r', hr'pos, H', -, hH'harm, hH'eq⟩ :=
      Work.Kernel.greenExpansion_chart (Ω := Ω) (c := a) (y := E.y E.ia) hΩo (hKΩ haK) hgA
        (E.ha_mem).1
    exact growth_on_tsupport_of_logExpansion (Ω := Ω) (a := a) (y := E.y E.ia) (g := gA)
      (ρ := E.ρ E.ia) (σ := E.σ E.ia) (δ := r') (H := H') (W := E.ψ E.ia)
      hgA (E.hσρ E.ia) (E.htgt E.ia) (E.hballΩ E.ia) hr'pos hH'harm hH'eq
  have hB_exp : ∃ C : ℝ, 0 < C ∧ ∀ᵐ z ∂(volume : Measure ℂ),
      z ∈ tsupport (Work.Drive.clampedPullback (E.y E.ib) (E.σ E.ib) (E.ψ E.ib)) →
        ‖gradient (Work.Drive.clampedPullback (E.y E.ib) (E.ρ E.ib) gB) z‖
          ≤ C / ‖z - (chartAt ℂ (E.y E.ib)) b‖ :=
    growth_on_tsupport_of_logExpansion (Ω := Ω) (a := b) (y := E.y E.ib) (g := gB)
      (ρ := E.ρ E.ib) (σ := E.σ E.ib) (δ := r) (H := H) (W := E.ψ E.ib)
      hgB (E.hσρ E.ib) (E.htgt E.ib) (E.hballΩ E.ib) hrpos hH
      (fun z hz _ => hueq z hz)
  have hdist : ∀ (w : ℂ) (t : ℝ), ‖(w + (t : ℂ)) - w‖ = |t| := by
    intro w t
    rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
  rcases eq_or_ne i E.ia with hia | hia
  · rw [hia]
    rcases eq_or_ne E.ia E.ib with hib | hib
    · -- both poles lie in this chart
      obtain ⟨C₁, hC₁, hb₁⟩ := hA_exp
      obtain ⟨C₂, hC₂, hb₂⟩ := hB_exp
      have hb₂' : ∀ᵐ z ∂(volume : Measure ℂ),
          z ∈ tsupport (Work.Drive.clampedPullback (E.y E.ia) (E.σ E.ia) (E.ψ E.ia)) →
            ‖gradient (Work.Drive.clampedPullback (E.y E.ia) (E.ρ E.ia) gB) z‖
              ≤ C₂ / ‖z - (chartAt ℂ (E.y E.ia)) b‖ := by
        rw [show E.ia = E.ib from hib]
        exact hb₂
      have hb_src : b ∈ (chartAt ℂ (E.y E.ia)).source := by
        rw [show chartAt ℂ (E.y E.ia) = chartAt ℂ (E.y E.ib) from
          congrArg (fun t => chartAt ℂ t) (congrArg E.y hib)]
        exact (E.hb_mem).1
      refine ⟨(chartAt ℂ (E.y E.ia)) a, (chartAt ℂ (E.y E.ia)) b, C₁, C₂,
        hC₁.le, hC₂.le, ?_, hb₁, hb₂'⟩
      intro h
      exact hab ((chartAt ℂ (E.y E.ia)).injOn (E.ha_mem).1 hb_src h)
    · -- pole of `gA` in this chart, pole of `gB` outside its closed `σ`-ball
      obtain ⟨C₁, hC₁, hb₁⟩ := hA_exp
      obtain ⟨C₂, hC₂, hb₂⟩ := hB_avoid E.ia hib
      refine ⟨(chartAt ℂ (E.y E.ia)) a,
        (chartAt ℂ (E.y E.ia)) (E.y E.ia) + ((E.σ E.ia + 2 : ℝ) : ℂ), C₁, C₂,
        hC₁.le, hC₂.le, ?_, hb₁, hb₂⟩
      intro h
      have h1 : dist ((chartAt ℂ (E.y E.ia)) a) ((chartAt ℂ (E.y E.ia)) (E.y E.ia))
          < E.s E.ia := (E.ha_mem).2
      rw [dist_eq_norm] at h1
      rw [h, hdist, abs_of_nonneg (by linarith [hσpos E.ia])] at h1
      have := E.hsσ E.ia
      linarith
  · rcases eq_or_ne i E.ib with hib | hib
    · -- pole of `gB` in this chart, pole of `gA` outside its closed `σ`-ball
      rw [hib]
      obtain ⟨C₁, hC₁, hb₁⟩ := hA_avoid E.ib (fun h => hia (hib.trans h))
      obtain ⟨C₂, hC₂, hb₂⟩ := hB_exp
      refine ⟨(chartAt ℂ (E.y E.ib)) (E.y E.ib) + ((E.σ E.ib + 1 : ℝ) : ℂ),
        (chartAt ℂ (E.y E.ib)) b, C₁, C₂, hC₁.le, hC₂.le, ?_, hb₁, hb₂⟩
      intro h
      have h1 : dist ((chartAt ℂ (E.y E.ib)) b) ((chartAt ℂ (E.y E.ib)) (E.y E.ib))
          < E.s E.ib := (E.hb_mem).2
      rw [dist_eq_norm] at h1
      rw [← h, hdist, abs_of_nonneg (by linarith [hσpos E.ib])] at h1
      have := E.hsσ E.ib
      linarith
    · -- both poles outside the closed `σ`-ball of the chart
      obtain ⟨C₁, hC₁, hb₁⟩ := hA_avoid i hia
      obtain ⟨C₂, hC₂, hb₂⟩ := hB_avoid i hib
      refine ⟨(chartAt ℂ (E.y i)) (E.y i) + ((E.σ i + 1 : ℝ) : ℂ),
        (chartAt ℂ (E.y i)) (E.y i) + ((E.σ i + 2 : ℝ) : ℂ), C₁, C₂,
        hC₁.le, hC₂.le, ?_, hb₁, hb₂⟩
      intro h
      have h4 : ((E.σ i + 1 : ℝ) : ℂ) ≠ ((E.σ i + 2 : ℝ) : ℂ) := by
        simp only [ne_eq, Complex.ofReal_inj]
        linarith
      exact h4 (add_left_cancel h)

/-! ## 4. The dominating function for the pairing integrand -/

lemma exists_integrable_domination {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] [DecidableEq X]
    {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X} (E : Work.Kernel.GreenCover ι Ω K a b)
    (hab : a ≠ b) (hΩo : IsOpen Ω) (haK : a ∈ K) (hbK : b ∈ K) (hKΩ : K ⊆ Ω)
    {gA gB χ : X → ℝ} (hgA : Work.SimplyConnected.ABS.IsGreenOn Ω a gA)
    (hgB : Work.SimplyConnected.ABS.IsGreenOn Ω b gB)
    (hχc1 : ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 (χ ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    (hχ1 : χ =ᶠ[nhds a] 1)
    (hψc1 : ∀ k i, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 ((E.ψ i) ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    {H : ℂ → ℝ} {r : ℝ} (hrpos : 0 < r) (hrρ : r ≤ E.ρ E.ib)
    (hpmem : (chartAt ℂ (E.y E.ib)) b ∈
      Metric.ball ((chartAt ℂ (E.y E.ib)) (E.y E.ib)) (E.ρ E.ib))
    (hH : InnerProductSpace.HarmonicOnNhd H (Metric.ball ((chartAt ℂ (E.y E.ib)) b) r))
    (hueq : ∀ z ∈ Metric.ball ((chartAt ℂ (E.y E.ib)) b) r,
      gB ((chartAt ℂ (E.y E.ib)).symm z)
        = -Real.log ‖z - (chartAt ℂ (E.y E.ib)) b‖ + H z)
    {Mb : ℝ} {Θ : ℕ → ℝ → ℝ}
    (hΘc1 : ∀ n, ContDiff ℝ 1 (Θ n))
    (hΘder : ∀ (n : ℕ) (w : ℝ), 0 ≤ deriv (Θ n) w ∧ deriv (Θ n) w ≤ 1)
    (hΘabs : ∀ (n : ℕ) (w : ℝ), |Θ n w| ≤ |w|)
    (i : ι) :
    ∃ g : ℂ → ℝ, Integrable g ∧ ∀ n : ℕ, ∀ᵐ z ∂(volume : Measure ℂ),
      ‖Work.Drive.clampedPullback (E.y i) (E.σ i) (E.ψ i) z *
        inner (𝕜 := ℝ) (gradient (Work.Drive.clampedPullback (E.y i) (E.ρ i) gB) z)
          (gradient (Work.Drive.clampedPullback (E.y i) (E.ρ i)
            (fun x : X => if x = a then Θ n (Mb + n) else χ x * Θ n (gA x))) z)‖ ≤ g z := by
  classical
  obtain ⟨p₁, p₂, C₁, C₂, hC₁, hC₂, hp, hbndA, hbndB⟩ :=
    growth_data E hab hΩo haK hbK hKΩ hgA hgB hrpos hrρ hpmem hH hueq i
  obtain ⟨K₁, B, hK₁, hB, htest⟩ :=
    exists_bound_gradient_plateau_test (Ω := Ω) (K := K) E hgA hχc1 hχ1 hΘc1 hΘder hΘabs i
  obtain ⟨hWc, hWcs⟩ :=
    Work.Drive.GreenRung.contDiff_clampedPullback_hasCompactSupport (x₀ := E.y i)
      (u := E.ψ i) (ρ := E.σ i) (ρ₀ := E.s i) (lt_trans (E.hspos i) (E.hsσ i))
      (le_of_lt (E.hspos i)) (E.hsσ i)
      ((Metric.ball_subset_ball (le_of_lt (E.hσρ i))).trans (E.htgt i)) (hψc1 i i)
      (fun x hx => (E.hψsupp i hx).2)
  have hvc : Continuous (fun z : ℂ => ‖Work.Drive.clampedPullback (E.y i) (E.σ i) (E.ψ i) z‖) :=
    hWc.continuous.norm
  have hvcs : HasCompactSupport
      (fun z : ℂ => ‖Work.Drive.clampedPullback (E.y i) (E.σ i) (E.ψ i) z‖) :=
    hWcs.norm
  have hint₁ : Integrable (fun z : ℂ =>
      (‖z - p₂‖)⁻¹ * ‖Work.Drive.clampedPullback (E.y i) (E.σ i) (E.ψ i) z‖) :=
    Work.Analysis.integrable_inv_norm_mul_of_hasCompactSupport p₂ _ hvc hvcs
  have hint₂ : Integrable (fun z : ℂ =>
      (‖z - p₁‖)⁻¹ * (‖z - p₂‖)⁻¹ * ‖Work.Drive.clampedPullback (E.y i) (E.σ i) (E.ψ i) z‖) :=
    Work.Analysis.integrable_inv_norm_mul_two hp _ hvc hvcs
  set D : ℝ := max (C₂ * K₁) (C₂ * B * C₁) with hD
  have hDnn : 0 ≤ D := by
    rw [hD]
    exact le_trans (mul_nonneg hC₂ hK₁) (le_max_left _ _)
  have hDpos : 0 < D + 1 := by linarith
  refine ⟨fun z : ℂ => (D + 1) *
      ((‖z - p₂‖)⁻¹ * ‖Work.Drive.clampedPullback (E.y i) (E.σ i) (E.ψ i) z‖ +
       (‖z - p₁‖)⁻¹ * (‖z - p₂‖)⁻¹ *
         ‖Work.Drive.clampedPullback (E.y i) (E.σ i) (E.ψ i) z‖),
    (hint₁.add hint₂).const_mul (D + 1), ?_⟩
  intro n
  filter_upwards [hbndA, hbndB, htest n] with z hA hB hT
  by_cases hz : z ∈ tsupport (Work.Drive.clampedPullback (E.y i) (E.σ i) (E.ψ i))
  · have hgA' : ‖gradient (Work.Drive.clampedPullback (E.y i) (E.ρ i) gA) z‖
        ≤ C₁ * (‖z - p₁‖)⁻¹ := by
      rw [div_eq_mul_inv] at hA
      exact hA hz
    have hgB' : ‖gradient (Work.Drive.clampedPullback (E.y i) (E.ρ i) gB) z‖
        ≤ C₂ * (‖z - p₂‖)⁻¹ := by
      rw [div_eq_mul_inv] at hB
      exact hB hz
    have hT' := hT hz
    set v : ℝ := ‖Work.Drive.clampedPullback (E.y i) (E.σ i) (E.ψ i) z‖ with hv
    set a₁ : ℝ := (‖z - p₁‖)⁻¹ with ha₁
    set a₂ : ℝ := (‖z - p₂‖)⁻¹ with ha₂
    have hv0 : 0 ≤ v := norm_nonneg _
    have ha₁0 : 0 ≤ a₁ := inv_nonneg.mpr (norm_nonneg _)
    have ha₂0 : 0 ≤ a₂ := inv_nonneg.mpr (norm_nonneg _)
    have hkey : v * (C₂ * a₂) * (K₁ + B * (C₁ * a₁))
        ≤ (D + 1) * (a₂ * v + a₁ * a₂ * v) := by
      have h1 : C₂ * K₁ ≤ D + 1 := by rw [hD]; linarith [le_max_left (C₂ * K₁) (C₂ * B * C₁)]
      have h2 : C₂ * B * C₁ ≤ D + 1 := by
        rw [hD]; linarith [le_max_right (C₂ * K₁) (C₂ * B * C₁)]
      have e : v * (C₂ * a₂) * (K₁ + B * (C₁ * a₁))
          = v * a₂ * (C₂ * K₁) + (v * a₁ * a₂) * (C₂ * B * C₁) := by ring
      have hnn1 : 0 ≤ v * a₂ := mul_nonneg hv0 ha₂0
      have hnn2 : 0 ≤ v * a₁ * a₂ := by positivity
      rw [e]
      have hle1 : v * a₂ * (C₂ * K₁) ≤ v * a₂ * (D + 1) :=
        mul_le_mul_of_nonneg_left h1 hnn1
      have hle2 : v * a₁ * a₂ * (C₂ * B * C₁) ≤ v * a₁ * a₂ * (D + 1) :=
        mul_le_mul_of_nonneg_left h2 hnn2
      calc v * a₂ * (C₂ * K₁) + (v * a₁ * a₂) * (C₂ * B * C₁)
          ≤ v * a₂ * (D + 1) + (v * a₁ * a₂) * (D + 1) := add_le_add hle1 hle2
        _ = (D + 1) * (a₂ * v + a₁ * a₂ * v) := by ring
    calc ‖Work.Drive.clampedPullback (E.y i) (E.σ i) (E.ψ i) z *
          inner (𝕜 := ℝ) (gradient (Work.Drive.clampedPullback (E.y i) (E.ρ i) gB) z)
            (gradient (Work.Drive.clampedPullback (E.y i) (E.ρ i)
              (fun x : X => if x = a then Θ n (Mb + n) else χ x * Θ n (gA x))) z)‖
        ≤ v * ‖inner (𝕜 := ℝ) (gradient (Work.Drive.clampedPullback (E.y i) (E.ρ i) gB) z)
            (gradient (Work.Drive.clampedPullback (E.y i) (E.ρ i)
              (fun x : X => if x = a then Θ n (Mb + n) else χ x * Θ n (gA x))) z)‖ := by
          rw [hv]; exact norm_mul_le _ _
      _ ≤ v * (‖gradient (Work.Drive.clampedPullback (E.y i) (E.ρ i) gB) z‖ *
            ‖gradient (Work.Drive.clampedPullback (E.y i) (E.ρ i)
              (fun x : X => if x = a then Θ n (Mb + n) else χ x * Θ n (gA x))) z‖) :=
          mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) hv0
      _ ≤ v * (C₂ * a₂) * (K₁ + B * (C₁ * a₁)) := by
          have h1 : ‖gradient (Work.Drive.clampedPullback (E.y i) (E.ρ i) gB) z‖ ≤ C₂ * a₂ := by
            rw [ha₂]; exact hgB'
          have h2 : ‖gradient (Work.Drive.clampedPullback (E.y i) (E.ρ i)
              (fun x : X => if x = a then Θ n (Mb + n) else χ x * Θ n (gA x))) z‖
              ≤ K₁ + B * (C₁ * a₁) := by
            have h3 : ‖gradient (Work.Drive.clampedPullback (E.y i) (E.ρ i) gA) z‖ ≤ C₁ * a₁ := by
              rw [ha₁]; exact hgA'
            nlinarith [hT', hB, h3, norm_nonneg (gradient (Work.Drive.clampedPullback (E.y i) (E.ρ i) gA) z)]
          have hnn : 0 ≤ C₂ * a₂ := mul_nonneg hC₂ ha₂0
          calc v * (‖gradient (Work.Drive.clampedPullback (E.y i) (E.ρ i) gB) z‖ *
                ‖gradient (Work.Drive.clampedPullback (E.y i) (E.ρ i)
                  (fun x : X => if x = a then Θ n (Mb + n) else χ x * Θ n (gA x))) z‖)
              ≤ v * ((C₂ * a₂) * (K₁ + B * (C₁ * a₁))) :=
                mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) hnn) hv0
            _ = v * (C₂ * a₂) * (K₁ + B * (C₁ * a₁)) := by ring
      _ ≤ (D + 1) * (a₂ * v + a₁ * a₂ * v) := hkey
      _ = (D + 1) * ((‖z - p₂‖)⁻¹ * ‖Work.Drive.clampedPullback (E.y i) (E.σ i) (E.ψ i) z‖ +
       (‖z - p₁‖)⁻¹ * (‖z - p₂‖)⁻¹ *
         ‖Work.Drive.clampedPullback (E.y i) (E.σ i) (E.ψ i) z‖) := by
          rw [hv, ha₁, ha₂]
  · have hz0 : Work.Drive.clampedPullback (E.y i) (E.σ i) (E.ψ i) z = 0 :=
      image_eq_zero_of_notMem_tsupport hz
    simp [hz0]

/-! ## 5. Eventual agreement of the clamped pullbacks of the test family -/

lemma eventually_eventuallyEq_clampedPullback_plateau {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] [DecidableEq X]
    {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X} (E : Work.Kernel.GreenCover ι Ω K a b)
    (hΩo : IsOpen Ω) (haΩ : a ∈ Ω) {gA χ : X → ℝ}
    (hgA : Work.SimplyConnected.ABS.IsGreenOn Ω a gA) (hχΩ : tsupport χ ⊆ Ω)
    {Mb : ℝ} {Θ : ℕ → ℝ → ℝ}
    (hΘid : ∀ (n : ℕ) (w : ℝ), 0 ≤ w → w ≤ (Mb + n) / 4 → Θ n w = w) (i : ι) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ᶠ n in Filter.atTop,
      Work.Drive.clampedPullback (E.y i) (E.ρ i)
          (fun x : X => if x = a then Θ n (Mb + n) else χ x * Θ n (gA x))
        =ᶠ[𝓝 z] Work.Drive.clampedPullback (E.y i) (E.ρ i) (fun x : X => χ x * gA x) := by
  classical
  set c := chartAt ℂ (E.y i) with hc
  have hnull : volume (Metric.sphere (c (E.y i)) (E.ρ i) ∪ {c a}) = 0 :=
    MeasureTheory.measure_union_null
      (MeasureTheory.Measure.addHaar_sphere volume (c (E.y i)) (E.ρ i))
      (measure_singleton (c a))
  filter_upwards [compl_mem_ae_iff.mpr hnull] with z hz
  have hzne : z ≠ c a := fun h => hz (Or.inr h)
  have haC : a ∉ ({a} : Set X)ᶜ := by simp
  by_cases hzball : z ∈ Metric.ball (c (E.y i)) (E.ρ i)
  · have hztgt : z ∈ c.target := (E.htgt i) hzball
    have hzsrc : c.symm z ∈ c.source := c.map_target hztgt
    have hzright : c (c.symm z) = z := c.right_inv hztgt
    by_cases hxΩ : c.symm z ∈ Ω
    · -- the pole `a` is not met: `gA` is harmonic and positive at the preimage
      have hxne : c.symm z ≠ a := fun h => hzne (by rw [← hzright, h])
      have hharm : Submission.HarmonicOnXAt gA (c.symm z) := hgA.2.1 _ ⟨hxΩ, hxne⟩
      have hpos : 0 < gA (c.symm z) := hgA.1 _ hxΩ hxne
      set cx := chartAt ℂ (c.symm z) with hcx
      have hxsrc : c.symm z ∈ cx.source := mem_chart_source ℂ _
      have hCh := (Submission.HarmonicOnXAt_iff_chart (u := gA) (x := c.symm z) (y := c.symm z)
        hxsrc).mp hharm
      have hval : (gA ∘ cx.symm) (cx (c.symm z)) = gA (c.symm z) := by
        simp only [Function.comp_apply, cx.left_inv hxsrc]
      have hmem : {y : X | 0 < gA y ∧ gA y < gA (c.symm z) + 1} ∈ 𝓝 (c.symm z) := by
        have hmemIoo : (gA ∘ cx.symm) (cx (c.symm z)) ∈ Set.Ioo (0 : ℝ) (gA (c.symm z) + 1) := by
          rw [hval]
          exact ⟨hpos, lt_add_one _⟩
        have hO : {w : ℂ | 0 < (gA ∘ cx.symm) w ∧ (gA ∘ cx.symm) w < gA (c.symm z) + 1}
            ∈ 𝓝 (cx (c.symm z)) :=
          hCh.1.continuousAt.eventually (isOpen_Ioo.mem_nhds hmemIoo)
        have hpre : cx ⁻¹' {w : ℂ | 0 < (gA ∘ cx.symm) w ∧ (gA ∘ cx.symm) w < gA (c.symm z) + 1}
            ∈ 𝓝 (c.symm z) :=
          (cx.continuousAt hxsrc).preimage_mem_nhds hO
        refine Filter.mem_of_superset (Filter.inter_mem hpre (cx.open_source.mem_nhds hxsrc)) ?_
        intro y hy
        obtain ⟨⟨h1, h2⟩, hy2⟩ := hy
        have hyv : (gA ∘ cx.symm) (cx y) = gA y := by
          simp only [Function.comp_apply, cx.left_inv hy2]
        exact ⟨by rw [← hyv]; exact h1, by rw [← hyv]; exact h2⟩
      set V : Set X := {y : X | 0 < gA y ∧ gA y < gA (c.symm z) + 1} ∩ ({a} : Set X)ᶜ with hV
      have hVmem : V ∈ 𝓝 (c.symm z) :=
        Filter.inter_mem hmem ((isClosed_singleton.isOpen_compl).mem_nhds hxne)
      have hVnn : ∀ y ∈ V, 0 ≤ gA y := fun y hy => (hy.1).1.le
      have hVle : ∀ y ∈ V, gA y ≤ gA (c.symm z) + 1 := fun y hy => (hy.1).2.le
      have hVnota : a ∉ V := fun h => haC h.2
      obtain ⟨N, hN⟩ := exists_nat_ge (4 * (gA (c.symm z) + 1) - Mb)
      have hN' : gA (c.symm z) + 1 ≤ (Mb + (N : ℝ)) / 4 := by
        have h1 : 4 * (gA (c.symm z) + 1) - Mb ≤ (N : ℝ) := hN
        linarith
      refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
      have hn' : gA (c.symm z) + 1 ≤ (Mb + (n : ℝ)) / 4 := by
        have h1 : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have h2 : Mb + (N : ℝ) ≤ Mb + (n : ℝ) := by linarith
        have h3 : (Mb + (N : ℝ)) / 4 ≤ (Mb + (n : ℝ)) / 4 := by linarith
        linarith [hN']
      have hVsrc : V ∩ c.source ∈ 𝓝 (c.symm z) :=
        Filter.inter_mem hVmem (c.open_source.mem_nhds hzsrc)
      have hWmem : c '' (V ∩ c.source) ∈ 𝓝 z := by
        have := c.image_mem_nhds hzsrc hVsrc
        rwa [hzright] at this
      refine Filter.eventually_iff_exists_mem.mpr ⟨c '' (V ∩ c.source), hWmem, fun w hw => ?_⟩
      obtain ⟨y, ⟨hyV, hysrc⟩, hyw⟩ := hw
      have hysymm : c.symm w = y := by rw [← hyw, c.left_inv hysrc]
      by_cases hwball : w ∈ Metric.ball (c (E.y i)) (E.ρ i)
      · rw [Work.Drive.clampedPullback_apply_of_mem hwball,
          Work.Drive.clampedPullback_apply_of_mem hwball, hysymm]
        have hya : y ≠ a := fun h => hVnota (h ▸ hyV)
        rw [if_neg hya, hΘid n (gA y) (hVnn y hyV) (by linarith [hVle y hyV, hn'])]
      · rw [Work.Drive.clampedPullback_apply_of_notMem hwball,
          Work.Drive.clampedPullback_apply_of_notMem hwball]
    · -- the preimage lies outside `Ω`: `χ` vanishes near it
      have hxnotin : c.symm z ∉ tsupport χ := fun h => hxΩ (hχΩ h)
      have hmem : (tsupport χ)ᶜ ∈ 𝓝 (c.symm z) :=
        (isClosed_tsupport χ).isOpen_compl.mem_nhds hxnotin
      have hxne : c.symm z ≠ a := fun h => hxΩ (by rw [h]; exact haΩ)
      set V : Set X := (tsupport χ)ᶜ ∩ ({a} : Set X)ᶜ with hV
      have hVmem : V ∈ 𝓝 (c.symm z) :=
        Filter.inter_mem hmem ((isClosed_singleton.isOpen_compl).mem_nhds hxne)
      have hVχ : ∀ y ∈ V, χ y = 0 := fun y hy =>
        image_eq_zero_of_notMem_tsupport hy.1
      have hVnota : a ∉ V := fun h => haC h.2
      have hVsrc : V ∩ c.source ∈ 𝓝 (c.symm z) :=
        Filter.inter_mem hVmem (c.open_source.mem_nhds hzsrc)
      have hWmem : c '' (V ∩ c.source) ∈ 𝓝 z := by
        have := c.image_mem_nhds hzsrc hVsrc
        rwa [hzright] at this
      refine Filter.eventually_atTop.mpr ⟨0, fun n _ => ?_⟩
      refine Filter.eventually_iff_exists_mem.mpr ⟨c '' (V ∩ c.source), hWmem, fun w hw => ?_⟩
      obtain ⟨y, ⟨hyV, hysrc⟩, hyw⟩ := hw
      have hysymm : c.symm w = y := by rw [← hyw, c.left_inv hysrc]
      have hyχ : χ y = 0 := hVχ y hyV
      have hya : y ≠ a := fun h => hVnota (h ▸ hyV)
      by_cases hwball : w ∈ Metric.ball (c (E.y i)) (E.ρ i)
      · rw [Work.Drive.clampedPullback_apply_of_mem hwball,
          Work.Drive.clampedPullback_apply_of_mem hwball, hysymm, if_neg hya, hyχ]
        ring
      · rw [Work.Drive.clampedPullback_apply_of_notMem hwball,
          Work.Drive.clampedPullback_apply_of_notMem hwball]
  · -- `z` is strictly outside the closed clamping ball
    have hzout : z ∉ Metric.closedBall (c (E.y i)) (E.ρ i) := by
      intro hcon
      exact hz (Or.inl (Metric.mem_sphere.mpr
        (le_antisymm (Metric.mem_closedBall.mp hcon) (not_lt.mp hzball))))
    refine Filter.eventually_atTop.mpr ⟨0, fun n _ => ?_⟩
    refine Filter.eventually_iff_exists_mem.mpr
      ⟨(Metric.closedBall (c (E.y i)) (E.ρ i))ᶜ, isClosed_closedBall.isOpen_compl.mem_nhds hzout,
        fun w hw => ?_⟩
    have hwball : w ∉ Metric.ball (c (E.y i)) (E.ρ i) := fun h =>
      hw (Metric.ball_subset_closedBall h)
    rw [Work.Drive.clampedPullback_apply_of_notMem hwball,
      Work.Drive.clampedPullback_apply_of_notMem hwball]

end Work.Kernel