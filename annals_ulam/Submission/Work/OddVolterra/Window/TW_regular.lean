import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Window.WindowDefs
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.Window.WindowBase
import Submission.Work.OddVolterra.Window.WindowFed
import Submission.Work.OddVolterra.Window.manifest_eq
import Submission.Work.OddVolterra.Existence.theta_lipschitz_state_ball
import Submission.Work.OddVolterra.Existence.aw_contDiffOn_awGodd
import Submission.Work.Anchor.ThetaM_contDiffOn_wide

/-!
# Regularity of the truncated `Θ`-datum `TW` of the odd transition window

`TW n h s σ z = chiT s σ z • thetac n h s σ z` is the `Θ`-datum fed to the long-interval
Volterra engine (`Work.VolterraLong.volterra_long_exists`, whose hypotheses `hΘ_cont` and
`hΘ_lip` it supplies).  Its definition clamps the paper's kernel: on the triangle `s < σ` it is
the paper's `Theta`, on and below the diagonal it is the manifest diagonal value
`ThetaM n h s s z`.

The two things proved here are

* `Continuous (fun p : ℝ × ℝ × St => TW n h p.1 p.2.1 p.2.2)`, and
* the Lipschitz estimate `‖TW n h s σ z - TW n h s σ z'‖ ≤ L ‖z - z'‖` for `s, σ` in the window
  `[7/10, 19/20]` and `z, z'` in the unit ball around `baseState σ`, with `L` independent of all
  variables.

Both rest on the following structural facts.

* The *cut-off* `chiT s σ z = cs s · cs σ · cz ‖z - baseState σ‖` is continuous, and it vanishes
  off the region `twRegion = {3/5 < s < 1, 3/5 < σ < 1, z 0 > 1/4, z 1 > 1/4}`:  indeed
  `cs t ≠ 0` forces `t ∈ (0.665, 0.985)` and `cz w ≠ 0` forces `w < 2/5`, whence
  `z 0 ≥ profileX σ - 2/5 ≥ 7/10 - 2/5 = 3/10 > 1/4`.
* On `twRegion` the clamped datum equals `ΘM n h s (max s σ) z`: on the triangle `s < σ` the
  Abel radicands are positive (`|z 0|, |z 1| > 1/5`, `σ + a > 1/10`), so the paper's kernel and
  its manifest representative agree (`Window.manifest_eq.ThetaM_eq_Theta`).
* `(s,σ,z) ↦ ThetaM n h s σ z` is `C^∞` on `Work.Anchor.Good`
  (`Work.Anchor.ThetaM_contDiffOn_Good`), a region containing the compact box
  `twBox D = {3/5 ≤ s ≤ 1, 3/5 ≤ σ ≤ 1, z 0 ≥ 1/4, z 1 ≥ 1/4, |z i| ≤ D}`.
  Hence (i) `ΘM` is bounded on each `twBox D` and (ii) its `fderiv` is bounded there; the
  segment mean value inequality then gives the state Lipschitz estimate on the box, uniformly
  over the window parameters.
-/

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

open Work.OddVolterra

/-! ## 1. General auxiliary lemmas -/

/-- Lipschitz bound for the product `x ↦ f x • g x` of a bounded Lipschitz scalar function and a
bounded Lipschitz vector function. -/
lemma tw_lipschitz_smul_of_lipschitz_of_bounded {α : Type*} [NormedAddCommGroup α]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : α → ℝ} {g : α → F} {s : Set α} {Mf Mg Kf Kg : ℝ}
    (hfM : ∀ x ∈ s, |f x| ≤ Mf) (hgM : ∀ x ∈ s, ‖g x‖ ≤ Mg)
    (hfK : ∀ x ∈ s, ∀ y ∈ s, |f x - f y| ≤ Kf * ‖x - y‖)
    (hgK : ∀ x ∈ s, ∀ y ∈ s, ‖g x - g y‖ ≤ Kg * ‖x - y‖) :
    ∀ x ∈ s, ∀ y ∈ s,
      ‖f x • g x - f y • g y‖ ≤ (Mf * Kg + Kf * Mg) * ‖x - y‖ := by
  intro x hx y hy
  have hMf : 0 ≤ Mf := le_trans (abs_nonneg _) (hfM x hx)
  have hMg : 0 ≤ Mg := le_trans (norm_nonneg _) (hgM y hy)
  have hKfd : 0 ≤ Kf * ‖x - y‖ := le_trans (abs_nonneg _) (hfK x hx y hy)
  have hsplit : f x • g x - f y • g y = f x • (g x - g y) + (f x - f y) • g y := by
    rw [smul_sub, sub_smul]; abel
  rw [hsplit]
  calc ‖f x • (g x - g y) + (f x - f y) • g y‖
      ≤ ‖f x • (g x - g y)‖ + ‖(f x - f y) • g y‖ := norm_add_le _ _
    _ = |f x| * ‖g x - g y‖ + |f x - f y| * ‖g y‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ Mf * (Kg * ‖x - y‖) + (Kf * ‖x - y‖) * Mg :=
          add_le_add (mul_le_mul (hfM x hx) (hgK x hx y hy) (norm_nonneg _) hMf)
            (mul_le_mul (hfK x hx y hy) (hgM y hy) (norm_nonneg _) hKfd)
    _ = (Mf * Kg + Kf * Mg) * ‖x - y‖ := by ring

/-- A point of the segment from `u` to `v` at distance exactly `r` from `c`, when `u` is strictly
inside and `v` outside the ball of radius `r` around `c`. -/
lemma tw_exists_crossing {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c u v : E} {r : ℝ} (hu : ‖u - c‖ < r) (hv : r ≤ ‖v - c‖) :
    ∃ t ∈ Set.Icc (0:ℝ) 1, ‖u + t • (v - u) - c‖ = r ∧
      ‖u - (u + t • (v - u))‖ ≤ ‖u - v‖ := by
  have hcont : ContinuousOn (fun t : ℝ => ‖u + t • (v - u) - c‖) (Set.Icc (0:ℝ) 1) := by fun_prop
  have h0 : ‖u + (0:ℝ) • (v - u) - c‖ = ‖u - c‖ := by simp
  have h1 : ‖u + (1:ℝ) • (v - u) - c‖ = ‖v - c‖ := by simp
  have hmem : r ∈ Set.Icc (‖u + (0:ℝ) • (v - u) - c‖) (‖u + (1:ℝ) • (v - u) - c‖) := by
    rw [h0, h1]; exact ⟨le_of_lt hu, hv⟩
  obtain ⟨t, ht, htr⟩ := (intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hcont) hmem
  refine ⟨t, ht, htr, ?_⟩
  have hkey : u - (u + t • (v - u)) = t • (u - v) := by
    rw [smul_sub, smul_sub]; abel
  rw [hkey, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact mul_le_of_le_one_left (norm_nonneg _) ht.2

/-- **Support extension.**  A function which vanishes outside the ball of radius `r` around `c`
and is `M`-Lipschitz on the ball of radius `R ≥ r` is `M`-Lipschitz everywhere. -/
lemma tw_lipschitz_of_support_subset_of_lipschitz_on_closedBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F]
    {c : E} {G : E → F} {r R M : ℝ} (hrR : r ≤ R) (hM : 0 ≤ M)
    (hsupp : ∀ z : E, r ≤ ‖z - c‖ → G z = 0)
    (hlip : ∀ z ∈ Metric.closedBall c R, ∀ z' ∈ Metric.closedBall c R,
      ‖G z - G z'‖ ≤ M * ‖z - z'‖) :
    ∀ z z' : E, ‖G z - G z'‖ ≤ M * ‖z - z'‖ := by
  intro z z'
  by_cases h1 : r ≤ ‖z - c‖
  · by_cases h2 : r ≤ ‖z' - c‖
    · rw [hsupp z h1, hsupp z' h2, sub_self, norm_zero]
      exact mul_nonneg hM (norm_nonneg _)
    · obtain ⟨t, ht, htr, htuv⟩ := tw_exists_crossing (c := c) (u := z') (v := z)
        (not_le.mp h2) h1
      have hmem : z' + t • (z - z') ∈ Metric.closedBall c R := by
        rw [Metric.mem_closedBall, dist_eq_norm, htr]; exact hrR
      have hz' : z' ∈ Metric.closedBall c R := by
        rw [Metric.mem_closedBall, dist_eq_norm]; exact le_trans (not_le.mp h2).le hrR
      have hGz : G z = 0 := hsupp z h1
      have hGw : G (z' + t • (z - z')) = 0 := hsupp _ htr.ge
      calc ‖G z - G z'‖ = ‖G z' - G (z' + t • (z - z'))‖ := by rw [norm_sub_rev, hGz, hGw]
        _ ≤ M * ‖z' - (z' + t • (z - z'))‖ := hlip z' hz' _ hmem
        _ ≤ M * ‖z' - z‖ := mul_le_mul_of_nonneg_left htuv hM
        _ = M * ‖z - z'‖ := by rw [norm_sub_rev]
  · by_cases h2 : r ≤ ‖z' - c‖
    · obtain ⟨t, ht, htr, htuv⟩ := tw_exists_crossing (c := c) (u := z) (v := z')
        (not_le.mp h1) h2
      have hmem : z + t • (z' - z) ∈ Metric.closedBall c R := by
        rw [Metric.mem_closedBall, dist_eq_norm, htr]; exact hrR
      have hz : z ∈ Metric.closedBall c R := by
        rw [Metric.mem_closedBall, dist_eq_norm]; exact le_trans (not_le.mp h1).le hrR
      have hGz' : G z' = 0 := hsupp z' h2
      have hGw : G (z + t • (z' - z)) = 0 := hsupp _ htr.ge
      calc ‖G z - G z'‖ = ‖G z - G (z + t • (z' - z))‖ := by rw [hGz', hGw]
        _ ≤ M * ‖z - (z + t • (z' - z))‖ := hlip z hz _ hmem
        _ ≤ M * ‖z - z'‖ := mul_le_mul_of_nonneg_left htuv hM
    · have hz : z ∈ Metric.closedBall c R := by
        rw [Metric.mem_closedBall, dist_eq_norm]; exact le_trans (not_le.mp h1).le hrR
      have hz' : z' ∈ Metric.closedBall c R := by
        rw [Metric.mem_closedBall, dist_eq_norm]; exact le_trans (not_le.mp h2).le hrR
      exact hlip z hz z' hz'

/-- **Mean value inequality along a segment.**  If `f` is differentiable on a set `K` containing
the whole segment from `x` to `y`, and `‖fderiv f‖ ≤ M` on `K`, then
`‖f y - f x‖ ≤ M ‖y - x‖`. -/
lemma tw_norm_sub_le_of_norm_fderiv_le_of_segment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {K : Set E} {M : ℝ} (hM : 0 ≤ M)
    (hdiff : ∀ z ∈ K, DifferentiableAt ℝ f z)
    (hbd : ∀ z ∈ K, ‖fderiv ℝ f z‖ ≤ M)
    {x y : E} (hseg : ∀ t ∈ Set.Icc (0:ℝ) 1, x + t • (y - x) ∈ K) :
    ‖f y - f x‖ ≤ M * ‖y - x‖ := by
  have hderiv : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivWithinAt (fun t : ℝ => f (x + t • (y - x)))
        ((fderiv ℝ f (x + t • (y - x))) (y - x)) (Set.Icc (0:ℝ) 1) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) t := by
      have := ((hasDerivAt_id t).smul_const (y - x)).const_add x
      simpa using this
    have h2 : HasFDerivAt f (fderiv ℝ f (x + t • (y - x))) (x + t • (y - x)) :=
      (hdiff _ (hseg t ht)).hasFDerivAt
    exact (h2.comp_hasDerivAt t h1).hasDerivWithinAt
  have hbd' : ∀ t ∈ Set.Ico (0:ℝ) 1,
      ‖(fderiv ℝ f (x + t • (y - x))) (y - x)‖ ≤ M * ‖y - x‖ := by
    intro t ht
    have ht' : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1, le_of_lt ht.2⟩
    calc ‖(fderiv ℝ f (x + t • (y - x))) (y - x)‖
        ≤ ‖fderiv ℝ f (x + t • (y - x))‖ * ‖y - x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * ‖y - x‖ := mul_le_mul_of_nonneg_right (hbd _ (hseg t ht')) (norm_nonneg _)
  have hmain := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun t : ℝ => f (x + t • (y - x)))
    (a := 0) (b := 1) (f' := fun t => (fderiv ℝ f (x + t • (y - x))) (y - x))
    (C := M * ‖y - x‖) hderiv hbd' 1 (by norm_num)
  simpa using hmain

/-- **Glue lemma.**  If `χ` is continuous, vanishes off the open set `U`, and `ψ` is continuous
and locally bounded on `U`, then `χ • ψ` is continuous. -/
lemma tw_continuous_smul_of_continuous_of_continuousOn {X : Type*} [TopologicalSpace X]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {χ : X → ℝ} {ψ : X → F} {U : Set X} (hU : IsOpen U)
    (hχ : Continuous χ) (hχ0 : ∀ x ∉ U, χ x = 0) (hψ : ContinuousOn ψ U)
    (hbd : ∀ x : X, ∃ C : ℝ, ∃ V ∈ 𝓝 x, ∀ y ∈ V, y ∈ U → ‖ψ y‖ ≤ C) :
    Continuous (fun x => χ x • ψ x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ U
  · exact (hχ.continuousOn.smul hψ).continuousAt (hU.mem_nhds hx)
  · obtain ⟨C, V, hV, hCV⟩ := hbd x
    have hχx : χ x = 0 := hχ0 x hx
    have hev : ∀ᶠ y in 𝓝 x, ‖χ y • ψ y‖ ≤ max C 0 * ‖χ y‖ := by
      filter_upwards [hV] with y hy
      by_cases hyU : y ∈ U
      · calc ‖χ y • ψ y‖ ≤ ‖χ y‖ * ‖ψ y‖ := norm_smul_le _ _
          _ ≤ ‖χ y‖ * C := mul_le_mul_of_nonneg_left (hCV y hy hyU) (norm_nonneg _)
          _ ≤ ‖χ y‖ * max C 0 := mul_le_mul_of_nonneg_left (le_max_left C 0) (norm_nonneg _)
          _ = max C 0 * ‖χ y‖ := by ring
      · rw [hχ0 y hyU, zero_smul, norm_zero]
        exact mul_nonneg (le_max_right _ _) (norm_nonneg _)
    have h1 : Filter.Tendsto (fun y => ‖χ y‖) (𝓝 x) (𝓝 0) := by
      rw [← tendsto_zero_iff_norm_tendsto_zero]
      have h2 : Filter.Tendsto χ (𝓝 x) (𝓝 (χ x)) := hχ.continuousAt
      rwa [hχx] at h2
    have hlim : Filter.Tendsto (fun y => max C 0 * ‖χ y‖) (𝓝 x) (𝓝 0) := by
      simpa using h1.const_mul (max C 0)
    have h2 : Filter.Tendsto (fun y => ‖χ y • ψ y‖) (𝓝 x) (𝓝 0) :=
      squeeze_zero' (Filter.Eventually.of_forall fun y => norm_nonneg _) hev hlim
    have h3 : Filter.Tendsto (fun y => χ y • ψ y) (𝓝 x) (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr h2
    have h4 : χ x • ψ x = 0 := by rw [hχ0 x hx, zero_smul]
    simpa [ContinuousAt, h4] using h3

/-! ## 2. The region supporting the cut-off -/

/-- The open region on which the cut-off `chiT` may be non-zero (and where all the manifest data
is well defined). -/
def twRegion : Set (ℝ × ℝ × St) :=
  {p | 3 / 5 < p.1 ∧ p.1 < 1 ∧ 3 / 5 < p.2.1 ∧ p.2.1 < 1 ∧
    1 / 4 < p.2.2 0 ∧ 1 / 4 < p.2.2 1}

lemma tw_isOpen_twRegion : IsOpen twRegion := by
  have h1 : Continuous (fun p : ℝ × ℝ × St => p.1) := continuous_fst
  have h2 : Continuous (fun p : ℝ × ℝ × St => p.2.1) := continuous_fst.comp continuous_snd
  have h3 : Continuous (fun p : ℝ × ℝ × St => p.2.2 0) :=
    (continuous_apply 0).comp (continuous_snd.comp continuous_snd)
  have h4 : Continuous (fun p : ℝ × ℝ × St => p.2.2 1) :=
    (continuous_apply 1).comp (continuous_snd.comp continuous_snd)
  have h : twRegion = (fun p : ℝ × ℝ × St => p.1) ⁻¹' Set.Ioo (3 / 5) 1 ∩
      ((fun p : ℝ × ℝ × St => p.2.1) ⁻¹' Set.Ioo (3 / 5) 1 ∩
      ((fun p : ℝ × ℝ × St => p.2.2 0) ⁻¹' Set.Ioi (1 / 4) ∩
       (fun p : ℝ × ℝ × St => p.2.2 1) ⁻¹' Set.Ioi (1 / 4))) := by
    ext p; simp [twRegion, Set.mem_Ioo, Set.mem_Ioi, and_assoc]
  rw [h]
  exact (isOpen_Ioo.preimage h1).inter ((isOpen_Ioo.preimage h2).inter
    ((isOpen_Ioi.preimage h3).inter (isOpen_Ioi.preimage h4)))

lemma tw_cs_ne_zero_lower {t : ℝ} (h : (cs : ℝ → ℝ) t ≠ 0) : 3 / 5 < t := by
  by_contra hcon
  rw [not_lt] at hcon
  refine h (cs_eq_zero ?_)
  rw [abs_of_nonpos (by rw [wCenter]; linarith), wCenter]
  linarith

lemma tw_cs_ne_zero_upper {t : ℝ} (h : (cs : ℝ → ℝ) t ≠ 0) : t < 1 := by
  by_contra hcon
  rw [not_lt] at hcon
  refine h (cs_eq_zero ?_)
  rw [abs_of_nonneg (by rw [wCenter]; linarith), wCenter]
  linarith

/-- The cut-off vanishes off `twRegion`. -/
lemma tw_chiT_eq_zero {p : ℝ × ℝ × St} (hp : p ∉ twRegion) :
    chiT p.1 p.2.1 p.2.2 = 0 := by
  by_contra h
  have h1 : (cs : ℝ → ℝ) p.1 ≠ 0 := fun h0 => h (by simp [chiT, h0])
  have h2 : (cs : ℝ → ℝ) p.2.1 ≠ 0 := fun h0 => h (by simp [chiT, h0])
  have h3 : (cz : ℝ → ℝ) ‖p.2.2 - baseState p.2.1‖ ≠ 0 := fun h0 => h (by simp [chiT, h0])
  have hs1 : 3 / 5 < p.1 := tw_cs_ne_zero_lower h1
  have hs2 : p.1 < 1 := tw_cs_ne_zero_upper h1
  have ht1 : 3 / 5 < p.2.1 := tw_cs_ne_zero_lower h2
  have ht2 : p.2.1 < 1 := tw_cs_ne_zero_upper h2
  have hw : ‖p.2.2 - baseState p.2.1‖ < 2 / 5 := by
    by_contra hcon
    rw [not_lt] at hcon
    exact h3 (cz_eq_zero_of_norm hcon)
  have hc0 : |p.2.2 0 - baseState p.2.1 0| ≤ 2 / 5 := by
    have h := norm_le_pi_norm (p.2.2 - baseState p.2.1) 0
    rw [Pi.sub_apply, Real.norm_eq_abs] at h
    exact le_trans h hw.le
  have hc1 : |p.2.2 1 - baseState p.2.1 1| ≤ 2 / 5 := by
    have h := norm_le_pi_norm (p.2.2 - baseState p.2.1) 1
    rw [Pi.sub_apply, Real.norm_eq_abs] at h
    exact le_trans h hw.le
  have hprof : (7 / 10 : ℝ) ≤ Commons.Geometry.Ulam.profileX p.2.1 :=
    seven_tenths_le_profileX (by linarith) (by linarith)
  have hb0 : baseState p.2.1 0 = Commons.Geometry.Ulam.profileX p.2.1 := by
    simp [Work.OddVolterra.baseState]
  have hb1 : baseState p.2.1 1 = Commons.Geometry.Ulam.profileX p.2.1 := by
    simp [Work.OddVolterra.baseState]
  rw [hb0] at hc0
  rw [hb1] at hc1
  exact hp ⟨hs1, hs2, ht1, ht2, by have := (abs_le.mp hc0).1; linarith,
    by have := (abs_le.mp hc1).1; linarith⟩

/-- `twRegion` is mapped into the region of smoothness of the manifest `Θ`-data by
`p ↦ (p.1, max p.1 p.2.1, p.2.2)`. -/
lemma tw_mapsTo_good {p : ℝ × ℝ × St} (hp : p ∈ twRegion) :
    (p.1, max p.1 p.2.1, p.2.2) ∈ Work.Anchor.Good := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp
  refine ⟨by linarith, by linarith, ?_, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (by linarith : (9 / 20 : ℝ) < p.1) (le_max_left _ _)
  · exact lt_of_lt_of_le (max_lt h2 h4) (by linarith : (1 : ℝ) ≤ 21 / 20)
  · rw [abs_of_pos (by linarith : (0 : ℝ) < p.2.2 0)]; linarith
  · rw [abs_of_pos (by linarith : (0 : ℝ) < p.2.2 1)]; linarith

/-! ## 3. Compact boxes inside the smoothness region -/

/-- The `z`-part of a compact box. -/
def twBoxZ (D : ℝ) : Set St :=
  {z : St | 1 / 4 ≤ z 0 ∧ 1 / 4 ≤ z 1 ∧ ∀ i : Fin 4, |z i| ≤ D}

/-- A compact box of parameters and states inside the smoothness region `Good`. -/
def twBox (D : ℝ) : Set (ℝ × ℝ × St) :=
  {r | r.1 ∈ Set.Icc (3 / 5 : ℝ) 1 ∧ r.2.1 ∈ Set.Icc (3 / 5 : ℝ) 1 ∧ r.2.2 ∈ twBoxZ D}

lemma tw_isCompact_twBoxZ (D : ℝ) : IsCompact (twBoxZ D) := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  refine ⟨?_, ?_⟩
  · have h1 : IsClosed {z : St | (1 / 4 : ℝ) ≤ z 0} :=
      isClosed_le continuous_const (continuous_apply 0)
    have h2 : IsClosed {z : St | (1 / 4 : ℝ) ≤ z 1} :=
      isClosed_le continuous_const (continuous_apply 1)
    have h3 : IsClosed {z : St | ∀ i : Fin 4, |z i| ≤ D} := by
      have hZ : {z : St | ∀ i : Fin 4, |z i| ≤ D} =
          ⋂ i : Fin 4, {z : St | |z i| ≤ D} := by ext z; simp
      rw [hZ]
      exact isClosed_iInter fun i =>
        isClosed_le ((continuous_apply i).abs) continuous_const
    have hZ : twBoxZ D = {z : St | (1 / 4 : ℝ) ≤ z 0} ∩ {z : St | (1 / 4 : ℝ) ≤ z 1} ∩
        {z : St | ∀ i : Fin 4, |z i| ≤ D} := by ext z; simp [twBoxZ, and_assoc]
    rw [hZ]
    exact (h1.inter h2).inter h3
  · refine (Metric.isBounded_closedBall (x := (0 : St)) (r := max D 1)).subset ?_
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right,
      pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ max D 1)]
    intro i
    rw [Real.norm_eq_abs]
    exact le_trans (hz.2.2 i) (le_max_left D 1)

lemma tw_isCompact_twBox (D : ℝ) : IsCompact (twBox D) := by
  have h : twBox D = Set.Icc (3 / 5 : ℝ) 1 ×ˢ (Set.Icc (3 / 5 : ℝ) 1 ×ˢ twBoxZ D) := by
    ext r; simp [twBox, Set.mem_prod]
  rw [h]
  exact isCompact_Icc.prod (isCompact_Icc.prod (tw_isCompact_twBoxZ D))

lemma tw_twBox_subset_Good (D : ℝ) : twBox D ⊆ Work.Anchor.Good := by
  intro r hr
  obtain ⟨h1, h2, h3⟩ := hr
  obtain ⟨hz0, hz1, hz2⟩ := h3
  refine ⟨by linarith [h1.1], by linarith [h1.2], by linarith [h2.1], by linarith [h2.2], ?_, ?_⟩
  · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ r.2.2 0)]; linarith
  · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ r.2.2 1)]; linarith

/-- The manifest `Θ`-data is bounded on every compact box. -/
lemma tw_twBox_bound (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsmall1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) (D : ℝ) :
    ∃ C : ℝ, ∀ r ∈ twBox D, ‖KernelExt.ThetaM n h r.1 r.2.1 r.2.2‖ ≤ C :=
  (tw_isCompact_twBox D).exists_bound_of_continuousOn
    (((Work.Anchor.ThetaM_contDiffOn_Good n hh hsmall1).continuousOn).mono
      (tw_twBox_subset_Good D))

/-! ## 4. The state data of the manifest kernel -/

lemma tw_abs_coord_sub_le {σ : ℝ} {z : St}
    (hz : z ∈ Metric.closedBall (baseState σ) (9 / 20)) (i : Fin 4) :
    |z i - baseState σ i| ≤ 9 / 20 := by
  have h := norm_le_pi_norm (z - baseState σ) i
  rw [Pi.sub_apply, Real.norm_eq_abs] at h
  exact le_trans h (Metric.mem_closedBall.mp hz)

lemma tw_abs_baseState_le_one (σ : ℝ) (i : Fin 4) : |baseState σ i| ≤ 1 := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by fin_cases i <;> simp
  rcases hi with rfl | rfl | rfl | rfl
  · simpa [Work.OddVolterra.baseState] using
      Commons.Geometry.Ulam.abs_profileX_le_one σ
  · simpa [Work.OddVolterra.baseState] using
      Commons.Geometry.Ulam.abs_profileX_le_one σ
  · have h : baseState σ 2 = deriv Commons.Geometry.Ulam.profileX σ := by
      simp [Work.OddVolterra.baseState]
    rw [h]
    linarith [Commons.Geometry.Ulam.abs_deriv_profileX_le σ]
  · have h : baseState σ 3 = deriv Commons.Geometry.Ulam.profileX σ := by
      simp [Work.OddVolterra.baseState]
    rw [h]
    linarith [Commons.Geometry.Ulam.abs_deriv_profileX_le σ]

lemma tw_mem_lower {s : ℝ} (hs : s ∈ Set.Icc wLeft wRight) : (3 / 5 : ℝ) ≤ s := by
  have h := hs.1; rw [wLeft] at h; linarith

lemma tw_mem_upper {s : ℝ} (hs : s ∈ Set.Icc wLeft wRight) : s ≤ 1 := by
  have h := hs.2; rw [wRight] at h; linarith

/-- On the ball of radius `9/20` around `baseState σ` (`σ` in the window) the first two state
coordinates are at least `1/4` and all coordinates are at most `2` in absolute value. -/
lemma tw_ball_data {σ : ℝ} (hσ : σ ∈ Set.Icc wLeft wRight) {z : St}
    (hz : z ∈ Metric.closedBall (baseState σ) (9 / 20)) :
    1 / 4 ≤ z 0 ∧ 1 / 4 ≤ z 1 ∧ ∀ i : Fin 4, |z i| ≤ 2 := by
  have hq : ∀ i : Fin 4, |z i| ≤ 2 := by
    intro i
    have h1 := tw_abs_coord_sub_le hz i
    have h2 := tw_abs_baseState_le_one σ i
    calc |z i| = |(z i - baseState σ i) + baseState σ i| := by ring_nf
      _ ≤ |z i - baseState σ i| + |baseState σ i| := abs_add_le _ _
      _ ≤ 9 / 20 + 1 := add_le_add h1 h2
      _ ≤ 2 := by norm_num
  have hprof : (7 / 10 : ℝ) ≤ Commons.Geometry.Ulam.profileX σ :=
    seven_tenths_le_profileX (le_of_lt (by rw [wLeft] at hσ; linarith [hσ.1]))
      (tw_mem_upper hσ)
  have h0 : |z 0 - baseState σ 0| ≤ 9 / 20 := tw_abs_coord_sub_le hz 0
  have h1 : |z 1 - baseState σ 1| ≤ 9 / 20 := tw_abs_coord_sub_le hz 1
  have hb0 : baseState σ 0 = Commons.Geometry.Ulam.profileX σ := by
    simp [Work.OddVolterra.baseState]
  have hb1 : baseState σ 1 = Commons.Geometry.Ulam.profileX σ := by
    simp [Work.OddVolterra.baseState]
  rw [hb0] at h0
  rw [hb1] at h1
  exact ⟨by linarith [(abs_le.mp h0).1], by linarith [(abs_le.mp h1).1], hq⟩

lemma tw_quarter_le_combo {z z' : St} {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hz : 1 / 4 ≤ z 0) (hz' : 1 / 4 ≤ z' 0) : 1 / 4 ≤ (z + t • (z' - z)) 0 := by
  have h : (z + t • (z' - z)) 0 = (1 - t) * z 0 + t * z' 0 := by
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  rw [h]
  nlinarith [ht.1, ht.2, hz, hz']

lemma tw_quarter_le_combo' {z z' : St} {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hz : 1 / 4 ≤ z 1) (hz' : 1 / 4 ≤ z' 1) : 1 / 4 ≤ (z + t • (z' - z)) 1 := by
  have h : (z + t • (z' - z)) 1 = (1 - t) * z 1 + t * z' 1 := by
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  rw [h]
  nlinarith [ht.1, ht.2, hz, hz']

lemma tw_abs_combo_le {z z' : St} {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hz : ∀ i : Fin 4, |z i| ≤ 2) (hz' : ∀ i : Fin 4, |z' i| ≤ 2) (i : Fin 4) :
    |(z + t • (z' - z)) i| ≤ 2 := by
  have h : (z + t • (z' - z)) i = (1 - t) * z i + t * z' i := by
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  rw [h]
  calc |(1 - t) * z i + t * z' i| ≤ |(1 - t) * z i| + |t * z' i| := abs_add_le _ _
    _ = |1 - t| * |z i| + |t| * |z' i| := by rw [abs_mul, abs_mul]
    _ = (1 - t) * |z i| + t * |z' i| := by
          rw [abs_of_nonneg (by linarith [ht.2]), abs_of_nonneg ht.1]
    _ ≤ (1 - t) * 2 + t * 2 :=
          add_le_add (mul_le_mul_of_nonneg_left (hz i) (by linarith [ht.2]))
            (mul_le_mul_of_nonneg_left (hz' i) ht.1)
    _ = 2 := by ring

/-- **Lipschitz constant and bound of the manifest kernel `ΘM` in the state**, uniformly over the
transition window. -/
lemma tw_ThetaM_state_data (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsmall1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
      (∀ s ∈ Set.Icc wLeft wRight, ∀ s' ∈ Set.Icc wLeft wRight, ∀ σ ∈ Set.Icc wLeft wRight,
        ∀ z ∈ Metric.closedBall (baseState σ) (9 / 20),
        ∀ z' ∈ Metric.closedBall (baseState σ) (9 / 20),
          ‖KernelExt.ThetaM n h s s' z - KernelExt.ThetaM n h s s' z'‖ ≤ M * ‖z - z'‖) ∧
      (∀ s ∈ Set.Icc wLeft wRight, ∀ s' ∈ Set.Icc wLeft wRight, ∀ σ ∈ Set.Icc wLeft wRight,
        ∀ z ∈ Metric.closedBall (baseState σ) (9 / 20),
          ‖KernelExt.ThetaM n h s s' z‖ ≤ B) := by
  have hΘ : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ × St => KernelExt.ThetaM n h p.1 p.2.1 p.2.2) Work.Anchor.Good :=
    Work.Anchor.ThetaM_contDiffOn_Good n hh hsmall1
  obtain ⟨M0, hM0⟩ := (tw_isCompact_twBox 2).exists_bound_of_continuousOn
    ((hΘ.continuousOn_fderiv_of_isOpen Work.Anchor.isOpen_Good
      (WithTop.coe_le_coe.mpr le_top)).mono (tw_twBox_subset_Good 2))
  obtain ⟨B0, hB0⟩ := tw_twBox_bound n hh hsmall1 2
  refine ⟨max M0 0, max B0 0, le_max_right _ _, le_max_right _ _, ?_, ?_⟩
  · intro s hs s' hs' σ hσ z hz z' hz'
    have hdiff : ∀ r ∈ twBox 2,
        DifferentiableAt ℝ (fun p : ℝ × ℝ × St => KernelExt.ThetaM n h p.1 p.2.1 p.2.2) r :=
      fun r hr => (hΘ.contDiffAt
        (Work.Anchor.isOpen_Good.mem_nhds (tw_twBox_subset_Good 2 hr))).differentiableAt (by simp)
    have hbdf : ∀ r ∈ twBox 2,
        ‖fderiv ℝ (fun p : ℝ × ℝ × St => KernelExt.ThetaM n h p.1 p.2.1 p.2.2) r‖ ≤ max M0 0 :=
      fun r hr => le_trans (hM0 r hr) (le_max_left _ _)
    have hmem0 : ((s, s', z) : ℝ × ℝ × St) ∈ twBox 2 := by
      obtain ⟨hz0, hz1, hz2⟩ := tw_ball_data hσ hz
      exact ⟨⟨tw_mem_lower hs, tw_mem_upper hs⟩, ⟨tw_mem_lower hs', tw_mem_upper hs'⟩,
        hz0, hz1, hz2⟩
    have hmem1 : ((s, s', z') : ℝ × ℝ × St) ∈ twBox 2 := by
      obtain ⟨hz0, hz1, hz2⟩ := tw_ball_data hσ hz'
      exact ⟨⟨tw_mem_lower hs, tw_mem_upper hs⟩, ⟨tw_mem_lower hs', tw_mem_upper hs'⟩,
        hz0, hz1, hz2⟩
    have hseg : ∀ t ∈ Set.Icc (0:ℝ) 1,
        ((s, s', z) : ℝ × ℝ × St) + t • ((s, s', z') - (s, s', z)) ∈ twBox 2 := by
      intro t ht
      obtain ⟨hz0, hz1, hz2⟩ := tw_ball_data hσ hz
      obtain ⟨hz'0, hz'1, hz'2⟩ := tw_ball_data hσ hz'
      have hcombo : ((s, s', z) : ℝ × ℝ × St) + t • ((s, s', z') - (s, s', z))
          = (s, s', z + t • (z' - z)) := by
        ext <;> simp
      rw [hcombo]
      exact ⟨⟨tw_mem_lower hs, tw_mem_upper hs⟩, ⟨tw_mem_lower hs', tw_mem_upper hs'⟩,
        tw_quarter_le_combo ht hz0 hz'0, tw_quarter_le_combo' ht hz1 hz'1,
        fun i => tw_abs_combo_le ht hz2 hz'2 i⟩
    have hmain := tw_norm_sub_le_of_norm_fderiv_le_of_segment (le_max_right M0 0) hdiff hbdf hseg
    rw [norm_sub_rev]
    refine le_trans hmain (le_of_eq ?_)
    have hnorm : ((s, s', z') : ℝ × ℝ × St) - (s, s', z) = (0, (0, z' - z)) := by
      ext <;> simp
    rw [hnorm, Prod.norm_def]
    simp [Prod.norm_def, norm_sub_rev]
  · intro s hs s' hs' σ hσ z hz
    obtain ⟨hz0, hz1, hz2⟩ := tw_ball_data hσ hz
    exact le_trans (hB0 (s, s', z) ⟨⟨tw_mem_lower hs, tw_mem_upper hs⟩,
      ⟨tw_mem_lower hs', tw_mem_upper hs'⟩, hz0, hz1, hz2⟩) (le_max_left _ _)

/-! ## 5. The manifest form of the clamped datum -/

/-- On the triangle and on the diagonal the clamped datum is the manifest datum at the slope
`max s σ`. -/
lemma tw_thetac_eq (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsmall1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {s σ : ℝ} (hs : 3 / 5 ≤ s) (hσ : 3 / 5 ≤ σ) {z : St}
    (hz0 : 1 / 5 ≤ z 0) (hz1 : 1 / 5 ≤ z 1) :
    thetac n h s σ z = KernelExt.ThetaM n h s (max s σ) z := by
  by_cases hlt : s < σ
  · rw [thetac, if_pos hlt, max_eq_right hlt.le]
    refine (ThetaM_eq_Theta n hn hh hlt (δ := 1 / 10) (by norm_num) z
      (fun a ha => ?_) (fun a ha => ?_)).symm
    · refine krad_pos_of_region hsmall1 (by linarith [ha.1, ha.2, hσ]) ?_
      rw [abs_neg, abs_of_nonneg (by linarith)]
      linarith
    · refine krad_pos_of_region hsmall1 (by linarith [ha.1, ha.2, hσ]) ?_
      rw [abs_of_nonneg (by linarith)]
      linarith
  · rw [thetac, if_neg hlt, max_eq_left (not_lt.mp hlt)]

/-- The global manifest form of `TW`. -/
lemma tw_TW_eq_manifest (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsmall1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    (p : ℝ × ℝ × St) :
    TW n h p.1 p.2.1 p.2.2
      = chiT p.1 p.2.1 p.2.2 • KernelExt.ThetaM n h p.1 (max p.1 p.2.1) p.2.2 := by
  rw [TW]
  by_cases hp : p ∈ twRegion
  · obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩ := hp
    rw [tw_thetac_eq n hn hh hsmall1 (le_of_lt hp1) (le_of_lt hp3)
      (by linarith [hp5]) (by linarith [hp6])]
  · rw [tw_chiT_eq_zero hp, zero_smul, zero_smul]

lemma tw_continuous_chiT : Continuous (fun p : ℝ × ℝ × St => chiT p.1 p.2.1 p.2.2) := by
  have hcs1 : Continuous (fun p : ℝ × ℝ × St => (cs : ℝ → ℝ) p.1) :=
    (ContDiffBump.contDiff cs (n := ⊤)).continuous.comp continuous_fst
  have hcs2 : Continuous (fun p : ℝ × ℝ × St => (cs : ℝ → ℝ) p.2.1) :=
    (ContDiffBump.contDiff cs (n := ⊤)).continuous.comp (continuous_fst.comp continuous_snd)
  have hbase : Continuous (fun p : ℝ × ℝ × St => baseState p.2.1) :=
    Work.OddVolterra.Existence.contDiff_baseState_comp.continuous.comp continuous_snd
  have hcz : Continuous (fun p : ℝ × ℝ × St =>
      (cz : ℝ → ℝ) ‖p.2.2 - baseState p.2.1‖) :=
    (ContDiffBump.contDiff cz (n := ⊤)).continuous.comp
      (((continuous_snd.comp continuous_snd).sub hbase).norm)
  rw [show (fun p : ℝ × ℝ × St => chiT p.1 p.2.1 p.2.2)
      = fun p => (cs : ℝ → ℝ) p.1 * ((cs : ℝ → ℝ) p.2.1 *
          (cz : ℝ → ℝ) ‖p.2.2 - baseState p.2.1‖) from by
    funext p; rw [chiT]; ring]
  exact hcs1.mul (hcs2.mul hcz)

/-! ## 6. Lipschitz in the state on the window -/

lemma tw_lipschitz_window (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsmall1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ Set.Icc wLeft wRight, ∀ σ ∈ Set.Icc wLeft wRight,
      ∀ z z' : St, ‖TW n h s σ z - TW n h s σ z'‖ ≤ L * ‖z - z'‖ := by
  obtain ⟨M, B, hM0, hB0, hMlip, hBbd⟩ := tw_ThetaM_state_data n hh hsmall1
  obtain ⟨Lc, hLc⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (𝕂 := ℝ)
    (ContDiffBump.hasCompactSupport cz) (ContDiffBump.contDiff cz (n := ⊤)) (by simp)
  refine ⟨1 * M + (Lc : ℝ) * B, add_nonneg (mul_nonneg zero_le_one hM0)
    (mul_nonneg Lc.coe_nonneg hB0), ?_⟩
  intro s hs σ hσ
  have hmax_mem : max s σ ∈ Set.Icc wLeft wRight :=
    ⟨le_max_of_le_left hs.1, max_le hs.2 hσ.2⟩
  have hinner : ∀ z ∈ Metric.closedBall (baseState σ) (9 / 20),
      ∀ z' ∈ Metric.closedBall (baseState σ) (9 / 20),
      ‖TW n h s σ z - TW n h s σ z'‖ ≤ (1 * M + (Lc : ℝ) * B) * ‖z - z'‖ := by
    intro z hz z' hz'
    have h1 : TW n h s σ z
        = (cz : ℝ → ℝ) ‖z - baseState σ‖ • KernelExt.ThetaM n h s (max s σ) z := by
      rw [tw_TW_eq_manifest n hn hh hsmall1 (s, σ, z), chiT_eq_cz_of_mem hs hσ z]
    have h2 : TW n h s σ z'
        = (cz : ℝ → ℝ) ‖z' - baseState σ‖ • KernelExt.ThetaM n h s (max s σ) z' := by
      rw [tw_TW_eq_manifest n hn hh hsmall1 (s, σ, z'), chiT_eq_cz_of_mem hs hσ z']
    rw [h1, h2]
    exact tw_lipschitz_smul_of_lipschitz_of_bounded
      (f := fun z : St => (cz : ℝ → ℝ) ‖z - baseState σ‖)
      (g := fun z : St => KernelExt.ThetaM n h s (max s σ) z)
      (s := Metric.closedBall (baseState σ) (9 / 20))
      (Mf := 1) (Mg := B) (Kf := (Lc : ℝ)) (Kg := M)
      (fun z _ => abs_cz_le_one _)
      (fun z hzmem => hBbd s hs (max s σ) hmax_mem σ hσ z hzmem)
      (fun z _ z' _ => by
        have h := hLc.dist_le_mul (‖z - baseState σ‖) (‖z' - baseState σ‖)
        rw [Real.dist_eq] at h
        refine le_trans h (mul_le_mul_of_nonneg_left ?_ Lc.coe_nonneg)
        simpa [Real.dist_eq] using
          abs_norm_sub_norm_le (z - baseState σ) (z' - baseState σ))
      (fun z hzmem z' hz'mem =>
        hMlip s hs (max s σ) hmax_mem σ hσ z hzmem z' hz'mem)
      z hz z' hz'
  have hsupp : ∀ z : St, 2 / 5 ≤ ‖z - baseState σ‖ → TW n h s σ z = 0 := by
    intro z hz
    rw [TW, chiT_eq_zero_of_far hz, zero_smul]
  exact tw_lipschitz_of_support_subset_of_lipschitz_on_closedBall (c := baseState σ)
    (r := 2 / 5) (R := 9 / 20) (M := 1 * M + (Lc : ℝ) * B) (by norm_num)
    (add_nonneg (mul_nonneg zero_le_one hM0) (mul_nonneg Lc.coe_nonneg hB0)) hsupp hinner

/-! ## 7. The main theorem -/

theorem TW_regular (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    Continuous (fun p : ℝ × ℝ × Work.OddVolterra.St =>
        Work.OddVolterra.Window.TW n h p.1 p.2.1 p.2.2) ∧
    (∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ Set.Icc Work.OddVolterra.Window.wLeft Work.OddVolterra.Window.wRight,
      ∀ σ ∈ Set.Icc Work.OddVolterra.Window.wLeft Work.OddVolterra.Window.wRight,
      ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState σ) 1,
      ∀ z' ∈ Metric.closedBall (Work.OddVolterra.baseState σ) 1,
        ‖Work.OddVolterra.Window.TW n h s σ z - Work.OddVolterra.Window.TW n h s σ z'‖
          ≤ L * ‖z - z'‖) := by
  have hsmall1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => hsmall k (by omega) s
  obtain ⟨L, hL0, hLip⟩ := tw_lipschitz_window n hn hh hsmall1
  refine ⟨?_, ⟨L, hL0, fun s hs σ hσ z _ z' _ => hLip s hs σ hσ z z'⟩⟩
  have hΨ : ContinuousOn (fun p : ℝ × ℝ × St =>
      KernelExt.ThetaM n h p.1 (max p.1 p.2.1) p.2.2) twRegion := by
    have hΘ : ContinuousOn (fun q : ℝ × ℝ × St => KernelExt.ThetaM n h q.1 q.2.1 q.2.2)
        Work.Anchor.Good := (Work.Anchor.ThetaM_contDiffOn_Good n hh hsmall1).continuousOn
    have hmap : Continuous (fun p : ℝ × ℝ × St => (p.1, max p.1 p.2.1, p.2.2)) := by fun_prop
    have hmaps : Set.MapsTo (fun p : ℝ × ℝ × St => (p.1, max p.1 p.2.1, p.2.2))
        twRegion Work.Anchor.Good := fun p hp => tw_mapsTo_good hp
    simpa only [Function.comp_def] using hΘ.comp hmap.continuousOn hmaps
  have hbd : ∀ p : ℝ × ℝ × St, ∃ C : ℝ, ∃ V ∈ 𝓝 p, ∀ q ∈ V, q ∈ twRegion →
      ‖KernelExt.ThetaM n h q.1 (max q.1 q.2.1) q.2.2‖ ≤ C := by
    intro p
    obtain ⟨C, hC⟩ := tw_twBox_bound n hh hsmall1
      (max (max (max |p.2.2 0| |p.2.2 1|) |p.2.2 2|) |p.2.2 3| + 1)
    refine ⟨max C 0, Metric.ball p 1, Metric.ball_mem_nhds p one_pos, ?_⟩
    intro q hq hqreg
    obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6⟩ := hqreg
    have hqnorm : ‖q - p‖ < 1 := by
      rw [Metric.mem_ball, dist_eq_norm] at hq; exact hq
    have hcoord : ∀ i : Fin 4, |q.2.2 i| ≤
        max (max (max |p.2.2 0| |p.2.2 1|) |p.2.2 2|) |p.2.2 3| + 1 := by
      intro i
      have h1 : |q.2.2 i - p.2.2 i| ≤ 1 := by
        have h : ‖q.2.2 i - p.2.2 i‖ ≤ ‖q - p‖ := by
          calc ‖q.2.2 i - p.2.2 i‖ ≤ ‖q.2.2 - p.2.2‖ := norm_le_pi_norm (q.2.2 - p.2.2) i
            _ ≤ ‖(q - p).2.2‖ := by
                rw [show (q - p).2.2 = q.2.2 - p.2.2 from rfl]
            _ ≤ ‖(q - p).2‖ := norm_snd_le _
            _ ≤ ‖q - p‖ := norm_snd_le _
        rw [← Real.norm_eq_abs]
        exact le_trans h hqnorm.le
      have h2 : |p.2.2 i| ≤ max (max (max |p.2.2 0| |p.2.2 1|) |p.2.2 2|) |p.2.2 3| := by
        fin_cases i
        · exact le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_refl _)))
        · exact le_max_of_le_left (le_max_of_le_left (le_max_of_le_right (le_refl _)))
        · exact le_max_of_le_left (le_max_of_le_right (le_refl _))
        · exact le_max_of_le_right (le_refl _)
      calc |q.2.2 i| = |(q.2.2 i - p.2.2 i) + p.2.2 i| := by ring_nf
        _ ≤ |q.2.2 i - p.2.2 i| + |p.2.2 i| := abs_add_le _ _
        _ ≤ 1 + max (max (max |p.2.2 0| |p.2.2 1|) |p.2.2 2|) |p.2.2 3| := add_le_add h1 h2
        _ = max (max (max |p.2.2 0| |p.2.2 1|) |p.2.2 2|) |p.2.2 3| + 1 := by ring
    refine le_trans (hC (q.1, max q.1 q.2.1, q.2.2) ?_) (le_max_left _ _)
    exact ⟨⟨le_of_lt hq1, le_of_lt hq2⟩,
      ⟨le_max_of_le_left (le_of_lt hq1), max_le (le_of_lt hq2) (le_of_lt hq4)⟩,
      le_of_lt hq5, le_of_lt hq6, hcoord⟩
  rw [show (fun p : ℝ × ℝ × St => TW n h p.1 p.2.1 p.2.2)
      = fun p => chiT p.1 p.2.1 p.2.2 • KernelExt.ThetaM n h p.1 (max p.1 p.2.1) p.2.2
      from funext fun p => tw_TW_eq_manifest n hn hh hsmall1 p]
  exact tw_continuous_smul_of_continuous_of_continuousOn tw_isOpen_twRegion tw_continuous_chiT
    (fun p hp => tw_chiT_eq_zero hp) hΨ hbd

end

end Work.OddVolterra.Window
