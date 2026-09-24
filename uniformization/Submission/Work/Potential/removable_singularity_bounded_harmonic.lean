import Mathlib
import Submission.Work.Potential.Defs
import Submission.Commons.Analysis.Complex.Dirichlet.dirichlet_ball
import Submission.Commons.Analysis.Complex.Harmonic.annulus_le_boundary
import Submission.Commons.Analysis.Complex.Harmonic.harmonic_le_of_boundary_le
import Submission.Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic

/-!
# Removable singularity for a bounded harmonic function on a Riemann surface

A harmonic function on a complex one-manifold `X` which is bounded outside a single point `z₀`
extends to a harmonic function on all of `X`.  The proof reduces, in the preferred chart at `z₀`,
to the classical planar statement: a bounded harmonic function on a punctured Euclidean ball
extends.  The extension is the Dirichlet solution in the ball (the Poisson integral of the
boundary values), and it is shown to agree with the given function by a logarithmic-barrier
(harmonic measure) estimate on the annuli `{δ < ‖z‖ < ρ}` together with `δ → 0`.
-/

open scoped Manifold ContDiff Topology
open Filter Set

noncomputable section

namespace Work.Potential

open Classical

/-! ## The planar heart -/

/-- **Removable singularity for bounded harmonic functions on a punctured Euclidean ball.**
A function harmonic on the punctured ball `{z : ℂ | 0 < ‖z‖ < R}` and bounded there extends to a
harmonic function on `{z | ‖z‖ < R / 2}`. -/
theorem removable_singularity_ball_local {u : ℂ → ℝ} {R M : ℝ} (hR : 0 < R)
    (hu : ∀ z : ℂ, ‖z‖ < R → z ≠ 0 → InnerProductSpace.HarmonicAt u z)
    (hb : ∀ z : ℂ, ‖z‖ < R → z ≠ 0 → |u z| ≤ M) :
    ∃ U : ℂ → ℝ, (∀ z : ℂ, ‖z‖ < R / 2 → InnerProductSpace.HarmonicAt U z) ∧
      (∀ z : ℂ, ‖z‖ < R / 2 → z ≠ 0 → U z = u z) := by
  set ρ : ℝ := R / 2 with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; linarith
  have hρR : ρ < R := by rw [hρdef]; linarith
  -- `M` is nonnegative, the punctured ball being nonempty
  have hMnn : 0 ≤ M := by
    have hne : ((ρ : ℝ) : ℂ) ≠ 0 := by simpa [Complex.ofReal_eq_zero] using hρ.ne'
    have hlt : ‖((ρ : ℝ) : ℂ)‖ < R := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]; exact hρR
    exact (abs_nonneg _).trans (hb _ hlt hne)
  -- the boundary data is continuous on the sphere
  have hFcont : ContinuousOn u (Metric.sphere (0 : ℂ) ρ) := by
    intro z hz
    have hznorm : ‖z‖ = ρ := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hzne : z ≠ 0 := by intro h; rw [h, norm_zero] at hznorm; linarith
    exact ((hu z (by rw [hznorm]; exact hρR) hzne).1.continuousAt).continuousWithinAt
  -- the Dirichlet solution in the disc, and its `U`
  obtain ⟨v, hvharm, hvcont⟩ :=
    Commons.Analysis.Complex.Dirichlet.dirichlet_ball (c := 0) (R := ρ) (F := u) hρ hFcont
  have hvharm' : ∀ z : ℂ, ‖z‖ < ρ → InnerProductSpace.HarmonicAt v z :=
    fun z hz => hvharm z (by simpa using hz)
  have hvcont' : ContinuousOn (fun z : ℂ => if ‖z‖ < ρ then v z else u z)
      (Metric.closedBall (0 : ℂ) ρ) := by
    simpa only [sub_zero] using hvcont
  let U : ℂ → ℝ := fun z => if ‖z‖ < ρ then v z else u z
  have hUcont : ContinuousOn U (Metric.closedBall (0 : ℂ) ρ) := hvcont'
  have hUharm : ∀ z : ℂ, ‖z‖ < ρ → InnerProductSpace.HarmonicAt U z := by
    intro z hz
    have hball : Metric.ball (0 : ℂ) ρ ∈ 𝓝 z :=
      Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_eq_norm] using hz)
    have hev : U =ᶠ[𝓝 z] v := by
      filter_upwards [hball] with y hy
      have hylt : ‖y‖ < ρ := by simpa [Metric.mem_ball, dist_eq_norm] using hy
      exact if_pos hylt
    exact (InnerProductSpace.harmonicAt_congr_nhds hev).mpr (hvharm' z hz)
  -- bounds: the maximum principle on the disc, applied to `v` and to `-v`
  have hubd : ∀ z ∈ Metric.sphere (0 : ℂ) ρ, u z ≤ M := by
    intro z hz
    have hznorm : ‖z‖ = ρ := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hzne : z ≠ 0 := by intro h; rw [h, norm_zero] at hznorm; linarith
    exact (le_abs_self _).trans (hb z (by rw [hznorm]; exact hρR) hzne)
  have hv_le : ∀ z : ℂ, ‖z‖ < ρ → v z ≤ M := by
    have h := Commons.Analysis.Complex.Harmonic.harmonic_le_of_boundary_le (c := 0) (R := ρ)
      (M := M) hρ (F := u) hubd (fun z hz => hvharm' z (by simpa using hz)) hvcont
    simpa only [sub_zero] using h
  have hnubd : ∀ z ∈ Metric.sphere (0 : ℂ) ρ, -u z ≤ M := by
    intro z hz
    have hznorm : ‖z‖ = ρ := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hzne : z ≠ 0 := by intro h; rw [h, norm_zero] at hznorm; linarith
    have h1 : -M ≤ u z := (abs_le.mp (hb z (by rw [hznorm]; exact hρR) hzne)).1
    linarith
  have hnegcont : ContinuousOn (fun z : ℂ => if ‖z - 0‖ < ρ then (-v) z else -u z)
      (Metric.closedBall (0 : ℂ) ρ) := by
    refine hvcont.neg.congr ?_
    intro z _
    by_cases hz : ‖z‖ < ρ <;> simp [hz]
  have hnv_le : ∀ z : ℂ, ‖z‖ < ρ → -v z ≤ M := by
    have h := Commons.Analysis.Complex.Harmonic.harmonic_le_of_boundary_le (c := 0) (R := ρ)
      (M := M) hρ (F := fun z : ℂ => -u z) hnubd
      (fun z hz => (hvharm' z (by simpa using hz)).neg) hnegcont
    simpa only [sub_zero, Pi.neg_apply] using h
  have hUbound : ∀ z : ℂ, ‖z‖ < ρ → |U z| ≤ M := by
    intro z hz
    have hUv : U z = v z := if_pos hz
    rw [hUv]
    exact abs_le.mpr ⟨by linarith [hnv_le z hz], hv_le z hz⟩
  -- `V = u - U` is bounded on the punctured disc and vanishes on the outer circle
  let V : ℂ → ℝ := u - U
  have hVharm : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → InnerProductSpace.HarmonicAt V z :=
    fun z hzpos hz =>
      (hu z (lt_trans hz hρR) (norm_pos_iff.mp hzpos)).sub (hUharm z hz)
  have hVcont : ∀ δ : ℝ, 0 < δ → ContinuousOn V {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ ρ} := by
    intro δ hδ
    have hUc : ContinuousOn U {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ ρ} :=
      hUcont.mono (fun z hz => by
        simp only [Metric.mem_closedBall, dist_zero_right]
        exact hz.2)
    have huc : ContinuousOn u {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ ρ} := by
      intro z hz
      have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hδ hz.1
      exact ((hu z (lt_of_le_of_lt hz.2 hρR) (norm_pos_iff.mp hzpos)).1.continuousAt).continuousWithinAt
    exact huc.sub hUc
  have hVbound : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ ρ → |V z| ≤ 2 * M := by
    intro z hzpos hzle
    rcases lt_or_eq_of_le hzle with hlt | heq
    · have h1 : |u z| ≤ M := hb z (lt_trans hlt hρR) (norm_pos_iff.mp hzpos)
      have h2 : |U z| ≤ M := hUbound z hlt
      have h3 : |V z| ≤ |u z| + |U z| := by
        have hVz : V z = u z - U z := rfl
        rw [hVz, abs_sub_le_iff]
        constructor <;> linarith [le_abs_self (u z), neg_le_abs (u z), le_abs_self (U z),
          neg_abs_le (U z)]
      calc |V z| ≤ |u z| + |U z| := h3
        _ ≤ M + M := add_le_add h1 h2
        _ = 2 * M := by ring
    · have hnot : ¬ ‖z‖ < ρ := by rw [heq]; exact lt_irrefl ρ
      have hUu : U z = u z := if_neg hnot
      have hzero : V z = 0 := sub_eq_zero.mpr hUu.symm
      rw [hzero, abs_zero]
      linarith [hMnn]
  -- the logarithmic-barrier (harmonic measure) estimate on the annuli
  have barrier : ∀ (W : ℂ → ℝ) (δ B : ℝ), 0 < δ → δ < ρ → 0 ≤ B →
      (∀ w : ℂ, δ < ‖w‖ → ‖w‖ < ρ → InnerProductSpace.HarmonicAt W w) →
      ContinuousOn W {w : ℂ | δ ≤ ‖w‖ ∧ ‖w‖ ≤ ρ} →
      (∀ w : ℂ, ‖w‖ = δ → W w ≤ B) →
      (∀ w : ℂ, ‖w‖ = ρ → W w ≤ 0) →
      ∀ w : ℂ, δ ≤ ‖w‖ → ‖w‖ ≤ ρ →
        W w ≤ B * (Real.log (ρ / δ))⁻¹ * Real.log (ρ / ‖w‖) := by
    intro W δ B hδ hδρ _ hharm hcont hinner houter w hw1 hw2
    let ψ : ℂ → ℝ := fun z => Real.log (ρ / ‖z‖)
    have hψharm : ∀ z : ℂ, δ < ‖z‖ → ‖z‖ < ρ → InnerProductSpace.HarmonicAt ψ z := by
      intro z hz1 hz2
      have hzne : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hδ hz1.le)
      have hlogw : InnerProductSpace.HarmonicAt (fun y : ℂ => Real.log ‖y‖) z :=
        AnalyticAt.harmonicAt_log_norm (f := id) analyticAt_id (by simpa using hzne)
      have hsub : InnerProductSpace.HarmonicAt (fun y : ℂ => Real.log ρ - Real.log ‖y‖) z :=
        (InnerProductSpace.harmonicAt_const (Real.log ρ)).sub hlogw
      refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mpr hsub
      filter_upwards [isOpen_compl_singleton.mem_nhds hzne] with y hy
      have hyne : y ≠ 0 := by simpa using hy
      exact Real.log_div hρ.ne' (by simpa [norm_eq_zero] using hyne)
    have hψcont : ContinuousOn ψ {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ ρ} := by
      have hlog : ContinuousOn (fun z : ℂ => Real.log ‖z‖) {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ ρ} := by
        refine Real.continuousOn_log.comp continuous_norm.continuousOn (fun z hz => ?_)
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        simpa using (lt_of_lt_of_le hδ hz.1).ne'
      have hsub : ContinuousOn ((fun _ : ℂ => Real.log ρ) - fun z : ℂ => Real.log ‖z‖)
          {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ ρ} := continuousOn_const.sub hlog
      refine hsub.congr (fun z hz => ?_)
      exact Real.log_div hρ.ne' (lt_of_lt_of_le hδ hz.1).ne'
    let W' : ℂ → ℝ := W - (B * (Real.log (ρ / δ))⁻¹) • ψ
    have hW'harm : InnerProductSpace.HarmonicOnNhd W' {z : ℂ | δ < ‖z‖ ∧ ‖z‖ < ρ} :=
      fun z hz => (hharm z hz.1 hz.2).sub
        ((hψharm z hz.1 hz.2).const_smul (c := B * (Real.log (ρ / δ))⁻¹))
    have hW'cont : ContinuousOn W' {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ ρ} :=
      hcont.sub (hψcont.const_smul (B * (Real.log (ρ / δ))⁻¹))
    have hLpos : 0 < Real.log (ρ / δ) := Real.log_pos (by rw [one_lt_div hδ]; exact hδρ)
    have hW'bound : ∀ z : ℂ, (‖z‖ = δ ∨ ‖z‖ = ρ) → W' z ≤ 0 := by
      intro z hz
      rcases hz with hz | hz
      · have hψz : ψ z = Real.log (ρ / δ) := by
          show Real.log (ρ / ‖z‖) = Real.log (ρ / δ)
          rw [hz]
        have hWz : W' z = W z - B := by
          show W z - (B * (Real.log (ρ / δ))⁻¹) * ψ z = W z - B
          rw [hψz, mul_assoc, inv_mul_cancel₀ hLpos.ne', mul_one]
        rw [hWz]
        linarith [hinner z hz]
      · have hψz : ψ z = 0 := by
          show Real.log (ρ / ‖z‖) = 0
          rw [hz, div_self hρ.ne', Real.log_one]
        have hWz : W' z = W z := by
          show W z - (B * (Real.log (ρ / δ))⁻¹) * ψ z = W z
          rw [hψz, mul_zero, sub_zero]
        rw [hWz]
        exact houter z hz
    have hmax := Commons.Analysis.Complex.Harmonic.annulus_le_boundary (u := W') (r := δ)
      (R := ρ) (M := 0) hδ hδρ hW'harm hW'cont hW'bound
    have hw := hmax w hw1 hw2
    have hfin : W w - B * (Real.log (ρ / δ))⁻¹ * Real.log (ρ / ‖w‖) ≤ 0 := by
      have hWw : W' w = W w - B * (Real.log (ρ / δ))⁻¹ * Real.log (ρ / ‖w‖) := rfl
      rw [hWw] at hw
      exact hw
    linarith
  -- conclusion: `V` vanishes on the punctured disc
  refine ⟨U, hUharm, ?_⟩
  intro z hz hzne
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hzne
  have hVle : ∀ δ : ℝ, 0 < δ → δ < ‖z‖ →
      V z ≤ 2 * M * (Real.log (ρ / δ))⁻¹ * Real.log (ρ / ‖z‖) := by
    intro δ hδ hδz
    have hδρ : δ < ρ := lt_trans hδz hz
    exact barrier V δ (2 * M) hδ hδρ (by linarith [hMnn])
      (fun w hw1 hw2 => hVharm w (lt_trans hδ hw1) hw2) (hVcont δ hδ)
      (fun w hw => (le_abs_self _).trans
        (hVbound w (by rw [hw]; exact hδ) (by rw [hw]; exact hδρ.le)))
      (fun w hw => by
        have hnot : ¬ ‖w‖ < ρ := by rw [hw]; exact lt_irrefl ρ
        have hUu : U w = u w := if_neg hnot
        have hzero : V w = 0 := sub_eq_zero.mpr hUu.symm
        rw [hzero])
      z hδz.le hz.le
  have hnegVle : ∀ δ : ℝ, 0 < δ → δ < ‖z‖ →
      -V z ≤ 2 * M * (Real.log (ρ / δ))⁻¹ * Real.log (ρ / ‖z‖) := by
    intro δ hδ hδz
    have hδρ : δ < ρ := lt_trans hδz hz
    exact barrier (fun w : ℂ => -V w) δ (2 * M) hδ hδρ (by linarith [hMnn])
      (fun w hw1 hw2 => (hVharm w (lt_trans hδ hw1) hw2).neg) ((hVcont δ hδ).neg)
      (fun w hw => (neg_le_abs _).trans
        (hVbound w (by rw [hw]; exact hδ) (by rw [hw]; exact hδρ.le)))
      (fun w hw => by
        have hnot : ¬ ‖w‖ < ρ := by rw [hw]; exact lt_irrefl ρ
        have hUu : U w = u w := if_neg hnot
        have hzero : V w = 0 := sub_eq_zero.mpr hUu.symm
        rw [hzero]; exact neg_zero.le)
      z hδz.le hz.le
  have htend : Filter.Tendsto (fun δ : ℝ => 2 * M * (Real.log (ρ / δ))⁻¹ * Real.log (ρ / ‖z‖))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hlog : Filter.Tendsto (fun δ : ℝ => Real.log (ρ / δ)) (𝓝[>] (0 : ℝ)) Filter.atTop := by
      have h1 : Filter.Tendsto (fun δ : ℝ => ρ * δ⁻¹) (𝓝[>] (0 : ℝ)) Filter.atTop :=
        Filter.Tendsto.const_mul_atTop hρ tendsto_inv_nhdsGT_zero
      refine Filter.Tendsto.congr' (Eventually.of_forall (fun δ => ?_))
        (Real.tendsto_log_atTop.comp h1)
      simp [div_eq_mul_inv]
    have h2 : Filter.Tendsto (fun δ : ℝ => (2 * M * Real.log (ρ / ‖z‖)) / Real.log (ρ / δ))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_const_nhds.div_atTop hlog
    refine Filter.Tendsto.congr' (Eventually.of_forall (fun δ => ?_)) h2
    rw [div_eq_mul_inv]
    ring
  have hVz : V z = 0 := by
    have h1 : V z ≤ 0 :=
      le_of_tendsto_of_tendsto tendsto_const_nhds htend (by
        filter_upwards [Ioo_mem_nhdsGT hzpos] with δ hδ
        exact hVle δ hδ.1 hδ.2)
    have h2 : -V z ≤ 0 :=
      le_of_tendsto_of_tendsto tendsto_const_nhds htend (by
        filter_upwards [Ioo_mem_nhdsGT hzpos] with δ hδ
        exact hnegVle δ hδ.1 hδ.2)
    linarith
  have hUv : U z = v z := if_pos hz
  have hVz' : u z - v z = 0 := by
    have h : u z - U z = 0 := hVz
    rw [hUv] at h
    exact h
  rw [hUv]
  linarith

/-- The same at an arbitrary centre, by translation. -/
theorem removable_singularity_ball_center {u : ℂ → ℝ} {a : ℂ} {R M : ℝ} (hR : 0 < R)
    (hu : ∀ z : ℂ, ‖z - a‖ < R → z ≠ a → InnerProductSpace.HarmonicAt u z)
    (hb : ∀ z : ℂ, ‖z - a‖ < R → z ≠ a → |u z| ≤ M) :
    ∃ U : ℂ → ℝ, (∀ z : ℂ, ‖z - a‖ < R / 2 → InnerProductSpace.HarmonicAt U z) ∧
      (∀ z : ℂ, ‖z - a‖ < R / 2 → z ≠ a → U z = u z) := by
  have hshift_an : ∀ w : ℂ, AnalyticAt ℂ (fun z : ℂ => a + z) w :=
    fun w => (analyticAt_const (v := a)).add analyticAt_id
  have hshift_an' : ∀ w : ℂ, AnalyticAt ℂ (fun z : ℂ => z - a) w :=
    fun w => analyticAt_id.sub (analyticAt_const (v := a))
  obtain ⟨Ũ, hŨharm, hŨeq⟩ :=
    removable_singularity_ball_local (u := fun w : ℂ => u (a + w)) (R := R) (M := M) hR
      (fun w hw hwne => by
        have hane : a + w ≠ a := by
          intro h
          exact hwne (by simpa using h)
        have hlt : ‖(a + w) - a‖ < R := by simpa using hw
        exact Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic (u := u)
          (f := fun z : ℂ => a + z) (x := w) (hshift_an w) (hu (a + w) hlt hane))
      (fun w hw hwne => by
        have hane : a + w ≠ a := by
          intro h
          exact hwne (by simpa using h)
        have hlt : ‖(a + w) - a‖ < R := by simpa using hw
        exact hb (a + w) hlt hane)
  refine ⟨fun z => Ũ (z - a), ?_, ?_⟩
  · intro z hz
    exact Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic (u := Ũ)
      (f := fun z : ℂ => z - a) (x := z) (hshift_an' z) (hŨharm (z - a) hz)
  · intro z hz hzne
    have hzne' : z - a ≠ 0 := sub_ne_zero.mpr hzne
    have h := hŨeq (z - a) hz hzne'
    simpa [sub_eq_add_neg, add_comm] using h

/-! ## Moving harmonicity across a single point -/

/-- Harmonicity at `y` is insensitive to changing a function at another point `z₀ ≠ y`:
if `U` agrees with `u` off `z₀`, then `u` harmonic at `y` implies `U` harmonic at `y`. -/
theorem harmonicOnXAt_of_eq_off {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {u U : X → ℝ} {z₀ y : X} (hy : y ≠ z₀) (h : ∀ x, x ≠ z₀ → U x = u x)
    (hu : Submission.HarmonicOnXAt u y) : Submission.HarmonicOnXAt U y := by
  rw [Submission.HarmonicOnXAt] at hu ⊢
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mpr hu
  by_cases hz : z₀ ∈ (chartAt ℂ y).source
  · have hne : (chartAt ℂ y) y ≠ (chartAt ℂ y) z₀ := by
      intro hh
      exact hy ((chartAt ℂ y).injOn (mem_chart_source ℂ y) hz hh)
    filter_upwards [(chartAt ℂ y).open_target.mem_nhds
      ((chartAt ℂ y).map_source (mem_chart_source ℂ y)),
      isOpen_compl_singleton.mem_nhds hne] with t ht htc
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at htc
    exact h _ (fun hc => htc (by rw [← (chartAt ℂ y).right_inv ht, hc]))
  · filter_upwards [(chartAt ℂ y).open_target.mem_nhds
      ((chartAt ℂ y).map_source (mem_chart_source ℂ y))] with t ht
    exact h _ (fun hc => hz (by rw [← hc]; exact (chartAt ℂ y).map_target ht))

/-! ## The main result -/

theorem removable_singularity_bounded_harmonic
    {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {z₀ : X} {u : X → ℝ}
    (hu : Submission.HarmonicOnX u (Set.univ \ {z₀}))
    (hb : ∃ M : ℝ, ∀ x, x ≠ z₀ → |u x| ≤ M) :
    ∃ U : X → ℝ, Submission.HarmonicOnX U Set.univ ∧ ∀ x, x ≠ z₀ → U x = u x := by
  obtain ⟨M, hM⟩ := hb
  -- a chart disc around `z₀` contained in the chart target
  obtain ⟨R, hR, hRsub⟩ : ∃ R : ℝ, 0 < R ∧
      Metric.closedBall ((chartAt ℂ z₀) z₀) R ⊆ (chartAt ℂ z₀).target := by
    have hmem : (chartAt ℂ z₀).target ∈ 𝓝 ((chartAt ℂ z₀) z₀) :=
      (chartAt ℂ z₀).open_target.mem_nhds
        ((chartAt ℂ z₀).map_source (mem_chart_source ℂ z₀))
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hmem
    exact ⟨ε / 2, by linarith,
      (Metric.closedBall_subset_ball (by linarith : ε / 2 < ε)).trans hball⟩
  have hz₀src : z₀ ∈ (chartAt ℂ z₀).source := mem_chart_source ℂ z₀
  have hRpos : (0 : ℝ) < R / 2 := by linarith
  -- chart values in the open ball correspond to points of the target
  have htarget_of : ∀ z : ℂ, ‖z - (chartAt ℂ z₀) z₀‖ < R → z ∈ (chartAt ℂ z₀).target := by
    intro z hz
    exact hRsub (Metric.ball_subset_closedBall (Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact hz)))
  -- a chart value different from the image of `z₀` corresponds to a point different from `z₀`
  have hsymm_ne : ∀ z : ℂ, z ∈ (chartAt ℂ z₀).target → z ≠ (chartAt ℂ z₀) z₀ →
      (chartAt ℂ z₀).symm z ≠ z₀ := by
    intro z hztgt hz hc
    exact hz (by rw [← (chartAt ℂ z₀).right_inv hztgt, hc])
  -- the planar removable-singularity result, applied to `u` read in the chart
  obtain ⟨U₀, hU₀harm, hU₀eq⟩ :=
    removable_singularity_ball_center (u := fun z => u ((chartAt ℂ z₀).symm z))
      (a := (chartAt ℂ z₀) z₀) (R := R) (M := M) hR
      (fun z hz hzne => by
        have hztgt : z ∈ (chartAt ℂ z₀).target := htarget_of z hz
        have hysrc : (chartAt ℂ z₀).symm z ∈ (chartAt ℂ z₀).source :=
          (chartAt ℂ z₀).map_target hztgt
        have hcy : (chartAt ℂ z₀) ((chartAt ℂ z₀).symm z) = z :=
          (chartAt ℂ z₀).right_inv hztgt
        have hyne : (chartAt ℂ z₀).symm z ≠ z₀ := hsymm_ne z hztgt hzne
        have hharm : Submission.HarmonicOnXAt u ((chartAt ℂ z₀).symm z) :=
          hu _ ⟨mem_univ _, hyne⟩
        have h := (Submission.HarmonicOnXAt_iff_chart (u := u) (x := (chartAt ℂ z₀).symm z)
          (y := z₀) hysrc).mp hharm
        rwa [hcy] at h)
      (fun z hz hzne => hM _ (hsymm_ne z (htarget_of z hz) hzne))
  refine ⟨fun w => if w = z₀ then U₀ ((chartAt ℂ z₀) z₀) else u w, ?_, ?_⟩
  · intro y _
    by_cases hy : y = z₀
    · -- harmonicity at the puncture: in the chart, reduce to the planar extension `U₀`
      rw [hy, Submission.HarmonicOnXAt]
      have heq : ((fun w => if w = z₀ then U₀ ((chartAt ℂ z₀) z₀) else u w) ∘
          (chartAt ℂ z₀).symm) =ᶠ[𝓝 ((chartAt ℂ z₀) z₀)] U₀ := by
        filter_upwards [(chartAt ℂ z₀).open_target.mem_nhds
            ((chartAt ℂ z₀).map_source hz₀src),
          Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hRpos)]
          with t ht htb
        have htb' : ‖t - (chartAt ℂ z₀) z₀‖ < R / 2 := by
          simpa [dist_eq_norm] using Metric.mem_ball.mp htb
        by_cases hc : (chartAt ℂ z₀).symm t = z₀
        · simp only [Function.comp_apply, if_pos hc]
          rw [← (chartAt ℂ z₀).right_inv ht, hc]
        · simp only [Function.comp_apply, if_neg hc]
          refine (hU₀eq t htb' ?_).symm
          intro hta
          exact hc (by rw [hta]; exact (chartAt ℂ z₀).left_inv hz₀src)
      refine (InnerProductSpace.harmonicAt_congr_nhds heq).mpr (hU₀harm _ ?_)
      rw [sub_self, norm_zero]; exact hRpos
    · exact harmonicOnXAt_of_eq_off hy (fun x hx => by simp [hx]) (hu y ⟨mem_univ y, hy⟩)
  · intro x hx
    simp [hx]

end Work.Potential
