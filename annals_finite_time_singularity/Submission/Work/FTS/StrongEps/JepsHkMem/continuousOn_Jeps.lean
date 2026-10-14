import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.L12Sin_mem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT


end Work.FTS.EllipticEst.TT
end
-- ===== merged: Submission.Work.FTS.StrongEps.Commute =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {f : Fn}

theorem isOpen_Quad : IsOpen Quad := isOpen_Ioi.prod isOpen_Ioo

/-- **The dominated-convergence computation of the `z`-derivative.**  For a profile which is
`C¹` on the open quadrant (with continuous `z`-derivative there), the `p`-integral form of `J_ε f`
at the angle `θ` is differentiable in `z`, with the integral of the derivative of the integrand as
derivative. -/
theorem hasDerivAt_integral_Jeps_z (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε) {f : Fn}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) Quad)
    (hdf : ContinuousOn (Function.uncurry (Work.Spaces.pz f)) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun z' => ∫ p : ℝ × ℝ, Jker ρ ε p * f (zShift z' p.1) (thShift θ p.2)
        ∂(volume.restrict (Metric.closedBall (0 : ℝ × ℝ) ε)))
      (∫ p : ℝ × ℝ, Jker ρ ε p *
        (Work.Spaces.pz f (zShift z p.1) (thShift θ p.2) * Real.exp (-p.1))
        ∂(volume.restrict (Metric.closedBall (0 : ℝ × ℝ) ε))) z := by
  have hzI : z ∈ Set.Ioo (z / 2) (2 * z) := self_mem_Ioo_div_two hz
  obtain ⟨C, hC⟩ := (isCompact_Kz z ε).prod (isCompact_Kth θ ε) |>.exists_bound_of_continuousOn
    (hdf.mono (Kz_prod_Kth_subset_Quad hz hε hθ))
  have hctrl := continuous_shift_pair z θ
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Metric.closedBall (0 : ℝ × ℝ) ε)) (𝕜 := ℝ)
    (F := fun x p => Jker ρ ε p * f (zShift x p.1) (thShift θ p.2))
    (F' := fun x p => Jker ρ ε p *
      (Work.Spaces.pz f (zShift x p.1) (thShift θ p.2) * Real.exp (-p.1)))
    (bound := fun p => Real.exp ε * C * ‖Jker ρ ε p‖)
    (x₀ := z) (s := Set.Ioo (z / 2) (2 * z)) (isOpen_Ioo.mem_nhds hzI)
    ?_ ?_ ?_ ?_ ?_ ?_).2
  · -- a.e.-strong measurability of the integrand, near `z`
    filter_upwards [isOpen_Ioo.mem_nhds hzI] with x hx
    have hctrl' : Continuous fun p : ℝ × ℝ => (zShift x p.1, thShift θ p.2) :=
      continuous_shift_pair x θ
    have hcont : ContinuousOn (fun p : ℝ × ℝ => f (zShift x p.1) (thShift θ p.2))
        (Metric.closedBall 0 ε) :=
      hf.continuousOn.comp hctrl'.continuousOn (fun p _ => mem_Quad_shift hz hθ (x := x) hx)
    exact (integrableOn_Jker_mul_ball hρ hε hcont).aestronglyMeasurable
  · -- integrability at `z`
    have hcont : ContinuousOn (fun p : ℝ × ℝ => f (zShift z p.1) (thShift θ p.2))
        (Metric.closedBall 0 ε) :=
      hf.continuousOn.comp hctrl.continuousOn (fun p _ => mem_Quad_shift hz hθ hzI)
    exact integrableOn_Jker_mul_ball hρ hε hcont
  · -- a.e.-strong measurability of the derivative
    have hcont : ContinuousOn
        (fun p : ℝ × ℝ => Work.Spaces.pz f (zShift z p.1) (thShift θ p.2) * Real.exp (-p.1))
        (Metric.closedBall 0 ε) :=
      (hdf.comp hctrl.continuousOn (fun p _ => mem_Quad_shift hz hθ hzI)).mul
        (Continuous.continuousOn (Real.continuous_exp.comp (continuous_neg.comp continuous_fst)))
    exact (integrableOn_Jker_mul_ball hρ hε hcont).aestronglyMeasurable
  · -- the domination
    rw [ae_restrict_iff' measurableSet_closedBall]
    refine Eventually.of_forall fun a ha x hx => ?_
    have h2 : ‖Work.Spaces.pz f (zShift x a.1) (thShift θ a.2)‖ ≤ C :=
      hC _ (mapsTo_ball_region hθ hx ha)
    have h3 : ‖Real.exp (-a.1)‖ ≤ Real.exp ε := by
      have hp' : max |a.1| |a.2| ≤ ε := by
        simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs]
          using ha
      obtain ⟨ha1, -⟩ := abs_le.mp (le_trans (le_max_left |a.1| |a.2|) hp')
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (by linarith)
    rw [norm_mul, norm_mul]
    have h4 : ‖Work.Spaces.pz f (zShift x a.1) (thShift θ a.2)‖ * ‖Real.exp (-a.1)‖
        ≤ C * Real.exp ε :=
      mul_le_mul h2 h3 (norm_nonneg _) (le_trans (norm_nonneg _) h2)
    calc ‖Jker ρ ε a‖
          * (‖Work.Spaces.pz f (zShift x a.1) (thShift θ a.2)‖ * ‖Real.exp (-a.1)‖)
        ≤ ‖Jker ρ ε a‖ * (C * Real.exp ε) := mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
      _ = Real.exp ε * C * ‖Jker ρ ε a‖ := by ring
  · -- integrability of the bound
    have hcont : ContinuousOn (fun p : ℝ × ℝ => ‖Jker ρ ε p‖) (Metric.closedBall 0 ε) :=
      (Jker_continuous hρ ε).norm.continuousOn
    exact (hcont.integrableOn_compact (isCompact_closedBall (0 : ℝ × ℝ) ε)).const_mul _
  · -- the pointwise derivative (chain rule)
    refine Eventually.of_forall fun a x hx => ?_
    have hquad : (zShift x a.1, thShift θ a.2) ∈ Quad := mem_Quad_shift hz hθ (x := x) hx
    have hd_on : DifferentiableOn ℝ (Function.uncurry f) Quad := hf.differentiableOn (by norm_num)
    have hd_at : DifferentiableAt ℝ (Function.uncurry f) (zShift x a.1, thShift θ a.2) :=
      hd_on.differentiableAt (isOpen_Quad.mem_nhds hquad)
    have hpr : DifferentiableAt ℝ (fun y : ℝ => (y, thShift θ a.2)) (zShift x a.1) := by fun_prop
    have hslice : HasDerivAt (fun y : ℝ => f y (thShift θ a.2))
        (Work.Spaces.pz f (zShift x a.1) (thShift θ a.2)) (zShift x a.1) := by
      have h := (hd_at.comp (zShift x a.1) hpr).hasDerivAt
      simpa only [Function.comp_def, Function.uncurry, Work.Spaces.pz] using h
    have hz1 : HasDerivAt (fun y : ℝ => zShift y a.1) (Real.exp (-a.1)) x := by
      simpa only [zShift, id_eq, one_mul] using (hasDerivAt_id x).mul_const (Real.exp (-a.1))
    exact (hslice.comp x hz1).const_mul (Jker ρ ε a)

/-- **`E1`, `z`-half: `J_ε` commutes with `∂_z` under the integral** (the `p`-integral form). -/
theorem Jeps_deriv_z (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε) {f : Fn}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) Quad)
    (hdf : ContinuousOn (Function.uncurry (Work.Spaces.pz f)) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    deriv (fun z' => Jeps ρ ε f z' θ) z
      = ∫ p : ℝ × ℝ, Jker ρ ε p *
          (Real.exp (-p.1) * Work.Spaces.pz f (zShift z p.1) (thShift θ p.2)) := by
  -- the restricted integral is the full integral: the kernel vanishes off the ball
  have hball : (fun z' => ∫ p : ℝ × ℝ, Jker ρ ε p * f (zShift z' p.1) (thShift θ p.2)
        ∂(volume.restrict (Metric.closedBall (0 : ℝ × ℝ) ε)))
      = fun z' => ∫ p : ℝ × ℝ, Jker ρ ε p * f (zShift z' p.1) (thShift θ p.2) := by
    funext z'
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
      (s := Metric.closedBall (0 : ℝ × ℝ) ε)
      (f := fun p : ℝ × ℝ => Jker ρ ε p * f (zShift z' p.1) (thShift θ p.2))
      (fun p hp => by rw [Jker_eq_zero_of_not_mem hρ hε hp, zero_mul])
  have hev : (fun z' => Jeps ρ ε f z' θ)
      =ᶠ[𝓝 z] fun z' => ∫ p : ℝ × ℝ, Jker ρ ε p * f (zShift z' p.1) (thShift θ p.2) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact Jeps_eq_integral ρ ε f hz' hθ
  rw [hev.deriv_eq, ← hball]
  rw [(hasDerivAt_integral_Jeps_z hρ hε hf hdf hz hθ).deriv]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
    (s := Metric.closedBall (0 : ℝ × ℝ) ε)
    (f := fun p : ℝ × ℝ => Jker ρ ε p *
      (Work.Spaces.pz f (zShift z p.1) (thShift θ p.2) * Real.exp (-p.1)))]
  · exact integral_congr_ae (Eventually.of_forall fun p => by ring)
  · intro p hp
    rw [Jker_eq_zero_of_not_mem hρ hε hp, zero_mul]

/-- **`E1`, `z`-half, `D_z`-form: `D_z (J_ε f) = J_ε (D_z f)` on the open quadrant.** -/
theorem Dz_Jeps (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε) {f : Fn}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) Quad)
    (hdf : ContinuousOn (Function.uncurry (Work.Spaces.pz f)) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.Dz (Jeps ρ ε f) z θ = Jeps ρ ε (Work.Spaces.Dz f) z θ := by
  have hdz : deriv (fun z' => Jeps ρ ε f z' θ) z
      = ∫ p : ℝ × ℝ, Jker ρ ε p *
          (Real.exp (-p.1) * Work.Spaces.pz f (zShift z p.1) (thShift θ p.2)) :=
    Jeps_deriv_z hρ hε hf hdf hz hθ
  have hJ : Jeps ρ ε (Work.Spaces.Dz f) z θ
      = ∫ p : ℝ × ℝ, Jker ρ ε p *
          (zShift z p.1 * Work.Spaces.pz f (zShift z p.1) (thShift θ p.2)) := by
    rw [show Work.Spaces.Dz f = fun z' θ' => z' * Work.Spaces.pz f z' θ' from rfl]
    exact Jeps_eq_integral ρ ε _ hz hθ
  simp only [Work.Spaces.Dz, Work.Spaces.pz, hdz, hJ]
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [zShift]
  ring

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.JepsHkMem.continuousOn_Jeps =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.JepsHkMem

open Work.FTS.StrongEps

/-! ## Elementary facts about the shifts -/

/-- The shift of a base point of the quadrant lies again in the quadrant: this is the reason the
whole statement is true. -/
theorem shift_mem_Quad' {x p : ℝ × ℝ} (hx : x ∈ Quad) :
    (zShift x.1 p.1, thShift x.2 p.2) ∈ Quad :=
  ⟨zShift_pos hx.1, thShift_mem hx.2⟩

/-- For a fixed base point `x`, the shift is continuous in the shift variable `p`. -/
theorem continuousOn_shift_right' {x : ℝ × ℝ} (s : Set (ℝ × ℝ)) :
    ContinuousOn (fun p : ℝ × ℝ => (zShift x.1 p.1, thShift x.2 p.2)) s := by
  refine ContinuousOn.prodMk ?_ ?_
  · simp only [zShift]
    exact (by fun_prop : Continuous fun p : ℝ × ℝ => x.1 * Real.exp (-p.1)).continuousOn
  · simp only [thShift]
    exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
      Real.arctan (Real.tan x.2 * Real.exp (-p.2))).continuousOn

/-- **A function vanishing off `s` is a.e. strongly measurable as soon as it is a.e. strongly
measurable on `s`.**  (`AEStronglyMeasurable f (μ.restrict s)` alone does not imply
`AEStronglyMeasurable f μ` — the values of `f` off `s` are uncontrolled — so the vanishing
hypothesis is used to glue the restriction by an indicator.) -/
theorem aestronglyMeasurable_of_eq_zero_off {f : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (h0 : ∀ x ∉ s, f x = 0)
    (hm : AEStronglyMeasurable f (volume.restrict s)) :
    AEStronglyMeasurable f volume := by
  refine ⟨s.indicator (hm.mk f), hm.stronglyMeasurable_mk.indicator hs, ?_⟩
  have h1 : ∀ᵐ x ∂volume, x ∈ s → f x = hm.mk f x := (ae_restrict_iff' hs).mp hm.ae_eq_mk
  filter_upwards [h1] with x hx
  by_cases hxs : x ∈ s
  · rw [Set.indicator_of_mem hxs]; exact hx hxs
  · rw [Set.indicator_of_notMem hxs, h0 x hxs]

/-! ## The `p`-integral form: continuity in the base point -/

/-- **Continuity of the `p`-integral form of `J_ε`** at a point of the open quadrant.

All the hypotheses on the profile are `ContinuousOn (uncurry g) Quad`; the compactness of the
support of `Jker ρ ε` (ball of radius `ε`) is what makes the domination argument work. -/
theorem cw_Jeps_integral {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {g : ℝ → ℝ → ℝ} (hg : ContinuousOn (Function.uncurry g) Quad)
    {z₀ θ₀ : ℝ} (hz₀ : 0 < z₀) (hθ₀ : θ₀ ∈ Set.Ioo 0 (π / 2)) :
    ContinuousWithinAt (fun x : ℝ × ℝ =>
      ∫ p : ℝ × ℝ, Jker ρ ε p * g (zShift x.1 p.1) (thShift x.2 p.2)) Quad (z₀, θ₀) := by
  have hq₀ : (z₀, θ₀) ∈ Quad := mem_Quad.mpr ⟨hz₀, hθ₀⟩
  -- the windows around the base point
  have hz2 : (0 : ℝ) < z₀ / 2 := by linarith
  have h2z : (0 : ℝ) < 2 * z₀ := by linarith
  have hθ2 : (0 : ℝ) < θ₀ / 2 := by linarith [hθ₀.1]
  have hθhi : (θ₀ + π / 2) / 2 < π / 2 := by linarith [hθ₀.2, Real.pi_pos]
  have hθlo : θ₀ / 2 < (θ₀ + π / 2) / 2 := by linarith [hθ₀.2, Real.pi_pos]
  let A : Set (ℝ × ℝ) := Metric.closedBall (0 : ℝ × ℝ) ε
  let W : Set (ℝ × ℝ) := Set.Icc (z₀ / 2) (2 * z₀) ×ˢ Set.Icc (θ₀ / 2) ((θ₀ + π / 2) / 2)
  let V : Set (ℝ × ℝ) := Set.Ioo (z₀ / 2) (2 * z₀) ×ˢ Set.Ioo (θ₀ / 2) ((θ₀ + π / 2) / 2)
  have hVmem : (z₀, θ₀) ∈ V :=
    ⟨⟨by linarith, by linarith⟩, ⟨by linarith [hθ₀.1], by linarith [hθ₀.2, Real.pi_pos]⟩⟩
  have hVnhds : V ∈ 𝓝[Quad] (z₀, θ₀) :=
    nhdsWithin_le_nhds (IsOpen.mem_nhds (isOpen_Ioo.prod isOpen_Ioo) hVmem)
  -- the shift map on the compact window is (jointly) continuous
  have hWcomp : IsCompact W := isCompact_Icc.prod isCompact_Icc
  have hAcomp : IsCompact A := isCompact_closedBall (0 : ℝ × ℝ) ε
  have hΦcont : ContinuousOn (fun y : (ℝ × ℝ) × (ℝ × ℝ) =>
      (zShift y.1.1 y.2.1, thShift y.1.2 y.2.2)) (W ×ˢ A) := by
    refine ContinuousOn.prodMk ?_ ?_
    · simp only [zShift]
      exact (by fun_prop : Continuous fun y : (ℝ × ℝ) × (ℝ × ℝ) =>
        y.1.1 * Real.exp (-y.2.1)).continuousOn
    · have htan : ContinuousOn (fun y : (ℝ × ℝ) × (ℝ × ℝ) => Real.tan y.1.2) (W ×ˢ A) :=
        Real.continuousOn_tan.comp (continuous_fst.snd.continuousOn) (fun y hy => by
          have hy2 : y.1.2 ∈ Set.Icc (θ₀ / 2) ((θ₀ + π / 2) / 2) := hy.1.2
          have hmem : y.1.2 ∈ Set.Ioo 0 (π / 2) :=
            ⟨lt_of_lt_of_le hθ2 hy2.1, lt_of_le_of_lt hy2.2 hθhi⟩
          exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [hmem.1, Real.pi_pos], hmem.2⟩).ne')
      have h1 : ContinuousOn (fun y : (ℝ × ℝ) × (ℝ × ℝ) =>
          Real.tan y.1.2 * Real.exp (-y.2.2)) (W ×ˢ A) :=
        htan.mul ((Real.continuous_exp.comp (continuous_neg.comp continuous_snd.snd)).continuousOn)
      have h2 := Real.continuous_arctan.comp_continuousOn h1
      simpa only [thShift, Function.comp_def] using h2
  have himg_compact : IsCompact ((fun y : (ℝ × ℝ) × (ℝ × ℝ) =>
      (zShift y.1.1 y.2.1, thShift y.1.2 y.2.2)) '' (W ×ˢ A)) :=
    (hWcomp.prod hAcomp).image_of_continuousOn hΦcont
  have himg_sub : ((fun y : (ℝ × ℝ) × (ℝ × ℝ) =>
      (zShift y.1.1 y.2.1, thShift y.1.2 y.2.2)) '' (W ×ˢ A)) ⊆ Quad := by
    rintro q ⟨y, hy, rfl⟩
    exact ⟨zShift_pos (lt_of_lt_of_le hz2 hy.1.1.1),
      thShift_mem ⟨lt_of_lt_of_le hθ2 hy.1.2.1, lt_of_le_of_lt hy.1.2.2 hθhi⟩⟩
  -- the bound on the profile over the compact image
  obtain ⟨C, hC⟩ := himg_compact.exists_bound_of_continuousOn (hg.mono himg_sub)
  have hbound_int : Integrable (fun p : ℝ × ℝ => max C 0 * ‖Jker ρ ε p‖) :=
    (Jker_integrable hρ hε).norm.const_mul (max C 0)
  -- a.e. strong measurability of the integrand
  have hmeas : ∀ᶠ x in 𝓝[Quad] (z₀, θ₀),
      AEStronglyMeasurable (fun p : ℝ × ℝ =>
        Jker ρ ε p * g (zShift x.1 p.1) (thShift x.2 p.2)) volume := by
    filter_upwards [hVnhds] with x hxV
    have hxQ : x ∈ Quad :=
      ⟨lt_trans hz2 hxV.1.1, ⟨lt_trans hθ2 hxV.2.1, lt_trans hxV.2.2 hθhi⟩⟩
    have hcontA : ContinuousOn (fun p : ℝ × ℝ =>
        Jker ρ ε p * g (zShift x.1 p.1) (thShift x.2 p.2)) A :=
      (Jker_continuous hρ ε).continuousOn.mul
        (hg.comp (continuousOn_shift_right' A) (fun p _ => shift_mem_Quad' hxQ))
    refine aestronglyMeasurable_of_eq_zero_off measurableSet_closedBall (fun p hp => ?_)
      (hcontA.aestronglyMeasurable measurableSet_closedBall)
    show Jker ρ ε p * g (zShift x.1 p.1) (thShift x.2 p.2) = 0
    rw [Jker_eq_zero_of_not_mem hρ hε hp, zero_mul]
  -- the domination, eventually in the base point
  have hbd : ∀ᶠ x in 𝓝[Quad] (z₀, θ₀), ∀ᵐ p ∂volume,
      ‖Jker ρ ε p * g (zShift x.1 p.1) (thShift x.2 p.2)‖ ≤ max C 0 * ‖Jker ρ ε p‖ := by
    filter_upwards [hVnhds] with x hxV
    refine Eventually.of_forall fun p => ?_
    by_cases hpA : p ∈ A
    · have hxW : x ∈ W := ⟨⟨le_of_lt hxV.1.1, le_of_lt hxV.1.2⟩,
        ⟨le_of_lt hxV.2.1, le_of_lt hxV.2.2⟩⟩
      have hb := hC (zShift x.1 p.1, thShift x.2 p.2) ⟨(x, p), ⟨hxW, hpA⟩, rfl⟩
      calc ‖Jker ρ ε p * g (zShift x.1 p.1) (thShift x.2 p.2)‖
          = ‖Jker ρ ε p‖ * ‖g (zShift x.1 p.1) (thShift x.2 p.2)‖ := norm_mul _ _
        _ ≤ ‖Jker ρ ε p‖ * C := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ ≤ ‖Jker ρ ε p‖ * max C 0 := mul_le_mul_of_nonneg_left (le_max_left C 0) (norm_nonneg _)
        _ = max C 0 * ‖Jker ρ ε p‖ := mul_comm _ _
    · rw [show Jker ρ ε p = 0 from Jker_eq_zero_of_not_mem hρ hε hpA, zero_mul, norm_zero]
      simp
  -- pointwise (a.e. in `p`) continuity in the base point
  have hpt : ∀ᵐ p ∂volume, ContinuousWithinAt (fun x : ℝ × ℝ =>
      Jker ρ ε p * g (zShift x.1 p.1) (thShift x.2 p.2)) Quad (z₀, θ₀) := by
    refine Eventually.of_forall fun p => ?_
    refine ContinuousWithinAt.const_mul ?_ (Jker ρ ε p)
    have hψon : ContinuousOn (fun x : ℝ × ℝ => (zShift x.1 p.1, thShift x.2 p.2)) Quad := by
      refine ContinuousOn.prodMk ?_ ?_
      · simp only [zShift]
        fun_prop
      · have htan : ContinuousOn (fun x : ℝ × ℝ => Real.tan x.2) Quad :=
          Real.continuousOn_tan.comp continuous_snd.continuousOn (fun x hx => by
            obtain ⟨-, hx2⟩ := hx
            exact (Real.cos_pos_of_mem_Ioo
              ⟨by linarith [hx2.1, Real.pi_pos], hx2.2⟩).ne')
        have h1 : ContinuousOn (fun x : ℝ × ℝ => Real.tan x.2 * Real.exp (-p.2)) Quad :=
          htan.mul_const _
        have h2 := Real.continuous_arctan.comp_continuousOn h1
        simpa only [thShift, Function.comp_def] using h2
    exact (hg.comp hψon (fun x hx => shift_mem_Quad' hx)).continuousWithinAt hq₀
  exact MeasureTheory.continuousWithinAt_of_dominated
    (F := fun (x : ℝ × ℝ) (p : ℝ × ℝ) =>
      Jker ρ ε p * g (zShift x.1 p.1) (thShift x.2 p.2))
    (x₀ := (z₀, θ₀)) (s := Quad) (bound := fun p : ℝ × ℝ => max C 0 * ‖Jker ρ ε p‖)
    hmeas hbd hbound_int hpt

/-! ## The statement -/

theorem continuousOn_Jeps {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {g : ℝ → ℝ → ℝ} (hg : ContinuousOn (fun q : ℝ × ℝ => g q.1 q.2) Work.FTS.StrongEps.Quad) :
    ContinuousOn (fun q : ℝ × ℝ => Work.FTS.StrongEps.Jeps ρ ε g q.1 q.2) Work.FTS.StrongEps.Quad := by
  rintro ⟨z₀, θ₀⟩ hq₀
  have hz₀ : 0 < z₀ := hq₀.1
  have hθ₀ : θ₀ ∈ Set.Ioo 0 (π / 2) := hq₀.2
  have hmain := cw_Jeps_integral hρ hε hg hz₀ hθ₀
  have hev : (fun x : ℝ × ℝ => Jeps ρ ε g x.1 x.2) =ᶠ[𝓝[Quad] (z₀, θ₀)]
      (fun x : ℝ × ℝ => ∫ p : ℝ × ℝ, Jker ρ ε p * g (zShift x.1 p.1) (thShift x.2 p.2)) := by
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    exact Jeps_eq_integral ρ ε g hx.1 hx.2
  exact hmain.congr_of_eventuallyEq hev (Jeps_eq_integral ρ ε g hz₀ hθ₀)

end Work.FTS.StrongEps.JepsHkMem
end
end
