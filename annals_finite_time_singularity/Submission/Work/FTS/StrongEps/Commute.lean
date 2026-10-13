/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/Commute.lean` — E1, the commutation of `J_ε` with `D_z`

This is the mathematical heart of **E1** of the design (`FTS_HARD_DESIGN.md`, section *(B)*):

* `hasDerivAt_integral_Jeps_z` / `Jeps_deriv_z` — differentiating `J_ε f` under the `p`-integral
  (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`; the kernel is supported in the ball of
  radius `ε`, and the shifts keep a compact sub-region of the quadrant compact, which is what
  supplies the domination);
* **`Dz_Jeps`** — `D_z (J_ε f) = J_ε (D_z f)` at every point of the open quadrant.  The identity is
  *exact*: the shifts `z ↦ z e^{-p₁}`, `θ ↦ arctan (tan θ e^{-p₂})` are the translations
  `s ↦ s - p₁`, `ζ ↦ ζ - p₂` of the log coordinates `s = log z`, `ζ = log tan θ`
  (`logPull_shift`).

The `θ`-half (`Dth_Jeps`) is in `Submission/Work/FTS/StrongEps/CommuteTheta.lean` and the iterated
forms (`D_z^j D_θ^i`) in `Submission/Work/FTS/StrongEps/CommuteIter.lean`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.Kernel

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
