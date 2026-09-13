/-
The mean value property for continuous viscosity subsolutions of the Laplacian (subharmonic
functions), and the localization of viscosity subsolutions to open subsets.

This is the first half of the proof that the Hessian of a continuous 2-convex function is a
Radon measure (Chaudhuri--Trudinger `[CT]` Theorem 2.4), see `Submission/Roadmap.md`, SESSION 12.
-/
import Mathlib
import Submission.MasterEstimate
import Submission.AlexandrovInputs
import Submission.Viscosity
import Submission.Commons.Analysis.Viscosity.strict_comparison_laplacian
import Submission.Commons.Analysis.ContDiff.exists_contDiff_eqOn_nhds_of_contDiffOn_of_ne_omega
import Submission.Commons.Analysis.Harmonic.exists_harmonicOn_ball_eqOn_sphere
import Submission.Commons.Analysis.Laplace.laplacian_add_quad
import Submission.Commons.Analysis.Harmonic.sphereAverage_harmonic_C2
import Submission.Commons.Analysis.Harmonic.le_setAverage_ball_of_forall_sphere
import Submission.Commons.Analysis.Harmonic.integral_laplacian_nonneg_of_ball_meanValue_cs
import Submission.Commons.Analysis.Calculus.FDeriv.laplacian_eq_trace_hessian
import Submission.Commons.Analysis.Calculus.FDeriv.hessianWithin_eq_hessian

open HessianEstimates
open MeasureTheory Metric Set Filter Function
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- A viscosity subsolution on `s` restricts to any open subset `t ⊆ s`.

The only point needing care is that the test function in the definition must be `C²` on the
whole of `s`, so the given `C²` function on `t` is first extended (by a bump cutoff) to a globally
`C²` function agreeing with it near `x`
(`Commons.Analysis.ContDiff.exists_contDiff_eqOn_nhds_of_contDiffOn`). -/
theorem isViscSubsolution_mono {F : (ℝ⁴ →L[ℝ] ℝ⁴) → ℝ} {u : ℝ⁴ → ℝ} {s t : Set ℝ⁴}
    (ht : IsOpen t) (hts : t ⊆ s) (h : IsViscSubsolution F u s) : IsViscSubsolution F u t := by
  intro φ hφ x hx hmax
  obtain ⟨φ', hφ', heq⟩ :=
    Commons.Analysis.ContDiff.exists_contDiff_eqOn_nhds_of_contDiffOn_of_ne_omega 2
      (by decide) ht hx hφ
  have hφ's : ContDiffOn ℝ 2 φ' s := hφ'.contDiffOn
  have hs_mem : s ∈ 𝓝 x := Filter.mem_of_superset (ht.mem_nhds hx) hts
  have hle : 𝓝[s] x ≤ 𝓝[t] x :=
    (nhdsWithin_le_iff (s := s) (t := t) (x := x)).mpr
      (mem_nhdsWithin_of_mem_nhds (ht.mem_nhds hx))
  have hmax'' : ∀ᶠ y in 𝓝[t] x, u y - φ' y ≤ u x - φ' x := by
    have hx' : φ' x = φ x := heq.self_of_nhds
    filter_upwards [hmax, heq.filter_mono (nhdsWithin_le_nhds (a := x))] with y h1 h2
    rw [h2, hx']
    exact h1
  have hmax' : ∀ᶠ y in 𝓝[s] x, u y - φ' y ≤ u x - φ' x := hmax''.filter_mono hle
  have hHess : HessOp φ' s x = HessOp φ t x := by
    unfold HessOp
    rw [Commons.Analysis.Calculus.FDeriv.hessianWithin_eq_hessian (u := φ') hs_mem,
        Commons.Analysis.Calculus.FDeriv.hessianWithin_eq_hessian (u := φ) (ht.mem_nhds hx)]
    exact congrArg InnerProductSpace.continuousLinearMapOfBilin
      heq.fderiv.fderiv_eq
  have h1 : F (HessOp φ' s x) ≤ 0 := h φ' hφ's x (hts hx) hmax'
  rw [hHess] at h1
  exact h1


/-- `IsViscSubsolution negTrace u s` in raw Laplacian form: at a smooth test function touching
`u` from above, the Laplacian of the test function is nonnegative. -/
theorem viscSubharmonic_raw {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s)
    (h : IsViscSubsolution negTrace u s) :
    ∀ φ : ℝ⁴ → ℝ, ContDiffOn ℝ 2 φ s → ∀ x ∈ s,
      (∀ᶠ y in 𝓝[s] x, u y - φ y ≤ u x - φ x) → 0 ≤ Laplacian.laplacian φ x := by
  intro φ hφ x hx hmax
  have h1 := h φ hφ x hx hmax
  have h2 := Commons.Analysis.Calculus.FDeriv.laplacian_eq_trace_hessian hs hx hφ
    (stdOrthonormalBasis ℝ ℝ⁴)
  rw [h2]
  have h3 := h1
  unfold negTrace HessOp at h3
  linarith

/-- **Comparison with harmonic functions.**  A continuous viscosity subharmonic function on the
open set `s` is bounded above on `closedBall c R` by any smooth harmonic function on `ball c R`
that agrees with it on the sphere. -/
theorem le_of_harmonic {u h : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s)
    (hu : ContinuousOn u s) (hvis : IsViscSubsolution negTrace u s)
    {c : ℝ⁴} {R : ℝ} (hR : 0 < R) (hsub : closedBall c R ⊆ s)
    (hh : ContDiffOn ℝ 2 h (ball c R))
    (hΔ : ∀ x ∈ ball c R, Laplacian.laplacian h x = 0)
    (hcont : ContinuousOn h (closedBall c R))
    (hbd : ∀ y ∈ sphere c R, u y = h y) :
    ∀ y ∈ closedBall c R, u y ≤ h y := by
  have hu' : ContinuousOn u (closedBall c R) := hu.mono hsub
  have hvis' : IsViscSubsolution negTrace u (ball c R) :=
    isViscSubsolution_mono (t := ball c R) (s := s) isOpen_ball
      (ball_subset_closedBall.trans hsub) hvis
  have hraw := viscSubharmonic_raw isOpen_ball hvis'
  have key : ∀ δ : ℝ, 0 < δ → ∀ y ∈ closedBall c R,
      u y ≤ h y + δ * (R ^ 2 - ‖y - c‖ ^ 2) := by
    intro δ hδ
    have hquad : ContDiffOn ℝ 2 (fun y : ℝ⁴ => R ^ 2 - ‖y - c‖ ^ 2) (ball c R) :=
      (contDiffOn_const (𝕜 := ℝ) (c := R ^ 2) (s := ball c R)).sub
        (ContDiffOn.norm_sq ℝ (contDiffOn_id.sub contDiffOn_const))
    have hvcd : ContDiffOn ℝ 2 (fun y : ℝ⁴ => h y + δ * (R ^ 2 - ‖y - c‖ ^ 2)) (ball c R) :=
      hh.add ((contDiffOn_const (𝕜 := ℝ) (c := δ) (s := ball c R)).mul hquad)
    have hvc : ContinuousOn (fun y : ℝ⁴ => h y + δ * (R ^ 2 - ‖y - c‖ ^ 2))
        (closedBall c R) :=
      hcont.add (continuousOn_const.mul (by fun_prop :
        ContinuousOn (fun y : ℝ⁴ => R ^ 2 - ‖y - c‖ ^ 2) (closedBall c R)))
    have hstrict : ∀ x ∈ ball c R,
        Laplacian.laplacian (fun y : ℝ⁴ => h y + δ * (R ^ 2 - ‖y - c‖ ^ 2)) x < 0 := by
      intro x hx
      have hcx : ContDiffAt ℝ 2 h x :=
        (hh.contDiffWithinAt hx).contDiffAt (isOpen_ball.mem_nhds hx)
      rw [Commons.Analysis.Laplace.laplacian_add_quad (n := 4) hcx δ R, hΔ x hx]
      ring_nf
      linarith
    have hsphere : ∀ y ∈ sphere c R,
        u y ≤ (fun y : ℝ⁴ => h y + δ * (R ^ 2 - ‖y - c‖ ^ 2)) y := by
      intro y hy
      have hdist : ‖y - c‖ = R := by
        have h1 := hy
        rw [mem_sphere] at h1
        rwa [dist_eq_norm] at h1
      show u y ≤ h y + δ * (R ^ 2 - ‖y - c‖ ^ 2)
      rw [hdist, hbd y hy]
      ring_nf
      linarith
    exact Commons.Analysis.Viscosity.strict_comparison_laplacian hR hu' hvcd hvc hraw hstrict
      hsphere
  intro y hy
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hq : (0:ℝ) ≤ R ^ 2 - ‖y - c‖ ^ 2 := by
    have h1 : ‖y - c‖ ≤ R := by rw [← dist_eq_norm]; exact mem_closedBall.mp hy
    nlinarith [hR, norm_nonneg (y - c), h1]
  have hpos : 0 < R ^ 2 - ‖y - c‖ ^ 2 + 1 := by linarith
  have hδ : 0 < ε / (R ^ 2 - ‖y - c‖ ^ 2 + 1) := div_pos hε hpos
  have h1 := key (ε / (R ^ 2 - ‖y - c‖ ^ 2 + 1)) hδ y hy
  have h2 : ε / (R ^ 2 - ‖y - c‖ ^ 2 + 1) * (R ^ 2 - ‖y - c‖ ^ 2) ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    nlinarith
  linarith

/-- **Sphere mean value property for a continuous viscosity subharmonic function.**  If `u` is
continuous and viscosity subharmonic on the open set `s`, then the average of `u` over any sphere
`sphere c R` with `closedBall c R ⊆ s` is at least `u c`.

This is the classical first step in the theory of subharmonic functions; the proof uses the
Dirichlet problem for the ball (`exists_harmonicOn_ball_eqOn_sphere`), the strict comparison
principle (`strict_comparison_laplacian`) and the mean value property for harmonic functions
(`sphereAverage_harmonic_C2`). -/
theorem viscSubharmonic_sphere_le {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s)
    (hu : ContinuousOn u s) (hvis : IsViscSubsolution negTrace u s)
    {c : ℝ⁴} {R : ℝ} (hR : 0 < R) (hsub : closedBall c R ⊆ s) :
    (∫ θ : Metric.sphere (0 : ℝ⁴) 1, (1 : ℝ) ∂MeasureTheory.volume.toSphere) * u c ≤
      ∫ θ : Metric.sphere (0 : ℝ⁴) 1, u (c + R • (θ : ℝ⁴))
        ∂MeasureTheory.volume.toSphere := by
  have hcont_sphere : ContinuousOn u (sphere c R) :=
    hu.mono (Metric.sphere_subset_closedBall.trans hsub)
  obtain ⟨h, hh, hΔ, hcnt, hbd⟩ :=
    Commons.Analysis.Harmonic.exists_harmonicOn_ball_eqOn_sphere (n := 4) hR hcont_sphere
  have hle := le_of_harmonic hs hu hvis hR hsub hh hΔ hcnt (fun y hy => (hbd y hy).symm)
  have hc : u c ≤ h c := hle c (mem_closedBall_self hR.le)
  have hav := Commons.Analysis.Harmonic.sphereAverage_harmonic_C2 (n := 4) (by norm_num) hR hh hΔ hcnt
  have hmass : (0:ℝ) ≤ ∫ θ : Metric.sphere (0 : ℝ⁴) 1, (1 : ℝ)
      ∂MeasureTheory.volume.toSphere := integral_nonneg fun _ => zero_le_one
  have hcongr : (∫ θ : Metric.sphere (0 : ℝ⁴) 1, u (c + R • (θ : ℝ⁴))
        ∂MeasureTheory.volume.toSphere)
      = ∫ θ : Metric.sphere (0 : ℝ⁴) 1, h (c + R • (θ : ℝ⁴))
        ∂MeasureTheory.volume.toSphere := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    have hθ : ‖(θ : ℝ⁴)‖ = 1 := by
      have h1 := θ.2
      rw [mem_sphere, dist_eq_norm, sub_zero] at h1
      exact h1
    have hmem : c + R • (θ : ℝ⁴) ∈ sphere c R := by
      rw [mem_sphere, dist_eq_norm,
        show c + R • (θ : ℝ⁴) - c = R • (θ : ℝ⁴) by abel, norm_smul, Real.norm_eq_abs,
        abs_of_pos hR, hθ, mul_one]
    show u (c + R • (θ : ℝ⁴)) = h (c + R • (θ : ℝ⁴))
    rw [hbd _ hmem]
  rw [hcongr, hav]
  exact mul_le_mul_of_nonneg_left hc hmass

/-- **Ball mean value property for a continuous viscosity subharmonic function.** -/
theorem viscSubharmonic_ball_le {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s)
    (hu : ContinuousOn u s) (hvis : IsViscSubsolution negTrace u s)
    {c : ℝ⁴} {R : ℝ} (hR : 0 < R) (hsub : closedBall c R ⊆ s) :
    u c ≤ ⨍ y in ball c R, u y := by
  refine Commons.Analysis.Harmonic.le_setAverage_ball_of_forall_sphere (n := 4) hR ?_ ?_
  · exact ((hu.mono hsub).integrableOn_compact (isCompact_closedBall c R)).mono_set
      ball_subset_closedBall
  · intro r hr hrR
    exact viscSubharmonic_sphere_le hs hu hvis hr
      ((closedBall_subset_closedBall hrR).trans hsub)

/-- **`Δu ≥ 0` in the sense of distributions for a continuous `2`-convex function.**  Combining the
ball mean value property (`viscSubharmonic_ball_le`) with the mollification lemma
(`Commons.Analysis.Harmonic.integral_laplacian_nonneg_of_ball_meanValue_cs`). -/
theorem twoConvex_laplacian_nonneg {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s)
    (hu : ContinuousOn u s) (h2 : IsTwoConvexOn u s) :
    ∀ φ : ℝ⁴ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ s → 0 ≤ φ →
      0 ≤ ∫ x, u x * Laplacian.laplacian φ x :=
  Commons.Analysis.Harmonic.integral_laplacian_nonneg_of_ball_meanValue_cs hs hu
    (fun c hc r hr hcr => viscSubharmonic_ball_le hs hu h2.1 hr hcr)

end Submission
