import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.RemovableSingularity
import Submission.Commons.Analysis.Complex.exp_I_mul_eq_of_norm_one

namespace Commons.Analysis.Complex

open Filter Metric Set Topology
open scoped Topology Real

noncomputable section

/-! ## Auxiliary lemmas for the exterior Jensen formula

The exterior Jensen formula is obtained from Mathlib's (interior) Jensen formula
`AnalyticOnNhd.circleAverage_log_norm` by inverting the exterior: the function
`w ↦ H w⁻¹` (with the removable singularity at `0` filled by the value `L` of `H`
at infinity) is analytic on the closed unit ball, and the zeros of `H` outside the
unit disc correspond to the zeros of `w ↦ H w⁻¹` inside the unit disc (with the
same multiplicity, inversion being a local biholomorphism), the weights
`log (1/‖w‖)` and `log ‖w⁻¹‖` matching up. -/

/-- **Inversion tends to infinity along the exterior filter.**  If `‖w‖ → ∞` then
`w ↦ w⁻¹` tends to `0`; conversely we record the form needed below: `w ↦ w⁻¹`,
for `w → 0` with `w ≠ 0`, tends to infinity in the sense of the filter
`comap (fun z => ‖z‖) atTop`. -/
theorem tendsto_inv_nhdsNE_zero_comap_norm_atTop :
    Tendsto (fun w : ℂ => w⁻¹) (𝓝[≠] (0 : ℂ))
      (Filter.comap (fun z : ℂ => ‖z‖) Filter.atTop) := by
  rw [tendsto_comap_iff]
  have h : Tendsto (fun w : ℂ => (‖w‖)⁻¹) (𝓝[≠] (0 : ℂ)) Filter.atTop :=
    tendsto_norm_nhdsNE_zero.inv_tendsto_nhdsGT_zero
  simpa [Function.comp_def, norm_inv] using h

/-- **The inversion of the exterior is analytic at the origin.**  If `H` is
analytic on the closed exterior `{1 ≤ ‖z‖}` and tends to `L` at infinity, then the
function `w ↦ H w⁻¹` (extended by `L` at `0`) is analytic at `0`. -/
theorem analyticAt_inv_comp_zero_of_tendsto_comap_norm {H : ℂ → ℂ} {L : ℂ}
    (hH : ∀ z : ℂ, 1 ≤ ‖z‖ → AnalyticAt ℂ H z)
    (hL : Filter.Tendsto H (Filter.comap (fun z : ℂ => ‖z‖) Filter.atTop) (nhds L)) :
    AnalyticAt ℂ (fun w : ℂ => if w = 0 then L else H w⁻¹) 0 := by
  refine _root_.Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_
  · have hball : ∀ᶠ w : ℂ in 𝓝 (0 : ℂ), w ∈ Metric.ball (0 : ℂ) 1 :=
      Metric.ball_mem_nhds 0 one_pos
    filter_upwards [self_mem_nhdsWithin, hball.filter_mono nhdsWithin_le_nhds] with w hw0 hw
    have hwle : ‖w‖ ≤ 1 := le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hw)
    have hw1 : 1 ≤ ‖w⁻¹‖ := by
      rw [norm_inv]
      exact (one_le_inv₀ (norm_pos_iff.mpr hw0)).mpr hwle
    have hev : (fun z : ℂ => if z = 0 then L else H z⁻¹) =ᶠ[𝓝 w] (fun z : ℂ => H z⁻¹) := by
      filter_upwards [isOpen_ne.mem_nhds hw0] with z hz
      simp [hz]
    exact DifferentiableAt.congr_of_eventuallyEq
      (((hH w⁻¹ hw1).comp (analyticAt_inv (𝕝 := ℂ) hw0)).differentiableAt) hev
  · rw [continuousAt_iff_punctured_nhds]
    have hcomp : Tendsto (fun w : ℂ => H w⁻¹) (𝓝[≠] (0 : ℂ)) (𝓝 L) :=
      hL.comp tendsto_inv_nhdsNE_zero_comap_norm_atTop
    have hev : (fun w : ℂ => if w = 0 then L else H w⁻¹) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun w : ℂ => H w⁻¹) := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      have hw' : w ≠ 0 := by simpa using hw
      simp [hw']
    have := hcomp.congr' hev.symm
    simpa using this

/-- **The inversion of the exterior is analytic on the closed unit ball.** -/
theorem analyticOnNhd_inv_comp_closedBall {H : ℂ → ℂ} {L : ℂ}
    (hH : ∀ z : ℂ, 1 ≤ ‖z‖ → AnalyticAt ℂ H z)
    (hL : Filter.Tendsto H (Filter.comap (fun z : ℂ => ‖z‖) Filter.atTop) (nhds L)) :
    AnalyticOnNhd ℂ (fun w : ℂ => if w = 0 then L else H w⁻¹) (Metric.closedBall (0 : ℂ) 1) := by
  intro z hz
  by_cases hz0 : z = 0
  · subst hz0
    exact analyticAt_inv_comp_zero_of_tendsto_comap_norm hH hL
  · have hzle : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hz
    have hz1 : 1 ≤ ‖z⁻¹‖ := by
      rw [norm_inv]
      exact (one_le_inv₀ (norm_pos_iff.mpr hz0)).mpr hzle
    have h1 : AnalyticAt ℂ (fun w : ℂ => H w⁻¹) z :=
      (hH z⁻¹ hz1).comp (analyticAt_inv (𝕝 := ℂ) hz0)
    refine h1.congr ?_
    filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
    simp [hw]

/-- Hypothesis `hcirc` transferred to the unit circle: `H` has no zero on the
unit circle. -/
theorem ne_zero_of_norm_eq_one {H : ℂ → ℂ}
    (hcirc : ∀ θ : ℝ, H (_root_.Complex.exp (θ * Complex.I)) ≠ 0) {w : ℂ} (hw : ‖w‖ = 1) :
    H w ≠ 0 := by
  obtain ⟨σ, hσ⟩ := Commons.Analysis.Complex.exp_I_mul_eq_of_norm_one hw
  rw [← hσ]
  exact hcirc σ

/-- **Divisors agree under inversion.**  The divisor on the closed unit ball of
`w ↦ H w⁻¹` at `u` equals the divisor on the exterior `{1 < ‖z‖}` of `H` at
`u⁻¹`.  This is the pointwise form of the change of variables in the exterior
Jensen formula; no hypothesis on the zeros is needed, since both divisors are
zero off the relevant region. -/
theorem divisor_inv_comp_eq {H : ℂ → ℂ} {L : ℂ}
    (hH : ∀ z : ℂ, 1 ≤ ‖z‖ → AnalyticAt ℂ H z)
    (hL : Filter.Tendsto H (Filter.comap (fun z : ℂ => ‖z‖) Filter.atTop) (nhds L))
    (hL0 : L ≠ 0)
    (hcirc : ∀ θ : ℝ, H (_root_.Complex.exp (θ * Complex.I)) ≠ 0) (u : ℂ) :
    MeromorphicOn.divisor (fun w : ℂ => if w = 0 then L else H w⁻¹)
        (Metric.closedBall (0 : ℂ) 1) u
      = MeromorphicOn.divisor H {z : ℂ | 1 < ‖z‖} u⁻¹ := by
  have hf_an : AnalyticOnNhd ℂ (fun w : ℂ => if w = 0 then L else H w⁻¹)
      (Metric.closedBall (0 : ℂ) 1) := analyticOnNhd_inv_comp_closedBall hH hL
  have hH_an : AnalyticOnNhd ℂ H {z : ℂ | 1 < ‖z‖} := fun z hz => hH z (le_of_lt hz)
  rcases eq_or_ne u 0 with rfl | hu0
  · have h0 : analyticOrderAt (fun w : ℂ => if w = 0 then L else H w⁻¹) (0 : ℂ) = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr (by simpa using hL0))
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf_an (by simp),
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ (by simp), h0]
    simp
  · by_cases hu : ‖u‖ ≤ 1
    · by_cases hu1 : ‖u‖ = 1
      · have huCB : u ∈ Metric.closedBall (0 : ℂ) 1 := by
          simpa [Metric.mem_closedBall] using hu
        have hfu : (fun w : ℂ => if w = 0 then L else H w⁻¹) u ≠ 0 := by
          have hu1' : ‖u⁻¹‖ = 1 := by rw [norm_inv, hu1]; simp
          have : H u⁻¹ ≠ 0 := ne_zero_of_norm_eq_one hcirc hu1'
          simp [hu0, this]
        have h0 : analyticOrderAt (fun w : ℂ => if w = 0 then L else H w⁻¹) u = 0 :=
          analyticOrderAt_eq_zero.mpr (Or.inr hfu)
        rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf_an huCB, h0,
          Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ (by simp [norm_inv, hu1])]
        simp
      · have hult : ‖u‖ < 1 := lt_of_le_of_ne hu hu1
        have huCB : u ∈ Metric.closedBall (0 : ℂ) 1 := by
          simpa [Metric.mem_closedBall] using hu
        have huE : u⁻¹ ∈ {z : ℂ | 1 < ‖z‖} := by
          show 1 < ‖u⁻¹‖
          rw [norm_inv]
          exact (one_lt_inv₀ (norm_pos_iff.mpr hu0)).mpr hult
        have hev : (fun w : ℂ => if w = 0 then L else H w⁻¹) =ᶠ[𝓝 u] (fun w : ℂ => H w⁻¹) := by
          filter_upwards [isOpen_ne.mem_nhds hu0] with w hw
          simp [hw]
        have hord : analyticOrderAt (fun w : ℂ => if w = 0 then L else H w⁻¹) u
            = analyticOrderAt H u⁻¹ := by
          rw [analyticOrderAt_congr hev]
          exact analyticOrderAt_comp_of_deriv_ne_zero (g := fun w : ℂ => w⁻¹)
            (analyticAt_inv (𝕝 := ℂ) hu0) (by rw [deriv_inv]; simp [hu0])
        rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf_an huCB,
          MeromorphicOn.AnalyticOnNhd.divisor_apply hH_an huE, hord]
    · have huCB : u ∉ Metric.closedBall (0 : ℂ) 1 := by
        intro h
        exact hu (by simpa [Metric.mem_closedBall] using h)
      have huE : u⁻¹ ∉ {z : ℂ | 1 < ‖z‖} := by
        intro h
        have h1 : 1 < ‖u⁻¹‖ := h
        rw [norm_inv] at h1
        have hu1 : ‖u‖ < 1 := (one_lt_inv₀ (norm_pos_iff.mpr hu0)).mp h1
        exact absurd (le_of_lt hu1) hu
      rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ huCB,
        Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ huE]

/-- **Exterior Jensen formula.**  Let `H` be analytic on the closed exterior
`{z : ℂ | 1 ≤ ‖z‖}` of the unit disc, tending to `L ≠ 0` at infinity, and nonzero
on the unit circle.  Then

`log ‖L‖ + ∑_{H z = 0, ‖z‖ > 1} ord_z(H) · log ‖z‖ = (1/2π) ∫₀^{2π} log ‖H(e^{iθ})‖ dθ`,

where the sum runs over the zeros of `H` in the exterior, counted with
multiplicity (`MeromorphicOn.divisor`).  It is obtained from the discrete form of
Jensen's formula by inverting the exterior into the unit disc. -/
theorem exterior_jensen (H : ℂ → ℂ) (L : ℂ)
    (hH : ∀ z : ℂ, 1 ≤ ‖z‖ → AnalyticAt ℂ H z)
    (hL : Filter.Tendsto H (Filter.comap (fun z : ℂ => ‖z‖) Filter.atTop) (nhds L))
    (hL0 : L ≠ 0)
    (hcirc : ∀ θ : ℝ, H (Complex.exp (θ * Complex.I)) ≠ 0) :
    Real.log ‖L‖
        + ∑ᶠ z : ℂ, (MeromorphicOn.divisor H {z : ℂ | 1 < ‖z‖} z : ℝ) * Real.log ‖z‖
      = (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi), Real.log ‖H (Complex.exp (θ * Complex.I))‖ := by
  have hf_an : AnalyticOnNhd ℂ (fun w : ℂ => if w = 0 then L else H w⁻¹)
      (Metric.closedBall (0 : ℂ) 1) := analyticOnNhd_inv_comp_closedBall hH hL
  have hf_an1 : AnalyticOnNhd ℂ (fun w : ℂ => if w = 0 then L else H w⁻¹)
      (Metric.closedBall (0 : ℂ) |(1 : ℝ)|) := by
    rw [abs_one]; exact hf_an
  have hf0 : (fun w : ℂ => if w = 0 then L else H w⁻¹) 0 = L := by simp
  have hf0' : (if (0 : ℂ) = 0 then L else H (0 : ℂ)⁻¹) = L := by simp
  have hf0ne : (fun w : ℂ => if w = 0 then L else H w⁻¹) 0 ≠ 0 := by rw [hf0]; exact hL0
  have hJ := hf_an1.circleAverage_log_norm (c := 0) (R := 1)
    (f := fun w : ℂ => if w = 0 then L else H w⁻¹) one_ne_zero hf0ne
  rw [abs_one] at hJ
  -- The finsum of Jensen's formula is the exterior divisor sum.
  have hsum :
      (∑ᶠ u : ℂ, ↑((MeromorphicOn.divisor (fun w : ℂ => if w = 0 then L else H w⁻¹)
            (Metric.closedBall (0 : ℂ) 1)) u) * Real.log (1 * ‖(0 : ℂ) - u‖⁻¹))
        = ∑ᶠ z : ℂ, (MeromorphicOn.divisor H {z : ℂ | 1 < ‖z‖} z : ℝ) * Real.log ‖z‖ := by
    calc ∑ᶠ u : ℂ, ↑((MeromorphicOn.divisor (fun w : ℂ => if w = 0 then L else H w⁻¹)
              (Metric.closedBall (0 : ℂ) 1)) u) * Real.log (1 * ‖(0 : ℂ) - u‖⁻¹)
        = ∑ᶠ u : ℂ, ↑((MeromorphicOn.divisor (fun w : ℂ => if w = 0 then L else H w⁻¹)
              (Metric.closedBall (0 : ℂ) 1)) u) * Real.log ‖u⁻¹‖ := by
          refine finsum_congr (fun u => ?_)
          rw [zero_sub, norm_neg, norm_inv, one_mul]
      _ = ∑ᶠ u : ℂ, ↑((MeromorphicOn.divisor H {z : ℂ | 1 < ‖z‖}) u⁻¹) * Real.log ‖u⁻¹‖ := by
          refine finsum_congr (fun u => ?_)
          rw [divisor_inv_comp_eq hH hL hL0 hcirc u]
      _ = ∑ᶠ z : ℂ, (MeromorphicOn.divisor H {z : ℂ | 1 < ‖z‖} z : ℝ) * Real.log ‖z‖ :=
          finsum_comp (g := fun z : ℂ =>
              (MeromorphicOn.divisor H {z : ℂ | 1 < ‖z‖} z : ℝ) * Real.log ‖z‖)
            (fun u : ℂ => u⁻¹) inv_involutive.bijective
  -- The circle average of `log ‖H‖` is the given integral.
  have hca : Real.circleAverage
        (fun x : ℂ => Real.log ‖(fun w : ℂ => if w = 0 then L else H w⁻¹) x‖) 0 1
      = (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi),
          Real.log ‖H (Complex.exp (θ * Complex.I))‖ := by
    have hcongr : Real.circleAverage
          (fun x : ℂ => Real.log ‖(fun w : ℂ => if w = 0 then L else H w⁻¹) x‖) 0 1
        = Real.circleAverage (fun z : ℂ => Real.log ‖H z⁻¹‖) 0 1 := by
      refine Real.circleAverage_congr_sphere ?_
      intro z hz
      have hz0 : z ≠ 0 := by
        rintro rfl
        simp at hz
      simp [hz0]
    have h2 : Real.circleAverage (fun z : ℂ => Real.log ‖H z⁻¹‖) 0 1
        = Real.circleAverage (fun z : ℂ => Real.log ‖H z‖) 0 1 :=
      Real.circleAverage_zero_one_congr_inv (f := fun z : ℂ => Real.log ‖H z‖)
    rw [hcongr, h2, Real.circleAverage_def, smul_eq_mul]
    congr 1
    exact intervalIntegral.integral_congr (fun θ _ => by simp [circleMap_zero])
  have hJ' : Real.circleAverage
        (fun x : ℂ => Real.log ‖(fun w : ℂ => if w = 0 then L else H w⁻¹) x‖) 0 1
      = (∑ᶠ z : ℂ, (MeromorphicOn.divisor H {z : ℂ | 1 < ‖z‖} z : ℝ) * Real.log ‖z‖)
        + Real.log ‖L‖ := by
    rw [hJ, hsum, hf0']
  rw [hca] at hJ'
  rw [hJ']
  ring

end

end Commons.Analysis.Complex