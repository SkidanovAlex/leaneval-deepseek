import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Instances.Real.Lemmas

namespace Commons.Topology.Curve

set_option autoImplicit false

theorem argument_lift_of_far
    {f : ℝ → ℂ} (hf : Continuous f) (hper : Function.Periodic f 1) :
    ∃ R : ℝ, ∀ p : ℂ, R < ‖p‖ → ∃ θ : ℝ → ℝ, Continuous θ ∧ (∀ t, θ (t + 1) = θ t) ∧
      ∀ t, f t - p = (‖f t - p‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I) := by
  -- A continuous, periodic curve is bounded.
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ t, ‖f t‖ ≤ M := by
    obtain ⟨r, hr⟩ := (hper.isBounded_of_continuous one_ne_zero hf).subset_closedBall (0 : ℂ)
    exact ⟨r, fun t => by
      have h := Metric.mem_closedBall.mp (hr (Set.mem_range_self t))
      rwa [dist_eq_norm, sub_zero] at h⟩
  refine ⟨M, fun p hp => ?_⟩
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (f 0)) (hM 0)
  have hpnorm : 0 < ‖p‖ := lt_of_le_of_lt hM0 hp
  have hpne : p ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hpnorm
    exact lt_irrefl 0 hpnorm
  -- Every point of the curve is within distance `M < ‖p‖` of the origin, so relative to the
  -- fixed nonzero direction `-p` the correction factor `W t = (f t - p) / (-p) = 1 - f t / p`
  -- stays in the disk of radius `M / ‖p‖ < 1` around `1`, a subset of the slit plane.
  set W : ℝ → ℂ := fun t => 1 - f t / p with hW
  have hWapply : ∀ t, W t = 1 - f t / p := fun t => by simp [hW]
  have hWcont : Continuous W := by
    rw [hW]
    exact continuous_const.sub (hf.div_const p)
  have hWslit : ∀ t, W t ∈ Complex.slitPlane := by
    intro t
    have hn : ‖-(f t / p)‖ < 1 := by
      rw [norm_neg, norm_div, div_lt_one hpnorm]
      exact lt_of_le_of_lt (hM t) hp
    have h1 : W t = 1 + -(f t / p) := by rw [hWapply t, sub_eq_add_neg]
    rw [h1]
    exact Complex.mem_slitPlane_of_norm_lt_one hn
  have hWper : ∀ t, W (t + 1) = W t := by
    intro t
    simp only [hWapply, hper t]
  have hWmul : ∀ t, (-p) * W t = f t - p := by
    intro t
    rw [hWapply t, mul_sub, mul_one]
    have hc : (-p) * (f t / p) = -f t := by
      rw [neg_mul, mul_div_cancel₀ (f t) hpne]
    rw [hc]
    ring
  refine ⟨fun t => Complex.arg (-p) + Complex.arg (W t), ?_, ?_, ?_⟩
  · -- Continuity of the argument function.
    refine Continuous.add continuous_const ?_
    rw [continuous_iff_continuousAt]
    intro t
    exact (Complex.continuousAt_arg (hWslit t)).comp hWcont.continuousAt
  · -- Periodicity.
    intro t
    simp only [hWper t]
  · -- The representation identity.
    intro t
    have hneg : (‖-p‖ : ℂ) * Complex.exp ((Complex.arg (-p) : ℂ) * Complex.I) = -p :=
      Complex.norm_mul_exp_arg_mul_I (-p)
    have hWexp : (‖W t‖ : ℂ) * Complex.exp ((Complex.arg (W t) : ℂ) * Complex.I) = W t :=
      Complex.norm_mul_exp_arg_mul_I (W t)
    have hnorm : (‖f t - p‖ : ℂ) = (‖-p‖ : ℂ) * (‖W t‖ : ℂ) := by
      rw [← hWmul t, norm_mul, Complex.ofReal_mul]
    have hexp : Complex.exp (((Complex.arg (-p) + Complex.arg (W t) : ℝ) : ℂ) * Complex.I)
        = Complex.exp ((Complex.arg (-p) : ℂ) * Complex.I)
          * Complex.exp ((Complex.arg (W t) : ℂ) * Complex.I) := by
      rw [Complex.ofReal_add, add_mul, Complex.exp_add]
    have key : (-p) * W t
        = ((‖-p‖ : ℂ) * (‖W t‖ : ℂ))
          * (Complex.exp ((Complex.arg (-p) : ℂ) * Complex.I)
              * Complex.exp ((Complex.arg (W t) : ℂ) * Complex.I)) := by
      conv_lhs => rw [← hneg, ← hWexp]
      ring
    calc f t - p
        = (-p) * W t := (hWmul t).symm
      _ = ((‖-p‖ : ℂ) * (‖W t‖ : ℂ))
            * (Complex.exp ((Complex.arg (-p) : ℂ) * Complex.I)
                * Complex.exp ((Complex.arg (W t) : ℂ) * Complex.I)) := key
      _ = (‖f t - p‖ : ℂ)
            * Complex.exp (((Complex.arg (-p) + Complex.arg (W t) : ℝ) : ℂ) * Complex.I) := by
            rw [← hnorm, ← hexp]

end Commons.Topology.Curve