import Mathlib
import Submission.Work.Sweep.Defs
import Submission.Work.Sweep.PureInterval.volume_circ_arc_le

namespace Work.Sweep.LengthInBall

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal Topology

/-- The arclength of the part of a curve lying in a measurable set `B` of diameter `D`
is at most `2 d D`, where `d` is a distortion bound for the curve. -/
theorem arclengthIn_le_of_diam {K : LeanEval.KnotTheory.PardonDistortion.Knot} {d D : ℝ}
    (hd : 0 ≤ d) (hbound : Work.Sweep.IsDistortionBound K d)
    {B : Set LeanEval.KnotTheory.PardonDistortion.R3} (hBmeas : MeasurableSet B)
    (hD : ∀ y ∈ B, ∀ z ∈ B, dist y z ≤ D)
    (hne : (K.curve '' Set.Ico 0 (2 * Real.pi) ∩ B).Nonempty) :
    Work.Sweep.arclengthIn K (Work.Sweep.paramSetInIco K B) ≤ ENNReal.ofReal (2 * d * D) := by
  classical
  -- A parameter at which the curve meets `B`.
  obtain ⟨y, hy⟩ := hne
  obtain ⟨hyimg, hyB⟩ := hy
  obtain ⟨s₀, hs₀Ico, hs₀eq⟩ := hyimg
  have hs₀B : K.curve s₀ ∈ B := hs₀eq ▸ hyB
  -- The arclength parametrisation of the curve, anchored at `0`.
  set φ : ℝ → ℝ := fun t => ∫ u in (0 : ℝ)..t, speed K u with hφ
  have hspeed_cont : Continuous (speed K) := by
    unfold speed
    exact (K.smooth.continuous_deriv (by simp)).norm
  have hφ_deriv : ∀ t : ℝ, HasDerivAt φ (speed K t) t := by
    intro t
    rw [hφ]
    exact intervalIntegral.integral_hasDerivAt_right (hspeed_cont.intervalIntegrable 0 t)
      (hspeed_cont.stronglyMeasurableAtFilter volume (𝓝 t)) hspeed_cont.continuousAt
  have hφ_pos : ∀ t : ℝ, 0 < deriv φ t := by
    intro t
    rw [(hφ_deriv t).deriv]
    unfold speed
    rw [norm_pos_iff]
    exact K.immersion t
  have hφ_strict : StrictMono φ := strictMono_of_deriv_pos hφ_pos
  have hφ0 : φ 0 = 0 := by rw [hφ]; simp
  have hφ_sub : ∀ a b : ℝ, ∫ u in a..b, speed K u = φ b - φ a := by
    intro a b
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hφ_deriv x)
      (hspeed_cont.intervalIntegrable a b)
  have hφ2pi_pos : 0 < φ (2 * Real.pi) := by
    have h := hφ_strict (show (0 : ℝ) < 2 * Real.pi by linarith [Real.pi_pos])
    rwa [hφ0] at h
  have htotal : totalArcLength K = φ (2 * Real.pi) := by
    rw [totalArcLength, parameterArcLength, hφ_sub 0 (2 * Real.pi), hφ0, sub_zero,
      abs_of_pos hφ2pi_pos]
  -- The set in which the arclength coordinate of a point of `B` must lie.
  have hDnn : 0 ≤ D := by
    have h := hD (K.curve s₀) hs₀B (K.curve s₀) hs₀B
    simpa using h
  have hdD : 0 ≤ d * D := mul_nonneg hd hDnn
  have hu₀ : 0 ≤ φ s₀ := by
    have h := hφ_strict.monotone (show (0 : ℝ) ≤ s₀ from hs₀Ico.1)
    rwa [hφ0] at h
  have hu₀L : φ s₀ ≤ totalArcLength K := by
    rw [htotal]
    exact hφ_strict.monotone (le_of_lt hs₀Ico.2)
  set A : Set ℝ := {u : ℝ | u ∈ Set.Icc 0 (totalArcLength K) ∧
      min |u - φ s₀| (totalArcLength K - |u - φ s₀|) ≤ d * D} with hAdef
  have hvolA : volume A ≤ ENNReal.ofReal (2 * (d * D)) :=
    PureInterval.volume_circ_arc_le (totalArcLength K) (φ s₀) (d * D) hu₀ hu₀L hdD
  -- Every parameter of `B` has arclength coordinate in `A`.
  have himg_sub : φ '' (paramSetInIco K B) ⊆ A := by
    rintro u ⟨t, htE, htu⟩
    rw [← htu]
    obtain ⟨htB, htIco⟩ : K.curve t ∈ B ∧ t ∈ Set.Ico 0 (2 * Real.pi) := by
      simpa only [paramSetInIco, Set.mem_inter_iff, Set.mem_preimage] using htE
    have hintr : intrinsicDistance K s₀ t ≤ d * D := by
      have h1 : intrinsicDistance K s₀ t ≤ d * dist (K.curve s₀) (K.curve t) :=
        hbound s₀ hs₀Ico t htIco
      have h2 : dist (K.curve s₀) (K.curve t) ≤ D := hD _ hs₀B _ htB
      exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hd)
    have hparam : parameterArcLength K s₀ t = |φ t - φ s₀| := by
      rw [parameterArcLength, hφ_sub s₀ t]
    have hintr' : min |φ t - φ s₀| (totalArcLength K - |φ t - φ s₀|) ≤ d * D := by
      have h := hintr
      unfold intrinsicDistance at h
      rwa [hparam] at h
    rw [hAdef]
    refine ⟨⟨?_, ?_⟩, hintr'⟩
    · have h := hφ_strict.monotone htIco.1
      rwa [hφ0] at h
    · rw [htotal]
      exact hφ_strict.monotone (le_of_lt htIco.2)
  -- The arclength is the measure of the image of the parameter set.
  have hEmeas : MeasurableSet (paramSetInIco K B) := by
    rw [paramSetInIco]
    exact (hBmeas.preimage K.smooth.continuous.measurable).inter measurableSet_Ico
  have harclen : arclengthIn K (paramSetInIco K B) = volume (φ '' (paramSetInIco K B)) := by
    rw [arclengthIn]
    exact lintegral_deriv_eq_volume_image_of_monotoneOn hEmeas
      (fun x _ => (hφ_deriv x).hasDerivWithinAt) (hφ_strict.monotone.monotoneOn _)
  calc arclengthIn K (paramSetInIco K B)
      = volume (φ '' (paramSetInIco K B)) := harclen
    _ ≤ volume A := measure_mono himg_sub
    _ ≤ ENNReal.ofReal (2 * (d * D)) := hvolA
    _ = ENNReal.ofReal (2 * d * D) := by
        rw [show 2 * (d * D) = 2 * d * D by ring]

end Work.Sweep.LengthInBall
