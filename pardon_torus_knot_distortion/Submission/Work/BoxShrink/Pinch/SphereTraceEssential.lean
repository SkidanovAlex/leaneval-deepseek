import Submission.Work.BoxShrink.Pinch.BubbleHalfRefuted
import Submission.Work.BoxShrink.Pinch.Bridge

/-!
# At the standard small box the sphere trace *is* essential

`BubbleHalfRefuted.lean` shows that at the standard round torus with the small box
`s = 3/2`, `c = 0`, `σ = swap 1 2`, `u = 0` Pardon's Lemma 3 conclusion fails.  It is natural to
ask whether that configuration also refutes the *corrected* interfaces
(`Work.BoxShrink.Bubble.PushOffHalf`, `Work.BoxShrink.Bubble.SmoothHalfS`,
`Work.BoxShrink.Pinch.PinchNoJump`), all of which carry the extra hypothesis
`¬ ContainsEssentialLoop (sphereSet c σ s)`.

This module proves that it does **not**: the sphere trace at that configuration is itself
essential, so that hypothesis fails there.

In coordinates: with `σ = swap 1 2` the box norm is `max(|x|, |z|/2^{1/3}, |y|/2^{2/3})` and the
`z`-term never binds on the torus (`|z| ≤ 1 < 2^{1/3}·3/2`), so

  `boxNorm (torusMap θ φ) = (2 + cos φ) · max(|cos θ|, |sin θ|/2^{2/3})`.

Writing `h θ = max(|cos θ|, |sin θ|/2^{2/3})` (which satisfies `1/2 < h θ ≤ 1`) and solving
`2 + cos φ = 3/(2 h θ)` gives `φ θ = arccos (3/(2 h θ) − 2)`, and then
`boxNorm (torusMap θ (φ θ)) = 3/2` for **every** `θ`.  So `θ ↦ torusMap θ (φ θ)` is a closed curve
of the torus inside `sphereSet 0 (swap 1 2) (3/2)` whose lift advances by `2π` in the *first*
parameter and returns in the second: its winding vector is `(1,0) ≠ 0`.  It is one of the two
components of the boundary of the box region (`BubbleHalfRefuted.boxRegion_essential`), so the
sphere trace wraps once around the torus.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Pinch

noncomputable section

/-- The profile of the box sphere in the meridian direction. -/
def traceProfile (t : ℝ) : ℝ := max |Real.cos t| (|Real.sin t| / (2 : ℝ) ^ (2 / 3 : ℝ))

theorem traceProfile_continuous : Continuous traceProfile :=
  (Real.continuous_cos.abs).max ((Real.continuous_sin.abs).div_const _)

theorem traceProfile_periodic (t : ℝ) :
    traceProfile (t + 2 * Real.pi) = traceProfile t := by
  unfold traceProfile
  rw [Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- The profile is bigger than `1/2`: otherwise `cos² + sin² ≤ 1/4 + 2^{4/3}/4 < 1`. -/
theorem half_lt_traceProfile (t : ℝ) : 1 / 2 < traceProfile t := by
  by_contra h
  push Not at h
  have hk : (0 : ℝ) < (2 : ℝ) ^ (2 / 3 : ℝ) := by positivity
  have hc : |Real.cos t| ≤ 1 / 2 := le_trans (le_max_left _ _) h
  have hs : |Real.sin t| / (2 : ℝ) ^ (2 / 3 : ℝ) ≤ 1 / 2 := le_trans (le_max_right _ _) h
  have hs' : |Real.sin t| ≤ (1 / 2) * (2 : ℝ) ^ (2 / 3 : ℝ) := by
    rw [div_le_iff₀ hk] at hs; linarith
  have h1 : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := Real.cos_sq_add_sin_sq t
  have h2 : Real.cos t ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hc 2
  have h3 : Real.sin t ^ 2 ≤ ((1 / 2) * (2 : ℝ) ^ (2 / 3 : ℝ)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hs' 2
  have hx : ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ 2 = (2 : ℝ) ^ (4 / 3 : ℝ) := by
    rw [sq, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have h4 : ((1 / 2) * (2 : ℝ) ^ (2 / 3 : ℝ)) ^ 2 = (2 : ℝ) ^ (4 / 3 : ℝ) / 4 := by
    rw [mul_pow, hx]; ring
  have h5 : (2 : ℝ) ^ (4 / 3 : ℝ) < 8 / 3 := two_rpow_four_thirds_lt
  have h6 : ((1 / 2 : ℝ) ^ 2 : ℝ) = 1 / 4 := by norm_num
  rw [h6] at h2
  nlinarith [h1, h2, h3, h4, h5]

theorem traceProfile_le_one (t : ℝ) : traceProfile t ≤ 1 := by
  refine max_le ?_ ?_
  · rw [abs_le]; exact ⟨Real.neg_one_le_cos t, Real.cos_le_one t⟩
  · have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 / 3 : ℝ) := Submission.one_le_rpow_two_thirds
    have h2 : (0 : ℝ) < (2 : ℝ) ^ (2 / 3 : ℝ) := by linarith
    rw [div_le_one h2]
    calc |Real.sin t| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin t, Real.sin_le_one t⟩
      _ ≤ (2 : ℝ) ^ (2 / 3 : ℝ) := h1

/-- The level of the box sphere at the standard small configuration, as a function of `θ`. -/
def tracePhi (t : ℝ) : ℝ := Real.arccos (3 / (2 * traceProfile t) - 2)

theorem tracePhi_arg_mem (t : ℝ) : 3 / (2 * traceProfile t) - 2 ∈ Set.Icc (-1 : ℝ) 1 := by
  have hp := half_lt_traceProfile t
  have h1 := traceProfile_le_one t
  have h2 : (0 : ℝ) < 2 * traceProfile t := by linarith
  have hle : 3 / (2 * traceProfile t) ≤ 3 := by
    rw [div_le_iff₀ h2]; nlinarith
  have hge : 3 / 2 ≤ 3 / (2 * traceProfile t) := by
    rw [le_div_iff₀ h2]; nlinarith
  exact ⟨by linarith, by linarith⟩

theorem tracePhi_continuous : Continuous tracePhi := by
  unfold tracePhi
  refine Real.continuous_arccos.comp ?_
  refine Continuous.sub (Continuous.div continuous_const ?_ ?_) continuous_const
  · exact continuous_const.mul traceProfile_continuous
  · intro t
    have := half_lt_traceProfile t
    positivity

theorem tracePhi_periodic (t : ℝ) : tracePhi (t + 2 * Real.pi) = tracePhi t := by
  unfold tracePhi
  rw [traceProfile_periodic]

theorem tracePhi_spec (t : ℝ) : 2 + Real.cos (tracePhi t) = 3 / (2 * traceProfile t) := by
  unfold tracePhi
  rw [Real.cos_arccos (tracePhi_arg_mem t).1 (tracePhi_arg_mem t).2]
  ring

/-- **The box norm along the curve `θ ↦ (θ, tracePhi θ)` is exactly `3/2`.** -/
theorem boxNorm_tracePhi (t : ℝ) :
    Submission.boxNorm 0 (Equiv.swap 1 2) (Work.Core.torusMap t (tracePhi t)) = 3 / 2 := by
  have hspec : 2 + Real.cos (tracePhi t) = 3 / (2 * traceProfile t) := tracePhi_spec t
  set a : ℝ := 2 + Real.cos (tracePhi t) with ha
  have hspec' : a = 3 / (2 * traceProfile t) := by rw [ha]; exact hspec
  have hapos : 0 < a := by
    have : Real.cos (tracePhi t) ≥ -1 := Real.neg_one_le_cos _
    rw [ha]; linarith
  -- the two non-trivial terms
  have hA : |(Work.Core.torusMap t (tracePhi t)).ofLp 0| = a * |Real.cos t| := by
    rw [torusMap_apply_zero, abs_mul, ← ha, abs_of_pos hapos]
  have hB : |(Work.Core.torusMap t (tracePhi t)).ofLp 1| / (2 : ℝ) ^ (2 / 3 : ℝ)
      = a * (|Real.sin t| / (2 : ℝ) ^ (2 / 3 : ℝ)) := by
    rw [torusMap_apply_one, abs_mul, ← ha, abs_of_pos hapos]
    ring
  have hZ : |(Work.Core.torusMap t (tracePhi t)).ofLp 2| / (2 : ℝ) ^ (1 / 3 : ℝ) ≤ 3 / 2 := by
    rw [torusMap_apply_two,
      div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (1 / 3 : ℝ))]
    have h1 : |Real.sin (tracePhi t)| ≤ 1 :=
      abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (1 / 3 : ℝ) := Submission.one_le_rpow_third
    calc |Real.sin (tracePhi t)| ≤ 1 := h1
      _ ≤ (3 / 2) * (2 : ℝ) ^ (1 / 3 : ℝ) := by nlinarith
  -- the maximum of the two non-trivial terms is `3/2`
  have hmax : max (a * |Real.cos t|) (a * (|Real.sin t| / (2 : ℝ) ^ (2 / 3 : ℝ))) = 3 / 2 := by
    rw [← mul_max_of_nonneg _ _ (le_of_lt hapos), ← traceProfile, hspec']
    have hne : traceProfile t ≠ 0 :=
      ne_of_gt (lt_trans (by norm_num) (half_lt_traceProfile t))
    field_simp
  rw [std_boxNorm, hA, hB]
  -- rearrange: `max (max A Z) B = max (max A B) Z = 3/2`
  rw [max_assoc, max_comm (|(Work.Core.torusMap t (tracePhi t)).ofLp 2| /
      (2 : ℝ) ^ (1 / 3 : ℝ)) (a * (|Real.sin t| / (2 : ℝ) ^ (2 / 3 : ℝ))), ← max_assoc]
  rw [hmax, max_eq_left hZ]

/-- **At the standard small box the sphere trace is essential.**  The curve
`s ↦ (2πs, tracePhi (2πs))` is a periodic path of the preimage of `sphereSet 0 (swap 1 2) (3/2)`
with shift `2π·(1,0)`, so the exact criterion of `Bridge.lean` produces an essential loop of the
torus inside the sphere trace. -/
theorem sphereSet_threeHalves_essential :
    Work.CoreTopology.standard.ContainsEssentialLoop
      (Work.BoxShrink.Core.sphereSet 0 (Equiv.swap 1 2) (3 / 2)) := by
  refine containsEssentialLoop_of_periodicPath (P := Work.CoreTopology.standard)
    (X := Work.BoxShrink.Core.sphereSet 0 (Equiv.swap 1 2) (3 / 2))
    (q := fun s : ℝ => (2 * Real.pi * s, tracePhi (2 * Real.pi * s)))
    (continuous_const.mul continuous_id |>.prodMk
      (tracePhi_continuous.comp (continuous_const.mul continuous_id)))
    (k := 1) (l := 0) ?_ ?_ ?_
  · intro t
    show (2 * Real.pi * (t + 1), tracePhi (2 * Real.pi * (t + 1))) =
      (2 * Real.pi * t, tracePhi (2 * Real.pi * t)) + Work.TorusCover.periodShift (1, 0)
    have h : 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi := by ring
    rw [h, tracePhi_periodic, Work.TorusCover.periodShift, Prod.mk_add_mk]
    ext <;> simp <;> ring
  · simp
  · intro t
    rw [Phi, Work.BoxShrink.Core.mem_sphereSet, standard_psi]
    exact boxNorm_tracePhi (2 * Real.pi * t)

end

end Work.BoxShrink.Pinch
