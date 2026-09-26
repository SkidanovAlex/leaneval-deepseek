import Mathlib
import Submission.Work.Drive.EpsForm.DatumCore
import Submission.Work.Drive.EpsForm.WaypointDesign2
import Submission.Work.Drive.EpsForm.WaypointDiscDefs
import Submission.Work.Drive.EpsForm.profX_levels
import Submission.Work.Drive.EpsForm.profX_injOn
import Submission.Work.Drive.EpsForm.continuousOn_eFunX2
import Submission.Work.Drive.EpsForm.eFunX_tendsto_zero
import Submission.Work.Drive.EpsForm.continuous_eDiscX_of
import Submission.Work.Drive.EpsForm.eDiscX_circlePoint
import Submission.Work.Drive.EpsForm.eDiscX_mem_carrier_imp
import Submission.Work.Drive.EpsForm.eFunX_chords
import Submission.Work.Drive.EpsForm.eFunX_injOn_rect
import Submission.Work.Drive.EpsForm.kapGamma_injOn
import Submission.Work.Drive.EpsForm.kapCurve_not_essential

namespace Work.Drive.EpsForm

/-!
## Assembly of `DatumCore` from the corrected waypoint design

The witness disc is `eDiscX` (`WaypointDesign2.lean`), the corrected tube-coordinate disc
map `eDiscX z = eFunX (arg z) ‖z‖`, and the witness curve is `kapCurve`
(`WaypointDiscDefs.lean`), whose trace is the union of the two chords
`t ↦ eFunX t (sig1 t)`, `t ↦ eFunX t (sig2 t)`.

The four geometric inputs are delegated lemmas:

* `continuousOn_eFunX2` and `eFunX_tendsto_zero` (with `eFunX_neg_pi_eq`) give the
  continuity of `eDiscX` through `continuous_eDiscX_of`;
* `eFunX_injOn_rect` (with `profX_injOn`) gives the injectivity of `eDiscX`;
* `eDiscX_circlePoint` gives the prescribed boundary curve `α = standardCurve 1 1`;
* `kapGamma_injOn` and `kapCurve_not_essential` give the simplicity and the
  inessentiality of `κ`, `eFunX_chords` identifies the two chords with the torus points
  `torusMap t (phLift t)` and `torusMap t (phLift t + dlt t)`, and
  `eDiscX_mem_carrier_imp` together with `eFunX_chords` gives the covering condition.
-/

set_option maxHeartbeats 800000

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-- Continuity of the disc map, from the two ingredients about `eFunX`. -/
theorem continuous_eDiscX : Continuous eDiscX :=
  continuous_eDiscX_of continuousOn_eFunX2 eFunX_tendsto_zero (fun s _ => eFunX_neg_pi_eq s)

/-- **Injectivity of the disc map**: the azimuth and the profile are recovered from the
image, except at the origin (the image of the centre of the disc). -/
theorem injective_eDiscX : Function.Injective eDiscX := by
  intro z z' h
  have hz : ‖(z : ℂ)‖ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨norm_nonneg _, by
      have := Metric.mem_closedBall.mp z.2
      rwa [dist_zero_right] at this⟩
  have hz' : ‖(z' : ℂ)‖ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨norm_nonneg _, by
      have := Metric.mem_closedBall.mp z'.2
      rwa [dist_zero_right] at this⟩
  obtain ⟨hs, hcase⟩ := eFunX_injOn_rect
    (Complex.arg (z : ℂ)) (Complex.arg_mem_Ioc (z : ℂ)) ‖(z : ℂ)‖ hz
    (Complex.arg (z' : ℂ)) (Complex.arg_mem_Ioc (z' : ℂ)) ‖(z' : ℂ)‖ hz' h
  apply Subtype.ext
  rcases hcase with h0 | ha
  · have h1 : (z : ℂ) = 0 := norm_eq_zero.mp h0
    have h2 : (z' : ℂ) = 0 := norm_eq_zero.mp (hs ▸ h0)
    rw [h1, h2]
  · have h1 : (z : ℂ) = ↑‖(z : ℂ)‖ * Complex.exp (↑(Complex.arg (z : ℂ)) * Complex.I) :=
      (Complex.norm_mul_exp_arg_mul_I (z : ℂ)).symm
    have h2 : (z' : ℂ) = ↑‖(z' : ℂ)‖ * Complex.exp (↑(Complex.arg (z' : ℂ)) * Complex.I) :=
      (Complex.norm_mul_exp_arg_mul_I (z' : ℂ)).symm
    rw [h1, h2, hs, ha]

/-- **The `κ ⊆ e(𝔻)` part.**  Every point of the trace of `κ` is a point of the closed disc
image: on the rising half of the wave it is the chord point `eFunX t (sig1 t)`, on the
falling half the chord point `eFunX t (sig2 t)`. -/
theorem kapGamma_mem_range_eDiscX_of_mem {s : ℝ} (hs : s ∈ Set.Icc 0 (2 * Real.pi)) :
    kapGamma s ∈ Set.range eDiscX := by
  have htIcc : kapTheta s ∈ Set.Icc u0 v0 := kapTheta_mem s
  have htIoc : kapTheta s ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨neg_pi_lt_kapTheta s, kapTheta_le_pi s⟩
  have hin : inRange (kapTheta s) := ⟨htIcc.1, htIcc.2⟩
  by_cases hsin : 0 < Real.sin s
  · refine ⟨⟨↑(sig1 (kapTheta s)) *
        ((Real.cos (kapTheta s) : ℂ) + Real.sin (kapTheta s) * Complex.I),
        mem_closedBall_mul_cos_add_sin _ (sig1_pos _) (sig1_le_one_of_inRange hin)⟩, ?_⟩
    rw [eDiscX_mul_cos_add_sin htIoc (sig1_pos _) (sig1_le_one_of_inRange hin),
      kapGamma, kapPhi_of_pos hsin]
    exact (eFunX_chords htIcc).1
  · have hle : Real.sin s ≤ 0 := le_of_not_gt hsin
    refine ⟨⟨↑(sig2 (kapTheta s)) *
        ((Real.cos (kapTheta s) : ℂ) + Real.sin (kapTheta s) * Complex.I),
        mem_closedBall_mul_cos_add_sin _ (sig2_pos _) (sig2_le_one_of_inRange hin)⟩, ?_⟩
    rw [eDiscX_mul_cos_add_sin htIoc (sig2_pos _) (sig2_le_one_of_inRange hin),
      kapGamma, kapPhi_of_nonpos hle]
    exact (eFunX_chords htIcc).2

/-- **The `κ ⊆ e(𝔻)` part**, for all real parameters (by `2π`-periodicity). -/
theorem kapGamma_mem_range_eDiscX (s : ℝ) : kapGamma s ∈ Set.range eDiscX := by
  set k : ℤ := ⌊s / (2 * Real.pi)⌋ with hk
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h1 : (k : ℝ) * (2 * Real.pi) ≤ s := by
    have h := Int.floor_le (s / (2 * Real.pi))
    rwa [le_div_iff₀ hpos] at h
  have h2 : s < (k : ℝ) * (2 * Real.pi) + 2 * Real.pi := by
    have h := Int.lt_floor_add_one (s / (2 * Real.pi))
    rw [div_lt_iff₀ hpos] at h
    linarith
  have hs : s - k * (2 * Real.pi) ∈ Set.Icc 0 (2 * Real.pi) := ⟨by linarith, by linarith⟩
  have hper : kapGamma s = kapGamma (s - k * (2 * Real.pi)) := by
    have h := kapGamma_periodic'.int_mul k (s - k * (2 * Real.pi))
    rw [show s - ↑k * (2 * Real.pi) + ↑k * (2 * Real.pi) = s by ring] at h
    exact h
  rw [hper]
  exact kapGamma_mem_range_eDiscX_of_mem hs

/-- **The covering condition**: every point of `e '' (open 𝔻) ∩ Σ` is a point of `κ`. -/
theorem eDiscX_mem_range_kapGamma (z : Metric.closedBall (0 : ℂ) 1) (hz : ‖(z : ℂ)‖ < 1)
    (h : eDiscX z ∈ Work.CoreTopology.standard.carrier) : eDiscX z ∈ Set.range kapGamma := by
  obtain ⟨ht, hcase⟩ := eDiscX_mem_carrier_imp z hz h
  have htIoo : Complex.arg (z : ℂ) ∈ Set.Ioo u0 v0 := by
    refine ⟨?_, ?_⟩
    · by_contra hcon
      push_neg at hcon
      have huu : Complex.arg (z : ℂ) = u0 := le_antisymm hcon ht.1
      rcases hcase with h1 | h1
      · rw [h1, huu, sig1_u0] at hz; exact lt_irrefl _ hz
      · rw [h1, huu, sig2_u0] at hz; exact lt_irrefl _ hz
    · by_contra hcon
      rw [not_lt] at hcon
      have hvv : Complex.arg (z : ℂ) = v0 := le_antisymm ht.2 hcon
      rcases hcase with h1 | h1
      · rw [h1, hvv, sig1_v0] at hz; exact lt_irrefl _ hz
      · rw [h1, hvv, sig2_v0] at hz; exact lt_irrefl _ hz
  rcases hcase with h1 | h1
  · obtain ⟨s, hs, hT, hsin⟩ := exists_kapTheta_eq_of_mem_Ioo htIoo
    refine ⟨s, ?_⟩
    simp only [eDiscX]
    rw [kapGamma, kapPhi_of_pos hsin, hT, h1]
    exact (eFunX_chords ⟨ht.1, ht.2⟩).1.symm
  · obtain ⟨s, hs, hT, hsin⟩ := exists_kapTheta_eq_of_mem_Ioo' htIoo
    refine ⟨s, ?_⟩
    simp only [eDiscX]
    rw [kapGamma, kapPhi_of_nonpos (le_of_lt hsin), hT, h1]
    exact (eFunX_chords ⟨ht.1, ht.2⟩).2.symm

/-- **Pardon's innermost-disc datum on the standard torus**, assembled from the explicit
waypoint design. -/
theorem work_datumCore : Work.Drive.EpsForm.DatumCore := by
  refine ⟨⟨eDiscX, continuous_eDiscX⟩, ?_, ?_, ?_⟩
  · intro z z' h
    exact injective_eDiscX h
  · intro θ
    exact eDiscX_circlePoint θ
  · refine ⟨kapCurve, ?_, kapCurve_not_essential, ?_, ?_⟩
    · simpa only [Work.CoreTopology.IsSimple, kapCurve_gamma] using kapGamma_injOn
    · intro y hy
      obtain ⟨s, rfl⟩ := hy
      exact kapGamma_mem_range_eDiscX s
    · intro z hz hmem
      exact eDiscX_mem_range_kapGamma z hz hmem

end

end Work.Drive.EpsForm
