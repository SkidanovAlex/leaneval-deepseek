import Mathlib
import Submission.Work.OddVolterra.Free.Defs
import Submission.Work.OddCurve.Free
import Submission.Work.OddEnvelope.Close.isEnvelopeCurve_semicircle
import Submission.Work.OddEnvelope.Sanity
import Submission.Work.OddCurve.semicircle_moment_eqs

namespace Work.OddVolterra.Free

open MeasureTheory Set
open scoped Interval

noncomputable section

/-- On the whole interval `(-1,1)` the *free* envelope profile of the unperturbed semicircle data
is the semicircle itself.  (`envProfileFree` is untruncated, so this is the statement one needs in
place of `Work.OddEnvelope.envelopeProfile_semicircle_eq`, which is about `envelopeProfile`; on
`(-1,1)` the two definitions agree by `envProfileFree_eq_envelopeProfile`.) -/
theorem envProfileFree_zero_profileX_eq {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    envProfileFree (0 : ℝ → ℝ) Work.OddEnvelope.profileX Work.OddEnvelope.profileX t =
      Work.OddEnvelope.semicircle t := by
  rw [envProfileFree_eq_envelopeProfile (h := (0 : ℝ → ℝ)) ht]
  exact Work.OddEnvelope.envelopeProfile_semicircle_eq ht

/-- The unperturbed semicircle satisfies the free-tip envelope interface. -/
theorem isEnvelopeCurveFree_semicircle :
    Work.OddCurve.Free.IsEnvelopeCurveFree (0 : ℝ → ℝ) Work.OddEnvelope.profileX
      Work.OddEnvelope.profileX :=
  Work.OddCurve.Free.isEnvelopeCurveFree_of_isEnvelopeCurve
    Work.OddEnvelope.Close.isEnvelopeCurve_semicircle

/-- The semicircle chord function is `C²`-close to itself. -/
theorem closeToProfileX_profileX :
    Work.OddCurve.LowSlope.CloseToProfileX Work.OddEnvelope.profileX := by
  intro s hs
  refine ⟨?_, ?_, ?_⟩ <;> rw [sub_self, abs_zero] <;> norm_num

/-- On a genuine section (`s > 0`, so that `profileX s < 1`) the radicand of the free envelope
profile of the semicircle data is the ball's radicand `1 - t² - (s t)²`. -/
theorem rad_zero_envProfileFree_profileX_eq {s t : ℝ} (hs : 0 < s)
    (ht : t ∈ Set.Icc (-(Work.OddEnvelope.profileX s)) (Work.OddEnvelope.profileX s)) :
    Work.OddCurve.rad (0 : ℝ → ℝ)
        (envProfileFree (0 : ℝ → ℝ) Work.OddEnvelope.profileX Work.OddEnvelope.profileX) s t =
      1 - t ^ 2 - (s * t) ^ 2 := by
  have hp := Work.OddEnvelope.profileX_pos s
  have hlt := Work.OddEnvelope.profileX_lt_one hs
  have ht' : t ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hsemi : envProfileFree (0 : ℝ → ℝ) Work.OddEnvelope.profileX Work.OddEnvelope.profileX t
      = Work.OddEnvelope.semicircle t := envProfileFree_zero_profileX_eq ht'
  have hsq : Work.OddEnvelope.semicircle t ^ 2 = 1 - t ^ 2 := by
    rw [Work.OddEnvelope.semicircle, Real.sq_sqrt (by nlinarith [ht'.1, ht'.2])]
  rw [Work.OddCurve.rad_def, hsemi]
  simp only [Pi.zero_apply, hsq]
  ring

/-- **The volume moment of the unperturbed semicircle** (`h = 0`, `x = y = profileX`, free
envelope profile): it is the ball's, `refConst n / √(1 + s²)`, on every genuine slope `s > 0`. -/
theorem momentA_envProfileFree_profileX (n : ℕ) {s : ℝ} (hs : 0 < s) :
    Work.OddCurve.momentA n (0 : ℝ → ℝ) Work.OddEnvelope.profileX Work.OddEnvelope.profileX
        (envProfileFree (0 : ℝ → ℝ) Work.OddEnvelope.profileX Work.OddEnvelope.profileX) s =
      Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2) := by
  rw [Work.OddCurve.momentA_def]
  have hcongr :
      (∫ t in (-(Work.OddEnvelope.profileX s))..(Work.OddEnvelope.profileX s),
        Work.OddCurve.rad (0 : ℝ → ℝ)
            (envProfileFree (0 : ℝ → ℝ) Work.OddEnvelope.profileX Work.OddEnvelope.profileX)
            s t ^ n *
          Real.sqrt (Work.OddCurve.rad (0 : ℝ → ℝ)
            (envProfileFree (0 : ℝ → ℝ) Work.OddEnvelope.profileX Work.OddEnvelope.profileX)
            s t)) =
      ∫ t in (-(Work.OddEnvelope.profileX s))..(Work.OddEnvelope.profileX s),
        (1 - t ^ 2 - (s * t) ^ 2) ^ n * Real.sqrt (1 - t ^ 2 - (s * t) ^ 2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith [Work.OddEnvelope.profileX_pos s])] at ht
    dsimp only
    rw [rad_zero_envProfileFree_profileX_eq hs ht]
  rw [hcongr, show Work.OddEnvelope.profileX s = 1 / Real.sqrt (1 + s ^ 2) from rfl]
  exact (Work.OddCurve.ball_moment_identity n s).1

/-- **The centroid moment of the unperturbed semicircle** (`h = 0`, `x = y = profileX`, free
envelope profile): it vanishes on every genuine slope `s > 0`. -/
theorem momentB_envProfileFree_profileX (n : ℕ) {s : ℝ} (hs : 0 < s) :
    Work.OddCurve.momentB n (0 : ℝ → ℝ) Work.OddEnvelope.profileX Work.OddEnvelope.profileX
        (envProfileFree (0 : ℝ → ℝ) Work.OddEnvelope.profileX Work.OddEnvelope.profileX) s = 0 := by
  rw [Work.OddCurve.momentB_def]
  have hderiv : deriv (0 : ℝ → ℝ) s = 0 := by
    rw [show (0 : ℝ → ℝ) = fun _ : ℝ => 0 from rfl]
    exact deriv_const s 0
  have hcongr :
      (∫ t in (-(Work.OddEnvelope.profileX s))..(Work.OddEnvelope.profileX s),
        Work.OddCurve.rad (0 : ℝ → ℝ)
            (envProfileFree (0 : ℝ → ℝ) Work.OddEnvelope.profileX Work.OddEnvelope.profileX)
            s t ^ (n - 1) *
          Real.sqrt (Work.OddCurve.rad (0 : ℝ → ℝ)
            (envProfileFree (0 : ℝ → ℝ) Work.OddEnvelope.profileX Work.OddEnvelope.profileX)
            s t) *
          (t + deriv (0 : ℝ → ℝ) s)) =
      ∫ t in (-(Work.OddEnvelope.profileX s))..(Work.OddEnvelope.profileX s),
        (1 - t ^ 2 - (s * t) ^ 2) ^ (n - 1) * Real.sqrt (1 - t ^ 2 - (s * t) ^ 2) * t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith [Work.OddEnvelope.profileX_pos s])] at ht
    dsimp only
    rw [rad_zero_envProfileFree_profileX_eq hs ht, hderiv]
    ring
  rw [hcongr, show Work.OddEnvelope.profileX s = 1 / Real.sqrt (1 + s ^ 2) from rfl]
  exact (Work.OddCurve.ball_moment_identity n s).2

theorem semicircleCurveFree (n : ℕ) (hn : 1 ≤ n) :
    Work.OddCurve.Free.IsEnvelopeCurveFree (0 : ℝ → ℝ) Work.OddEnvelope.profileX
        Work.OddEnvelope.profileX ∧
      Work.OddCurve.LowSlope.CloseToProfileX Work.OddEnvelope.profileX ∧
      (∀ s : ℝ, 0 < s → s ≤ 1 →
        Work.OddCurve.momentA n 0 Work.OddEnvelope.profileX Work.OddEnvelope.profileX
          (Work.OddVolterra.Free.envProfileFree 0 Work.OddEnvelope.profileX
            Work.OddEnvelope.profileX) s =
          Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2)) ∧
      (∀ s : ℝ, 0 < s → s ≤ 1 →
        Work.OddCurve.momentB n 0 Work.OddEnvelope.profileX Work.OddEnvelope.profileX
          (Work.OddVolterra.Free.envProfileFree 0 Work.OddEnvelope.profileX
            Work.OddEnvelope.profileX) s = 0) := by
  have _ : 1 ≤ n := hn
  refine ⟨isEnvelopeCurveFree_semicircle, closeToProfileX_profileX, ?_, ?_⟩
  · intro s hs _
    exact momentA_envProfileFree_profileX n hs
  · intro s hs _
    exact momentB_envProfileFree_profileX n hs

end

end Work.OddVolterra.Free
