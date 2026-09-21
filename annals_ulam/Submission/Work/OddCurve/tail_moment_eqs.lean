import Mathlib
import Submission.Work.OddCurve.Defs
import Submission.Work.OddCurve.ball_moment_identity

/-!
# The two moment equations on the semicircle tail `1 - τ < s ≤ 1`

On the slopes beyond the perturbation window the chord curve `(x, y)` is the semicircle's
(`x s = y s = 1/√(1+s²)`, the fields `x_tail`, `y_tail` of `IsEnvelopeCurve`) and the bump `h`
vanishes near `s` (`hz`).  Hence, on the whole section `(-x s, y s)`, which lies inside the
unperturbed part `(-tStar, tStar)` of the profile, the profile is the semicircle
(`Work.OddEnvelope.envelopeProfile_eq_semicircle`) and the radicand of both moment equations
collapses to the ball radicand `1 - t² - (s t)²`.  The two equations are therefore exactly the ball
moment identity `Work.OddCurve.ball_moment_identity` with constant `refConst n`.
-/

namespace Work.OddCurve

noncomputable section

open MeasureTheory Set Filter
open scoped Interval

/-- On the tail the radicand of the moment equations is the ball radicand.  All the content is
the identification of the profile with the semicircle on the section and the vanishing of the
bump there. -/
lemma tail_rad_eq_ball {h x y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hz : ∀ s : ℝ, 1 - tau < s → Filter.EventuallyEq (nhds s) h (fun _ : ℝ => 0))
    {s t : ℝ} (hs : 1 - tau < s)
    (ht : t ∈ Set.Icc (-(Work.OddEnvelope.profileX s)) (Work.OddEnvelope.profileX s)) :
    rad h (Work.OddEnvelope.envelopeProfile h x y) s t = 1 - t ^ 2 - (s * t) ^ 2 := by
  have hpx_pos : 0 < Work.OddEnvelope.profileX s := Work.OddEnvelope.profileX_pos s
  have hs_pos : (0 : ℝ) < s := lt_of_lt_of_le Work.OddEnvelope.one_sub_tau_pos hs.le
  have hpx_lt : Work.OddEnvelope.profileX s < Work.OddEnvelope.tStar := by
    have h := Work.OddEnvelope.profileX_strictAntiOn
      (Work.OddEnvelope.one_sub_tau_pos : (0 : ℝ) < 1 - Work.OddEnvelope.tau) hs_pos hs
    simpa [Work.OddEnvelope.tStar] using h
  have hpx_lt_one : Work.OddEnvelope.profileX s < 1 :=
    lt_trans hpx_lt Work.OddEnvelope.tStar_lt_one
  have ht_abs : |t| ≤ Work.OddEnvelope.profileX s := by
    rw [abs_le]
    exact ⟨by linarith [ht.1], ht.2⟩
  -- the section lies strictly inside the unperturbed part of the profile
  have ht_mem : t ∈ Set.Ioo (-Work.OddEnvelope.tStar) Work.OddEnvelope.tStar :=
    ⟨by linarith [ht_abs, neg_abs_le t],
     by linarith [ht_abs, le_abs_self t, hpx_lt]⟩
  have hf : Work.OddEnvelope.envelopeProfile h x y t = Work.OddEnvelope.semicircle t :=
    Work.OddEnvelope.envelopeProfile_eq_semicircle H ht_mem
  have ht_lt_one : |t| < 1 := lt_of_le_of_lt ht_abs hpx_lt_one
  have ht1 : -1 < t := (abs_lt.mp ht_lt_one).1
  have ht2 : t < 1 := (abs_lt.mp ht_lt_one).2
  have hsq_nonneg : 0 ≤ 1 - t ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr ht2) (by linarith : (0 : ℝ) < 1 + t)]
  have hsemi : Work.OddEnvelope.semicircle t ^ 2 = 1 - t ^ 2 := by
    rw [Work.OddEnvelope.semicircle, Real.sq_sqrt hsq_nonneg]
  have hhs : h s = 0 := (hz s hs).eq_of_nhds
  rw [rad, hf, hsemi, hhs]
  ring

theorem tail_moment_eqs (n : ℕ) {h x y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hz : ∀ s : ℝ, 1 - Work.OddCurve.tau < s →
      Filter.EventuallyEq (nhds s) h (fun _ : ℝ => 0)) :
    Work.OddCurve.MomentEqsOn n (Work.OddCurve.refConst n) h x y
      (Work.OddEnvelope.envelopeProfile h x y) (Set.Ioc (1 - Work.OddCurve.tau) 1) := by
  constructor
  · intro s hs
    obtain ⟨hs1, _hs2⟩ := hs
    have hxs : x s = Work.OddEnvelope.profileX s := H.x_tail s hs1.le
    have hys : y s = Work.OddEnvelope.profileX s := H.y_tail s hs1.le
    rw [momentA_def, hxs, hys]
    have hcongr :
        (∫ t in (-(Work.OddEnvelope.profileX s))..(Work.OddEnvelope.profileX s),
            rad h (Work.OddEnvelope.envelopeProfile h x y) s t ^ n *
              Real.sqrt (rad h (Work.OddEnvelope.envelopeProfile h x y) s t)) =
          ∫ t in (-(Work.OddEnvelope.profileX s))..(Work.OddEnvelope.profileX s),
            (1 - t ^ 2 - (s * t) ^ 2) ^ n * Real.sqrt (1 - t ^ 2 - (s * t) ^ 2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (show -(Work.OddEnvelope.profileX s) ≤ Work.OddEnvelope.profileX s by
        have := Work.OddEnvelope.profileX_pos s
        linarith)] at ht
      dsimp only
      rw [tail_rad_eq_ball H hz hs1 ht]
    rw [hcongr]
    simp only [Work.OddEnvelope.profileX]
    exact (ball_moment_identity n s).1
  · intro s hs
    obtain ⟨hs1, _hs2⟩ := hs
    have hxs : x s = Work.OddEnvelope.profileX s := H.x_tail s hs1.le
    have hys : y s = Work.OddEnvelope.profileX s := H.y_tail s hs1.le
    have hds : deriv h s = 0 := by
      rw [(hz s hs1).deriv_eq, deriv_const]
    rw [momentB_def, hxs, hys, hds]
    have hcongr :
        (∫ t in (-(Work.OddEnvelope.profileX s))..(Work.OddEnvelope.profileX s),
            rad h (Work.OddEnvelope.envelopeProfile h x y) s t ^ (n - 1) *
              Real.sqrt (rad h (Work.OddEnvelope.envelopeProfile h x y) s t) * (t + 0)) =
          ∫ t in (-(Work.OddEnvelope.profileX s))..(Work.OddEnvelope.profileX s),
            (1 - t ^ 2 - (s * t) ^ 2) ^ (n - 1) *
              Real.sqrt (1 - t ^ 2 - (s * t) ^ 2) * t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (show -(Work.OddEnvelope.profileX s) ≤ Work.OddEnvelope.profileX s by
        have := Work.OddEnvelope.profileX_pos s
        linarith)] at ht
      dsimp only
      rw [tail_rad_eq_ball H hz hs1 ht]
      ring
    rw [hcongr]
    simp only [Work.OddEnvelope.profileX]
    exact (ball_moment_identity n s).2

end

end Work.OddCurve
