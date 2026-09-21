import Mathlib
import Submission.Work.OddCurve.Free
import Submission.Work.OddCurve.Tail
import Submission.Work.OddCurve.Defs

/-!
# The two moment equations on all slopes `0 < s ≤ 1`, free tips

`Work.OddCurve.Free.IsEnvelopeCurveFree` differs from `Work.OddEnvelope.IsEnvelopeCurve` by
replacing the two tip normalisations `x s → 1`, `y s → 1` with the mere existence of positive
limits.  The transition-slope input gives the equations on `(0, 1-τ]`; this file adds the tail
`(1-τ, 1]`, where the curve is the semicircle's and the bump vanishes, so that both equations are
the ball's reference identities.

The non-free analogue is `Work.OddCurve.momentEqsOn_Ioc_one_of_smallSlopes`.  Its tail argument
(`Work.OddCurve.tail_moment_eqs`) goes through `Work.OddEnvelope.envelopeProfile_eq_semicircle`,
which uses the normalisation `c s → 1` to make the *inverse* `slopeRight c` well defined on all of
`(0,1)`.  With free tips that global surjectivity is false, but it is not needed: on the
unperturbed part `(-tStar, tStar)` the slope realising a point is produced explicitly by
`Work.OddEnvelope.profileX`, and the branch condition `y s = profileX s` for `s ≥ 1-τ` identifies
the two inverse-function values.  Everything else is copied from the non-free argument.
-/

namespace Work.OddCurve.Free

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

variable {h x y : ℝ → ℝ}

/-! ## Elementary consequences of the free interface -/

lemma IsEnvelopeCurveFree.strictAntiOn_y (H : IsEnvelopeCurveFree h x y) :
    StrictAntiOn y (Set.Ioi 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0) H.smooth_y.continuousOn ?_
  intro s hs
  rw [interior_Ioi] at hs
  exact H.y_deriv_neg s hs

lemma IsEnvelopeCurveFree.strictAntiOn_x (H : IsEnvelopeCurveFree h x y) :
    StrictAntiOn x (Set.Ioi 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0) H.smooth_x.continuousOn ?_
  intro s hs
  rw [interior_Ioi] at hs
  exact H.x_deriv_neg s hs

/-- Beyond the perturbation window the bump vanishes (from the support condition). -/
lemma IsEnvelopeCurveFree.h_eq_zero_of_gt (H : IsEnvelopeCurveFree h x y) {s : ℝ}
    (hs : 1 - Work.OddCurve.tau < s) : h s = 0 := by
  by_contra hne
  exact absurd (H.h_support (Function.mem_support.mpr hne)).2 (not_le.mpr hs)

/-! ## The unperturbed part of the profile is the semicircle -/

/-- On the unperturbed part `(0, tStar)` the slope realising `t` is the semicircle's: there is
`σ > 1 - τ` with `profileX σ = t`.  Explicitly `σ = √(1/t² - 1)`. -/
lemma exists_slope_of_mem_Ioo {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) Work.OddEnvelope.tStar) :
    ∃ σ : ℝ, 1 - Work.OddCurve.tau < σ ∧ Work.OddEnvelope.profileX σ = t := by
  have ht0 : 0 < t := ht.1
  have htts : t < Work.OddEnvelope.tStar := ht.2
  have ht2lt1 : t ^ 2 < 1 := by
    have h := Work.OddEnvelope.tStar_lt_one
    nlinarith [Work.OddEnvelope.tStar_pos]
  have hsub_pos : 0 < 1 / t ^ 2 - 1 := by
    have h1 : 1 < 1 / t ^ 2 := one_lt_one_div (pow_pos ht0 2) ht2lt1
    linarith
  refine ⟨Real.sqrt (1 / t ^ 2 - 1), ?_, ?_⟩
  · rw [Real.lt_sqrt (x := 1 - Work.OddCurve.tau) (y := 1 / t ^ 2 - 1)
      (by norm_num [Work.OddCurve.tau])]
    have hts_sq : 1 / Work.OddEnvelope.tStar ^ 2 = 1 + (1 - Work.OddCurve.tau) ^ 2 := by
      simp only [Work.OddEnvelope.tStar, Work.OddEnvelope.profileX_sq, one_div_one_div]
      norm_num [Work.OddCurve.tau, Work.OddEnvelope.tau]
    have htsq_lt : t ^ 2 < Work.OddEnvelope.tStar ^ 2 :=
      pow_lt_pow_left₀ htts (le_of_lt ht0) (by norm_num : (2 : ℕ) ≠ 0)
    have hrec : 1 / Work.OddEnvelope.tStar ^ 2 < 1 / t ^ 2 :=
      one_div_lt_one_div_of_lt (pow_pos ht0 2) htsq_lt
    linarith
  · have hsq : (Real.sqrt (1 / t ^ 2 - 1)) ^ 2 = 1 / t ^ 2 - 1 := Real.sq_sqrt hsub_pos.le
    have h1 : 1 + (Real.sqrt (1 / t ^ 2 - 1)) ^ 2 = 1 / t ^ 2 := by rw [hsq]; ring
    rw [Work.OddEnvelope.profileX, h1, show (1 : ℝ) / t ^ 2 = (1 / t) ^ 2 by rw [div_pow, one_pow],
      Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 1 / t), one_div_one_div]

/-- On `(0, tStar)` the right branch is the semicircle. -/
lemma envelopeRight_eq_semicircle_free (H : IsEnvelopeCurveFree h x y) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) Work.OddEnvelope.tStar) :
    Work.OddEnvelope.envelopeRight h y t = Work.OddEnvelope.semicircle t := by
  obtain ⟨σ, hσ, hσt⟩ := exists_slope_of_mem_Ioo ht
  have hσpos : 0 < σ := lt_of_lt_of_le (by norm_num [Work.OddCurve.tau]) hσ.le
  have hyσ : y σ = t := by rw [H.y_tail σ hσ.le, hσt]
  have hst : Work.OddEnvelope.slopeRight y t = σ := by
    have h := (H.strictAntiOn_y.injOn).leftInvOn_invFunOn hσpos
    simp only [Work.OddEnvelope.slopeRight, ← hyσ]
    exact h
  rw [Work.OddEnvelope.envelopeRight, hst, H.h_eq_zero_of_gt hσ, add_zero, ← hσt,
    Work.OddEnvelope.mul_profileX_eq_semicircle hσpos]

/-- On `(-tStar, 0)` the left branch is the semicircle. -/
lemma envelopeLeft_eq_semicircle_free (H : IsEnvelopeCurveFree h x y) {t : ℝ}
    (ht : t ∈ Set.Ioo (-Work.OddEnvelope.tStar) 0) :
    Work.OddEnvelope.envelopeLeft h x t = Work.OddEnvelope.semicircle t := by
  have ht' : -t ∈ Set.Ioo (0 : ℝ) Work.OddEnvelope.tStar :=
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  obtain ⟨σ, hσ, hσt⟩ := exists_slope_of_mem_Ioo ht'
  have hσpos : 0 < σ := lt_of_lt_of_le (by norm_num [Work.OddCurve.tau]) hσ.le
  have hxσ : x σ = -t := by rw [H.x_tail σ hσ.le, hσt]
  have hsl : Work.OddEnvelope.slopeLeft x t = σ := by
    have h := (H.strictAntiOn_x.injOn).leftInvOn_invFunOn hσpos
    simp only [Work.OddEnvelope.slopeLeft, ← hxσ]
    exact h
  have hneg : -(σ * t) = σ * (-t) := by ring
  rw [Work.OddEnvelope.envelopeLeft, hsl, H.h_eq_zero_of_gt hσ, add_zero, hneg, ← hσt,
    Work.OddEnvelope.mul_profileX_eq_semicircle hσpos, hσt, Work.OddEnvelope.semicircle_even]

/-- On the unperturbed part `(-tStar, tStar)` the envelope profile is the semicircle. -/
lemma envelopeProfile_eq_semicircle_free (H : IsEnvelopeCurveFree h x y) {t : ℝ}
    (ht : t ∈ Set.Ioo (-Work.OddEnvelope.tStar) Work.OddEnvelope.tStar) :
    Work.OddEnvelope.envelopeProfile h x y t = Work.OddEnvelope.semicircle t := by
  rcases lt_trichotomy t 0 with hneg | heq | hpos
  · have hmem : t ∈ Set.Ioo (-1 : ℝ) 0 :=
      ⟨by linarith [Work.OddEnvelope.tStar_lt_one, ht.1], hneg⟩
    rw [Work.OddEnvelope.envelopeProfile_of_neg hmem]
    exact envelopeLeft_eq_semicircle_free H ⟨ht.1, hneg⟩
  · rw [heq, Work.OddEnvelope.envelopeProfile_zero, Work.OddEnvelope.semicircle]
    norm_num
  · have hmem : t ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨hpos, lt_trans ht.2 Work.OddEnvelope.tStar_lt_one⟩
    rw [Work.OddEnvelope.envelopeProfile_of_pos hmem]
    exact envelopeRight_eq_semicircle_free H ⟨hpos, ht.2⟩

/-- On the tail sections the radicand of the moment equations is the ball radicand. -/
lemma tail_rad_eq_ball_free (H : IsEnvelopeCurveFree h x y) {s t : ℝ}
    (hs : 1 - Work.OddCurve.tau < s)
    (ht : t ∈ Set.Icc (-(Work.OddEnvelope.profileX s)) (Work.OddEnvelope.profileX s)) :
    Work.OddCurve.rad h (Work.OddEnvelope.envelopeProfile h x y) s t = 1 - t ^ 2 - (s * t) ^ 2 := by
  have hs_pos : (0 : ℝ) < s := lt_of_lt_of_le (by norm_num [Work.OddCurve.tau]) hs.le
  have hpx_lt : Work.OddEnvelope.profileX s < Work.OddEnvelope.tStar := by
    have h := Work.OddEnvelope.profileX_strictAntiOn
      (show (0 : ℝ) < 1 - Work.OddEnvelope.tau by norm_num [Work.OddEnvelope.tau]) hs_pos hs
    simpa [Work.OddEnvelope.tStar] using h
  have hpx_lt_one : Work.OddEnvelope.profileX s < 1 :=
    lt_trans hpx_lt Work.OddEnvelope.tStar_lt_one
  have ht_abs : |t| ≤ Work.OddEnvelope.profileX s := by
    rw [abs_le]
    exact ⟨by linarith [ht.1], ht.2⟩
  have ht_mem : t ∈ Set.Ioo (-Work.OddEnvelope.tStar) Work.OddEnvelope.tStar :=
    ⟨by linarith [neg_abs_le t, ht_abs],
     by linarith [le_abs_self t, ht_abs, hpx_lt]⟩
  have hf : Work.OddEnvelope.envelopeProfile h x y t = Work.OddEnvelope.semicircle t :=
    envelopeProfile_eq_semicircle_free H ht_mem
  have ht_lt_one : |t| < 1 := lt_of_le_of_lt ht_abs hpx_lt_one
  have ht2 : t < 1 := (abs_lt.mp ht_lt_one).2
  have hsq_nonneg : 0 ≤ 1 - t ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr ht2) (by linarith [(abs_lt.mp ht_lt_one).1] : (0 : ℝ) < 1 + t)]
  have hsemi : Work.OddEnvelope.semicircle t ^ 2 = 1 - t ^ 2 := by
    rw [Work.OddEnvelope.semicircle, Real.sq_sqrt hsq_nonneg]
  rw [Work.OddCurve.rad, hf, hsemi, H.h_eq_zero_of_gt hs]
  ring

/-! ## The moment equations on the tail -/

theorem tail_moment_eqs_free (n : ℕ) {h x y : ℝ → ℝ}
    (H : IsEnvelopeCurveFree h x y)
    (hz : ∀ s : ℝ, 1 - Work.OddCurve.tau < s →
      Filter.EventuallyEq (nhds s) h (fun _ : ℝ => 0)) :
    Work.OddCurve.MomentEqsOn n (Work.OddCurve.refConst n) h x y
      (Work.OddEnvelope.envelopeProfile h x y) (Set.Ioc (1 - Work.OddCurve.tau) 1) := by
  constructor
  · intro s hs
    obtain ⟨hs1, _hs2⟩ := hs
    have hxs : x s = Work.OddEnvelope.profileX s := H.x_tail s hs1.le
    have hys : y s = Work.OddEnvelope.profileX s := H.y_tail s hs1.le
    rw [Work.OddCurve.momentA_def, hxs, hys]
    have hcongr :
        (∫ t in (-(Work.OddEnvelope.profileX s))..(Work.OddEnvelope.profileX s),
            Work.OddCurve.rad h (Work.OddEnvelope.envelopeProfile h x y) s t ^ n *
              Real.sqrt (Work.OddCurve.rad h (Work.OddEnvelope.envelopeProfile h x y) s t)) =
          ∫ t in (-(Work.OddEnvelope.profileX s))..(Work.OddEnvelope.profileX s),
            (1 - t ^ 2 - (s * t) ^ 2) ^ n * Real.sqrt (1 - t ^ 2 - (s * t) ^ 2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (show -(Work.OddEnvelope.profileX s) ≤ Work.OddEnvelope.profileX s by
        have := Work.OddEnvelope.profileX_pos s
        linarith)] at ht
      dsimp only
      rw [tail_rad_eq_ball_free H hs1 ht]
    rw [hcongr]
    simp only [Work.OddEnvelope.profileX]
    exact (Work.OddCurve.ball_moment_identity n s).1
  · intro s hs
    obtain ⟨hs1, _hs2⟩ := hs
    have hxs : x s = Work.OddEnvelope.profileX s := H.x_tail s hs1.le
    have hys : y s = Work.OddEnvelope.profileX s := H.y_tail s hs1.le
    have hds : deriv h s = 0 := by
      rw [(hz s hs1).deriv_eq, deriv_const]
    rw [Work.OddCurve.momentB_def, hxs, hys, hds]
    have hcongr :
        (∫ t in (-(Work.OddEnvelope.profileX s))..(Work.OddEnvelope.profileX s),
            Work.OddCurve.rad h (Work.OddEnvelope.envelopeProfile h x y) s t ^ (n - 1) *
              Real.sqrt (Work.OddCurve.rad h (Work.OddEnvelope.envelopeProfile h x y) s t) *
              (t + 0)) =
          ∫ t in (-(Work.OddEnvelope.profileX s))..(Work.OddEnvelope.profileX s),
            (1 - t ^ 2 - (s * t) ^ 2) ^ (n - 1) *
              Real.sqrt (1 - t ^ 2 - (s * t) ^ 2) * t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (show -(Work.OddEnvelope.profileX s) ≤ Work.OddEnvelope.profileX s by
        have := Work.OddEnvelope.profileX_pos s
        linarith)] at ht
      dsimp only
      rw [tail_rad_eq_ball_free H hs1 ht]
      ring
    rw [hcongr]
    simp only [Work.OddEnvelope.profileX]
    exact (Work.OddCurve.ball_moment_identity n s).2

/-! ## The two moment equations on `(0,1]` -/

theorem momentEqsOn_Ioc_one_of_smallSlopes_free (n : ℕ) {h x y : ℝ → ℝ}
    (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    (hz : ∀ s : ℝ, 1 - Work.OddCurve.tau < s →
      Filter.EventuallyEq (nhds s) h (fun _ : ℝ => 0))
    (hsmall : Work.OddCurve.SmallSlopeEqs n h x y) :
    Work.OddCurve.MomentEqsOn n (Work.OddCurve.refConst n) h x y
      (Work.OddEnvelope.envelopeProfile h x y) (Set.Ioc 0 1) := by
  obtain ⟨hA, hB⟩ := (Work.OddCurve.smallSlopeEqs_iff n h x y).mp hsmall
  obtain ⟨tA, tB⟩ := tail_moment_eqs_free n H hz
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · by_cases hle : s ≤ 1 - Work.OddCurve.tau
    · exact hA s hs.1 hle
    · exact tA s ⟨lt_of_not_ge hle, hs.2⟩
  · by_cases hle : s ≤ 1 - Work.OddCurve.tau
    · exact hB s hs.1 hle
    · exact tB s ⟨lt_of_not_ge hle, hs.2⟩

end

end Work.OddCurve.Free
