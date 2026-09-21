import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Ball
import Submission.Work.OddVolterra.Assembly
import Submission.Work.OddEnvelope.Main
import Submission.Work.OddEnvelope.Profile

/-!
# The two moment identities on the unperturbed tail `[1 - τ, 1]`

On the tail of the slope window the perturbation `h` vanishes identically
(`htail`), and the chord-endpoint curve `(x, y)` of the Volterra construction
agrees there with the semicircle chord function `profileX`
(`CurveData.tail_x`, `CurveData.tail_y`).  Hence, on the tail, the envelope
profile is the semicircle and the two moment integrals are those of the ball,
so the identities hold with the ball constant
`Commons.Geometry.Ulam.oddSemicircleMomentConstant n`.

The file proves this from the ball identities `ball_momentF`, `ball_momentH`
together with two facts about the tail:

* `envelopeProfile_eq_semicircle_of_tail` : on `[-tStar, tStar]` the envelope
  profile is the semicircle (this only uses that the curve is a chord curve and
  that `h` vanishes on the tail);
* `deriv_eq_zero_of_eq_zero_on_Ici` : a function differentiable at a point and
  vanishing on a right neighbourhood of it has zero derivative there (needed
  because the centroid integrand carries the factor `∂_s L = t + h'(s)`).
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.Bridge

noncomputable section

/-! ### A derivative vanishing on a half-line -/

/-- If a function differentiable at `a` vanishes on `[a, ∞)`, then its derivative
at `a` vanishes: the right difference quotients are all `0`, and the two-sided
derivative is their limit. -/
theorem deriv_eq_zero_of_eq_zero_on_Ici {h : ℝ → ℝ} {a : ℝ} (hd : DifferentiableAt ℝ h a)
    (hz : ∀ s : ℝ, a ≤ s → h s = 0) : deriv h a = 0 := by
  have hsub : Set.Ioi a ⊆ ({a}ᶜ : Set ℝ) := fun x hx => by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt hx
  have h1 : Tendsto (slope h a) (𝓝[Set.Ioi a] a) (𝓝 (deriv h a)) :=
    (hd.hasDerivAt.tendsto_slope).mono_left (nhdsWithin_mono a hsub)
  have h2 : Tendsto (slope h a) (𝓝[Set.Ioi a] a) (𝓝 (0 : ℝ)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [slope, hz x (le_of_lt hx), hz a le_rfl]
    simp
  exact tendsto_nhds_unique h1 h2

/-! ### The two branches of the envelope on the tail -/

/-- On the tail the right branch of the envelope is the semicircle.  Only the
vanishing of `h` on `[1 - τ, ∞)` and the chord-curve properties of `c` are
used (not the monotonicity/shape conditions of `IsEnvelopeBranch`). -/
theorem envelopeRight_eq_semicircle_of_tail {h c : ℝ → ℝ}
    (hc : Work.OddEnvelope.IsChordCurve c) (hh : ∀ s : ℝ, 1 - tau ≤ s → h s = 0)
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) Work.OddEnvelope.tStar) :
    Work.OddEnvelope.envelopeRight h c t = Work.OddEnvelope.semicircle t := by
  set σ := Work.OddEnvelope.slopeRight c t with hσdef
  have ht_lt_one : t < 1 := lt_of_le_of_lt ht.2 Work.OddEnvelope.tStar_lt_one
  have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨ht.1, ht_lt_one⟩
  have hσpos : 0 < σ := by
    rw [hσdef]; exact Work.OddEnvelope.IsChordCurve.slopeRight_pos hc ht'
  have hcσ : c σ = t := by
    rw [hσdef]; exact Work.OddEnvelope.IsChordCurve.slopeRight_eq hc ht'
  have hσge : 1 - tau ≤ σ := by
    rcases lt_trichotomy σ (1 - tau) with hlt | heq | hgt
    · exfalso
      have h2 : c (1 - tau) < c σ :=
        Work.OddEnvelope.IsChordCurve.strictAntiOn hc hσpos Work.OddEnvelope.one_sub_tau_pos hlt
      rw [Work.OddEnvelope.IsChordCurve.tail hc (1 - tau) le_rfl, hcσ] at h2
      exact absurd h2 (not_lt.mpr ht.2)
    · exact heq.ge
    · exact hgt.le
  have hp0 : h σ = 0 := hh σ hσge
  have hcx : c σ = Work.OddEnvelope.profileX σ :=
    Work.OddEnvelope.IsChordCurve.tail hc σ hσge
  have ht_eq : t = Work.OddEnvelope.profileX σ := by rw [← hcσ, hcx]
  calc Work.OddEnvelope.envelopeRight h c t
      = Work.OddEnvelope.slopeRight c t * t + h (Work.OddEnvelope.slopeRight c t) := rfl
    _ = σ * t + h σ := by rw [hσdef]
    _ = σ * t := by rw [hp0, add_zero]
    _ = σ * Work.OddEnvelope.profileX σ := by rw [ht_eq]
    _ = Work.OddEnvelope.semicircle (Work.OddEnvelope.profileX σ) :=
        Work.OddEnvelope.mul_profileX_eq_semicircle hσpos
    _ = Work.OddEnvelope.semicircle t := by rw [ht_eq]

/-- On the tail the left branch of the envelope is the semicircle. -/
theorem envelopeLeft_eq_semicircle_of_tail {h c : ℝ → ℝ}
    (hc : Work.OddEnvelope.IsChordCurve c) (hh : ∀ s : ℝ, 1 - tau ≤ s → h s = 0)
    {t : ℝ} (ht : t ∈ Set.Ico (-Work.OddEnvelope.tStar) 0) :
    Work.OddEnvelope.envelopeLeft h c t = Work.OddEnvelope.semicircle t := by
  have ht' : -t ∈ Set.Ioc (0 : ℝ) Work.OddEnvelope.tStar :=
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have h := envelopeRight_eq_semicircle_of_tail (h := Work.OddEnvelope.negH h) (c := c) hc
    (fun s hs => by simp only [Work.OddEnvelope.negH, hh s hs, neg_zero]) ht'
  rw [Work.OddEnvelope.envelopeLeft_eq_negH, h, Work.OddEnvelope.semicircle_even]

/-- On the unperturbed part `[-tStar, tStar]` the envelope profile is the semicircle. -/
theorem envelopeProfile_eq_semicircle_of_tail {h x y : ℝ → ℝ}
    (hx : Work.OddEnvelope.IsChordCurve x) (hy : Work.OddEnvelope.IsChordCurve y)
    (hh : ∀ s : ℝ, 1 - tau ≤ s → h s = 0) {t : ℝ}
    (ht : t ∈ Set.Icc (-Work.OddEnvelope.tStar) Work.OddEnvelope.tStar) :
    Work.OddEnvelope.envelopeProfile h x y t = Work.OddEnvelope.semicircle t := by
  rcases lt_trichotomy t 0 with hneg | heq | hpos
  · have ht' : t ∈ Set.Ioo (-1 : ℝ) 0 :=
      ⟨by linarith [ht.1, Work.OddEnvelope.tStar_lt_one], hneg⟩
    rw [Work.OddEnvelope.envelopeProfile_of_neg ht']
    exact envelopeLeft_eq_semicircle_of_tail hx hh ⟨ht.1, hneg⟩
  · rw [heq, Work.OddEnvelope.envelopeProfile_zero]
    simp [Work.OddEnvelope.semicircle]
  · have ht' : t ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨hpos, by linarith [ht.2, Work.OddEnvelope.tStar_lt_one]⟩
    rw [Work.OddEnvelope.envelopeProfile_of_pos ht']
    exact envelopeRight_eq_semicircle_of_tail hy hh ⟨hpos, ht.2⟩

/-! ### The moment identities on the tail -/

theorem moment_identities_on_tail (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hdata : Work.OddVolterra.CurveData n h x y)
    (htail : ∀ s : ℝ, 1 - Work.OddVolterra.tau ≤ s → h s = 0) :
    ∀ s ∈ Set.Icc (1 - Work.OddVolterra.tau) 1,
      Work.OddVolterra.momentF n h x y (Work.OddEnvelope.envelopeProfile h x y) s
          = Work.OddVolterra.momentRHS n s ∧
      Work.OddVolterra.momentH n h x y (Work.OddEnvelope.envelopeProfile h x y) s = 0 := by
  intro s hs
  obtain ⟨hs1, hs2⟩ := hs
  have hx : Work.OddEnvelope.IsChordCurve x :=
    ⟨hdata.smooth_x, hdata.deriv_x_neg, hdata.tendsto_x, hdata.tail_x⟩
  have hy : Work.OddEnvelope.IsChordCurve y :=
    ⟨hdata.smooth_y, hdata.deriv_y_neg, hdata.tendsto_y, hdata.tail_y⟩
  have hspos : 0 < s := lt_of_lt_of_le Work.OddEnvelope.one_sub_tau_pos hs1
  have hxs : x s = Work.OddEnvelope.profileX s := hdata.tail_x s hs1
  have hys : y s = Work.OddEnvelope.profileX s := hdata.tail_y s hs1
  have hhs : h s = 0 := htail s hs1
  have hle : -(Work.OddEnvelope.profileX s) ≤ Work.OddEnvelope.profileX s := by
    linarith [Work.OddEnvelope.profileX_pos s]
  have hc_le : Work.OddEnvelope.profileX s ≤ Work.OddEnvelope.tStar :=
    Work.OddEnvelope.profileX_strictAntiOn.antitoneOn Work.OddEnvelope.one_sub_tau_pos hspos hs1
  have hInt : ∀ t ∈ Set.Icc (-(Work.OddEnvelope.profileX s)) (Work.OddEnvelope.profileX s),
      Work.OddEnvelope.envelopeProfile h x y t = Work.OddEnvelope.semicircle t := by
    intro t ht
    exact envelopeProfile_eq_semicircle_of_tail hx hy htail
      ⟨by linarith [ht.1, hc_le], by linarith [ht.2, hc_le]⟩
  have hpsi : ∀ t ∈ Set.Icc (-(Work.OddEnvelope.profileX s)) (Work.OddEnvelope.profileX s),
      psi h (Work.OddEnvelope.envelopeProfile h x y) s t
        = psi (fun _ : ℝ => 0) Work.OddEnvelope.semicircle s t := by
    intro t ht
    show (Work.OddEnvelope.envelopeProfile h x y t) ^ 2 - (s * t + h s) ^ 2
        = (Work.OddEnvelope.semicircle t) ^ 2 - (s * t + 0) ^ 2
    rw [hInt t ht, hhs]
  have hderivh : deriv h s = 0 :=
    deriv_eq_zero_of_eq_zero_on_Ici ((hh.differentiable (by simp)).differentiableAt)
      (fun t ht => htail t (le_trans hs1 ht))
  have hF : momentF n h x y (Work.OddEnvelope.envelopeProfile h x y) s
      = momentF n (fun _ : ℝ => 0) Work.OddEnvelope.profileX Work.OddEnvelope.profileX
          Work.OddEnvelope.semicircle s := by
    unfold momentF momentIntegrand
    rw [hxs, hys]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hle] at ht
    beta_reduce
    rw [hpsi t ht]
  have hH : momentH n h x y (Work.OddEnvelope.envelopeProfile h x y) s
      = momentH n (fun _ : ℝ => 0) Work.OddEnvelope.profileX Work.OddEnvelope.profileX
          Work.OddEnvelope.semicircle s := by
    unfold momentH centroidIntegrand lineSlope
    rw [hxs, hys]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hle] at ht
    beta_reduce
    simp only [hpsi t ht, hderivh, deriv_const, add_zero]
  exact ⟨by rw [hF]; exact ball_momentF n hspos,
    by rw [hH]; exact ball_momentH n hspos⟩

end

end Work.OddVolterra.Bridge
