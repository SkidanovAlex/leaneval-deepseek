import Mathlib
import Submission.Work.OddCurve.Defs
import Submission.Work.OddCurve.ball_moment_identity
import Submission.Work.Odd.profile_eq_semicircle_of_roots

/-!
# The constant of the transition-slope equations is the ball's constant

`Work.OddCurve.const_eq_refConst_of_smallSlope`: if `(h,x,y)` is an envelope curve whose bump is
supported in the *open* window `(1-2τ, 1-τ)` and the two moment equations hold on the transition
slopes `0 < s ≤ 1-τ` with constant `C`, then `C = refConst n`.

The reason is that at the last transition slope `s = 1-τ` the section is the unperturbed one
(`x s = y s = profileX s = tStar`), the bump vanishes there (support in the *open* window), and
the profile coincides with the semicircle on the whole section `[-tStar, tStar]`.  Hence `(A)` at
`s = 1-τ` *is* the ball identity `Work.OddCurve.ball_moment_identity` at `s = 1-τ`, and the
common factor `√(1+s²)` cancels.
-/

namespace Work.OddCurve

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- The semicircle profile is continuous. -/
lemma continuousOn_semicircle_Icc :
    ContinuousOn Work.OddEnvelope.semicircle (Set.Icc (-1 : ℝ) 1) :=
  (Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2))).continuousOn

/-- **The profile is the semicircle on the whole section of a tail slope.**  For `0 < a ≤ tStar`
the envelope profile agrees with the semicircle on the closed interval `[-a, a]`:  the agreement
is known on the open interval (`Work.OddEnvelope.envelopeProfile_eq_semicircle`) and both
functions are continuous, so it extends to the closure. -/
lemma envelopeProfile_eq_semicircle_Icc_tStar {h x y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y) {a : ℝ} (ha0 : 0 < a)
    (ha : a ≤ Work.OddEnvelope.tStar) :
    ∀ t ∈ Set.Icc (-a) a,
      Work.OddEnvelope.envelopeProfile h x y t = Work.OddEnvelope.semicircle t := by
  have hstar_lt_one : Work.OddEnvelope.tStar < 1 := Work.OddEnvelope.tStar_lt_one
  have hcont : ContinuousOn
      (fun t : ℝ => Work.OddEnvelope.envelopeProfile h x y t - Work.OddEnvelope.semicircle t)
      (Set.Icc (-1 : ℝ) 1) :=
    (Work.OddEnvelope.continuousOn_envelopeProfile' H).sub continuousOn_semicircle_Icc
  have hclosed : IsClosed (Set.Icc (-1 : ℝ) 1 ∩
      (fun t : ℝ => Work.OddEnvelope.envelopeProfile h x y t -
        Work.OddEnvelope.semicircle t) ⁻¹' {0}) :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hsub : Set.Ioo (-a) a ⊆ Set.Icc (-1 : ℝ) 1 ∩
      (fun t : ℝ => Work.OddEnvelope.envelopeProfile h x y t -
        Work.OddEnvelope.semicircle t) ⁻¹' {0} := by
    intro t ht
    have ha_lt_one : a < 1 := lt_of_le_of_lt ha hstar_lt_one
    have ht1 : -1 < t := by linarith [ht.1, ha_lt_one]
    have ht2 : t < 1 := by linarith [ht.2, ha_lt_one]
    have hmem : t ∈ Set.Ioo (-Work.OddEnvelope.tStar) Work.OddEnvelope.tStar :=
      ⟨by linarith [ht.1, ha], by linarith [ht.2, ha]⟩
    refine ⟨⟨le_of_lt ht1, le_of_lt ht2⟩, ?_⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [Work.OddEnvelope.envelopeProfile_eq_semicircle H hmem, sub_self]
  have hIcc : Set.Icc (-a) a ⊆ Set.Icc (-1 : ℝ) 1 ∩
      (fun t : ℝ => Work.OddEnvelope.envelopeProfile h x y t -
        Work.OddEnvelope.semicircle t) ⁻¹' {0} := by
    have hcl : closure (Set.Ioo (-a) a) = Set.Icc (-a) a :=
      closure_Ioo (by linarith : -a ≠ a)
    rw [← hcl]
    exact hclosed.closure_subset_iff.mpr hsub
  intro t ht
  exact sub_eq_zero.mp (hIcc ht).2

/-- **The volume moment at a tail slope.**  If `s ≥ 1 - τ`, `s > 0` and the bump vanishes at
`s`, then the volume moment `(A)` of the envelope curve at slope `s` equals the ball's value
`refConst n / √(1+s²)`.  Only the interval endpoint `s = 1-τ` is used below; the general form is
convenient because it makes no use of the open window beyond `h s = 0`. -/
lemma momentA_eq_refConst_of_ge_tail (n : ℕ) {h x y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y) {s : ℝ}
    (hs0 : 0 < s) (hs : 1 - tau ≤ s) (hh : h s = 0) :
    momentA n h x y (Work.OddEnvelope.envelopeProfile h x y) s =
      refConst n / Real.sqrt (1 + s ^ 2) := by
  have hxs : x s = Work.OddEnvelope.profileX s := H.x_tail s hs
  have hys : y s = Work.OddEnvelope.profileX s := H.y_tail s hs
  have hp_pos : 0 < Work.OddEnvelope.profileX s := Work.OddEnvelope.profileX_pos s
  have hp_le : Work.OddEnvelope.profileX s ≤ Work.OddEnvelope.tStar := by
    have h1tau : (1 - Work.OddEnvelope.tau) ∈ Set.Ioi (0 : ℝ) := by
      rw [← Work.OddCurve.tau_eq]
      norm_num [Work.OddEnvelope.tau, Work.OddCurve.tau]
    have hs' : 1 - Work.OddEnvelope.tau ≤ s := by
      rw [← Work.OddCurve.tau_eq]
      exact hs
    exact Work.OddEnvelope.profileX_strictAntiOn.antitoneOn h1tau hs0 hs'
  have hf : ∀ t ∈ Set.Icc (-(Work.OddEnvelope.profileX s)) (Work.OddEnvelope.profileX s),
      Work.OddEnvelope.envelopeProfile h x y t = Work.OddEnvelope.semicircle t :=
    envelopeProfile_eq_semicircle_Icc_tStar H hp_pos hp_le
  -- the radicand is the ball's radicand on the whole section
  have hrad : ∀ t ∈ Set.Icc (-(Work.OddEnvelope.profileX s)) (Work.OddEnvelope.profileX s),
      rad h (Work.OddEnvelope.envelopeProfile h x y) s t = 1 - t ^ 2 - (s * t) ^ 2 := by
    intro t ht
    have habs : |t| ≤ Work.OddEnvelope.profileX s := by
      rw [abs_le]
      exact ⟨by linarith [ht.1], ht.2⟩
    have hlt : |t| < 1 := lt_of_le_of_lt habs (Work.OddEnvelope.profileX_lt_one hs0)
    have hnl : 0 ≤ 1 - t ^ 2 := by
      have h1 : -1 < t := (abs_lt.mp hlt).1
      have h2 : t < 1 := (abs_lt.mp hlt).2
      nlinarith
    have hsq : Work.OddEnvelope.semicircle t ^ 2 = 1 - t ^ 2 := by
      rw [Work.OddEnvelope.semicircle]
      exact Real.sq_sqrt hnl
    rw [rad, hf t ht, hsq, hh, add_zero]
  -- the two integrands agree pointwise on the section
  have hcongr :
      (∫ t in (-(Work.OddEnvelope.profileX s))..(Work.OddEnvelope.profileX s),
          rad h (Work.OddEnvelope.envelopeProfile h x y) s t ^ n *
            Real.sqrt (rad h (Work.OddEnvelope.envelopeProfile h x y) s t)) =
        ∫ t in (-(Work.OddEnvelope.profileX s))..(Work.OddEnvelope.profileX s),
          (1 - t ^ 2 - (s * t) ^ 2) ^ n * Real.sqrt (1 - t ^ 2 - (s * t) ^ 2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith [hp_pos])] at ht
    dsimp only
    rw [hrad t ht]
  have h1 : momentA n h x y (Work.OddEnvelope.envelopeProfile h x y) s =
      ∫ t in (-(Work.OddEnvelope.profileX s))..(Work.OddEnvelope.profileX s),
        rad h (Work.OddEnvelope.envelopeProfile h x y) s t ^ n *
          Real.sqrt (rad h (Work.OddEnvelope.envelopeProfile h x y) s t) := by
    rw [momentA_def, hxs, hys]
  rw [h1, hcongr]
  simp only [Work.OddEnvelope.profileX]
  exact (ball_moment_identity n s).1

/-- **The constant of the transition-slope moment equations is the ball's constant.**  At the last
transition slope `s = 1-τ` the section is the unperturbed one, the bump vanishes there, and the
profile is the semicircle on the whole section; hence `(A)` at `s = 1-τ` is the ball identity and
the common factor `√(1+s²)` cancels. -/
theorem const_eq_refConst_of_smallSlope (n : ℕ) {C : ℝ} {h x y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hsupp : Function.support h ⊆ Set.Ioo (1 - 2 * Work.OddCurve.tau) (1 - Work.OddCurve.tau))
    (hEq : Work.OddCurve.SmallSlopeEqsC n C h x y) :
    C = Work.OddCurve.refConst n := by
  have htau_lt : Work.OddCurve.tau < 1 := by norm_num [tau]
  have hh0 : h (1 - tau) = 0 := by
    by_contra hne
    have hmem := hsupp (by simpa [Function.mem_support] using hne)
    exact absurd hmem.2 (lt_irrefl _)
  have hA : momentA n h x y (Work.OddEnvelope.envelopeProfile h x y) (1 - tau) =
      C / Real.sqrt (1 + (1 - tau) ^ 2) :=
    hEq.1 (1 - tau) ⟨by linarith, le_rfl⟩
  have hkey := momentA_eq_refConst_of_ge_tail n H (by linarith : (0 : ℝ) < 1 - tau) le_rfl hh0
  have hxC : C / Real.sqrt (1 + (1 - tau) ^ 2) =
      refConst n / Real.sqrt (1 + (1 - tau) ^ 2) := by
    rw [← hA, hkey]
  have hne : Real.sqrt (1 + (1 - tau) ^ 2) ≠ 0 := by positivity
  have hmul : C / Real.sqrt (1 + (1 - tau) ^ 2) * Real.sqrt (1 + (1 - tau) ^ 2) =
      refConst n / Real.sqrt (1 + (1 - tau) ^ 2) * Real.sqrt (1 + (1 - tau) ^ 2) := by
    rw [hxC]
  rw [div_mul_cancel₀ C hne, div_mul_cancel₀ (refConst n) hne] at hmul
  exact hmul

end

end Work.OddCurve
