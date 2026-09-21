import Mathlib
import Submission.Work.OddBridge.Defs
import Submission.Work.OddBridge.isEnvelopeCurve_of_curveData
import Submission.Work.OddBridge.Kden_radicand_pos_of_curve
import Submission.Work.OddBridge.hmid_of_curveData
import Submission.Work.OddVolterra.RowIdentity.odd_rowF
import Submission.Work.OddVolterra.RowIdentity.odd_rowH
import Submission.Work.OddVolterra.Bridge.moment_identities_on_tail

/-!
# The two row identities `(t1)`, `(t2)` for a `CurveData` curve

`Work.OddVolterra.RowIdentity.odd_rowF` and `odd_rowH` are the paper's row identities, proved
under the hypothesis list of `Work.OddVolterra.RowIdentity.Setup`.  This file checks that list
against the data produced by the Volterra construction (`Work.OddVolterra.CurveData`): the
envelope chapter `Work.OddEnvelope` supplies the smoothness of the profile, its two root
conditions and the semicircle on the fixed window `(-X₁, X₁)`; the two positivity packages
(`hKden`, `hmid`) are `Work.OddBridge.Kden_radicand_pos_of_curve` and
`Work.OddBridge.hmid_of_curveData`.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddBridge

open Work.OddVolterra

noncomputable section

/-- A smooth perturbation supported in `[1 - 2τ, 1 - τ]` vanishes on the whole tail
`[1 - τ, ∞)`: off the support window, and at the endpoint by continuity. -/
theorem h_eq_zero_of_tau_le {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    {s : ℝ} (hs : 1 - Work.OddVolterra.tau ≤ s) : h s = 0 := by
  rcases lt_or_eq_of_le hs with hlt | heq
  · by_contra hne
    exact absurd (hsupp hne).2 (not_le.mpr hlt)
  · subst heq
    have hzero : ∀ u : ℝ, 1 - Work.OddVolterra.tau < u → h u = 0 := by
      intro u hu
      by_contra hne
      exact absurd (hsupp hne).2 (not_le.mpr hu)
    have hcont : ContinuousAt h (1 - Work.OddVolterra.tau) := hh.continuous.continuousAt
    have hleft : Filter.Tendsto h (𝓝[Set.Ioi (1 - Work.OddVolterra.tau)]
        (1 - Work.OddVolterra.tau)) (𝓝 (h (1 - Work.OddVolterra.tau))) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hright : Filter.Tendsto h (𝓝[Set.Ioi (1 - Work.OddVolterra.tau)]
        (1 - Work.OddVolterra.tau)) (𝓝 0) := by
      apply Filter.Tendsto.congr'
      · filter_upwards [self_mem_nhdsWithin] with u hu
        exact (hzero u hu).symm
      · exact tendsto_const_nhds
    exact tendsto_nhds_unique hleft hright

/-- `profileX 1 ≤ tStar`: the fixed window of the row identities is contained in the
unperturbed part of the profile. -/
lemma profileX_one_le_tStar : Work.OddEnvelope.profileX 1 ≤ Work.OddEnvelope.tStar := by
  have h := Work.OddEnvelope.profileX_strictAntiOn
    (show (0 : ℝ) < 1 - Work.OddEnvelope.tau by norm_num [Work.OddEnvelope.tau])
    (show (0 : ℝ) < 1 by norm_num)
    (show 1 - Work.OddEnvelope.tau < 1 by norm_num [Work.OddEnvelope.tau])
  exact le_of_lt (by simpa [Work.OddEnvelope.tStar] using h)

/-- **The hypothesis list of the two row identities, read off from a `CurveData` curve.** -/
theorem row_hyps (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hdata : Work.OddVolterra.CurveData n h x y) {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (hc1 : c < 1) :
    (∀ u ∈ Set.Ioc (0 : ℝ) 1,
        Work.OddEnvelope.envelopeProfile h x y (y u) = u * y u + h u ∧
        Work.OddEnvelope.envelopeProfile h x y (-(x u)) = -(u * (-(x u)) + h u)) ∧
      (∀ σ ∈ Set.Ioo a 1, deriv x σ ≤ 0) ∧ (∀ σ ∈ Set.Ioo a 1, deriv y σ ≤ 0) ∧
      (x 1 = Commons.Geometry.Ulam.profileX 1) ∧
      (y 1 = Commons.Geometry.Ulam.profileX 1) ∧
      (∀ t ∈ Set.Icc (-(Commons.Geometry.Ulam.profileX 1))
        (Commons.Geometry.Ulam.profileX 1),
        Work.OddEnvelope.envelopeProfile h x y t = Commons.Geometry.Ulam.semicircle t) ∧
      (∀ s ∈ Set.Icc a 1, x 1 ≤ x s) ∧ (∀ s ∈ Set.Icc a 1, y 1 ≤ y s) ∧
      (-x 1 ≤ y 1) ∧
      (∀ s ∈ Set.Icc a 1, -(x s) ∈ Set.Ioo (-1 : ℝ) 1 ∧ y s ∈ Set.Ioo (-1 : ℝ) 1) ∧
      (∀ s σ : ℝ, a ≤ s → s ≤ σ → σ ≤ 1 →
        0 < (y σ + hquot h s σ) * (line h σ (y σ) + line h s (y σ)) ∧
        0 < (-(x σ) + hquot h s σ) * (line h σ (-(x σ)) + line h s (-(x σ)))) ∧
      (∀ s ∈ Set.Icc a 1,
        ∀ t ∈ Set.Ioo (-(Commons.Geometry.Ulam.profileX 1))
          (Commons.Geometry.Ulam.profileX 1),
        0 < psi h Commons.Geometry.Ulam.semicircle s t) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (Work.OddEnvelope.envelopeProfile h x y)
        (Set.Ioo (-1 : ℝ) 1) := by
  have H : Work.OddEnvelope.IsEnvelopeCurve h x y :=
    Work.OddBridge.isEnvelopeCurve_of_curveData n hh hsupp hdata
  obtain ⟨-, -, -, -, hf_cont, -, -, hroot_r, hroot_l, hint_mem, -, -, -⟩ :=
    Work.OddEnvelope.envelopeProfile_spec H
  have hxchord : Work.OddEnvelope.IsChordCurve x := H.toChordCurve_x
  have hychord : Work.OddEnvelope.IsChordCurve y := H.toChordCurve_y
  have htail : ∀ u : ℝ, 1 - Work.OddVolterra.tau ≤ u → h u = 0 :=
    fun u hu => h_eq_zero_of_tau_le hh hsupp hu
  have hone : (1 : ℝ) - Work.OddVolterra.tau ≤ 1 := by norm_num [Work.OddVolterra.tau]
  refine ⟨fun u hu => ⟨hroot_r u hu.1, hroot_l u hu.1⟩, ?_, ?_, hdata.tail_x 1 hone,
    hdata.tail_y 1 hone, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hf_cont⟩
  · intro σ hσ
    exact le_of_lt (hdata.deriv_x_neg σ (lt_trans ha hσ.1))
  · intro σ hσ
    exact le_of_lt (hdata.deriv_y_neg σ (lt_trans ha hσ.1))
  · intro t ht
    have hpx : Commons.Geometry.Ulam.profileX 1 ≤ Work.OddEnvelope.tStar := by
      have heq : Commons.Geometry.Ulam.profileX 1 = Work.OddEnvelope.profileX 1 := rfl
      rw [heq]
      exact profileX_one_le_tStar
    have ht' : t ∈ Set.Icc (-Work.OddEnvelope.tStar) Work.OddEnvelope.tStar :=
      ⟨le_trans (neg_le_neg hpx) ht.1, le_trans ht.2 hpx⟩
    exact Work.OddVolterra.Bridge.envelopeProfile_eq_semicircle_of_tail hxchord hychord htail ht'
  · intro u hu
    rcases lt_or_eq_of_le hu.2 with hlt | heq
    · exact le_of_lt (hxchord.strictAntiOn (lt_of_lt_of_le ha hu.1) (by norm_num) hlt)
    · rw [heq]
  · intro u hu
    rcases lt_or_eq_of_le hu.2 with hlt | heq
    · exact le_of_lt (hychord.strictAntiOn (lt_of_lt_of_le ha hu.1) (by norm_num) hlt)
    · rw [heq]
  · rw [hdata.tail_x 1 hone, hdata.tail_y 1 hone]
    exact neg_le_self (le_of_lt (Commons.Geometry.Ulam.profileX_pos 1 (by norm_num)))
  · intro u hu
    exact hint_mem u (lt_of_lt_of_le ha hu.1)
  · obtain ⟨hKdenY, hKdenX⟩ := Work.OddBridge.Kden_radicand_pos_of_curve n hh hsupp hdata
    intro s σ hs' hsσ hσ1
    have hs0 : 0 < s := lt_of_lt_of_le ha hs'
    have hσ0 : 0 < σ := lt_of_lt_of_le hs0 hsσ
    exact ⟨hKdenY s σ hs0 hσ0 (le_trans hsσ hσ1) hσ1,
      hKdenX s σ hs0 hσ0 (le_trans hsσ hσ1) hσ1⟩
  · obtain ⟨-, hmidIoc⟩ := Work.OddBridge.hmid_of_curveData n hh hsupp hdata
    intro s hs t ht
    exact hmidIoc s ⟨lt_of_lt_of_le ha hs.1, hs.2⟩ t ht

/-- **The first row identity `(t1)` for a `CurveData` curve.** -/
theorem rowF_of_curveData (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hdata : Work.OddVolterra.CurveData n h x y) :
    Work.OddBridge.RowF n h x y := by
  intro a c ha hac hc1 s hs
  obtain ⟨hxy, hxdec, hydec, hxb, hyb, hfb, hxle, hyle, hord, hint, hKden, hmid, hf⟩ :=
    row_hyps n hn hh hsupp hdata ha hac hc1
  exact Work.OddVolterra.RowIdentity.odd_rowF n hn ha hac hc1 hh hdata.smooth_x hdata.smooth_y
    hf hxy hxdec hydec hxb hyb hfb hxle hyle hord hint hKden hmid hs

/-- **The second row identity `(t2)` for a `CurveData` curve.** -/
theorem rowH_of_curveData (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hdata : Work.OddVolterra.CurveData n h x y) :
    Work.OddBridge.RowH n h x y := by
  intro a c ha hac hc1 s hs
  obtain ⟨hxy, hxdec, hydec, hxb, hyb, hfb, hxle, hyle, hord, hint, hKden, hmid, hf⟩ :=
    row_hyps n hn hh hsupp hdata ha hac hc1
  exact Work.OddVolterra.RowIdentity.odd_rowH n hn ha hac hc1 hh hdata.smooth_x hdata.smooth_y
    hf hxy hxdec hydec hxb hyb hfb hxle hyle hord hint hKden hmid hs

end

end Work.OddBridge
