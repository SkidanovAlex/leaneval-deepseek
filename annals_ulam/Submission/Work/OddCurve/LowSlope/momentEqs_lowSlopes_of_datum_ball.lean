import Mathlib
import Submission.Work.OddCurve.LowSlope.cent_inertia_of_datum_ball
import Submission.Work.OddCurve.LowSlope.reduction
import Submission.Work.OddCurve.LowSlope.refConst_eq_inertia

namespace Work.OddCurve.LowSlope

set_option linter.unusedVariables false

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- On the low-slope window `(0, 1-2τ]` the bump vanishes and (being smooth) so does its
derivative: `h` is identically zero on the open interval `(0, 1-2τ)` and `deriv h` is continuous
there, hence `deriv h (1-2τ) = 0` as well. -/
lemma deriv_eq_zero_of_hzero (h : ℝ → ℝ) (H : ContDiffOn ℝ ∞ h (Set.Ioi 0))
    (hzero : ∀ s : ℝ, 0 < s → s ≤ 1 - 2 * Work.OddEnvelope.tau → h s = 0) :
    ∀ s : ℝ, 0 < s → s ≤ 1 - 2 * Work.OddEnvelope.tau → deriv h s = 0 := by
  set c : ℝ := 1 - 2 * Work.OddEnvelope.tau with hc
  have hc0 : (0 : ℝ) < c := by rw [hc]; norm_num [Work.OddEnvelope.tau]
  have hzeroOn : Set.EqOn (deriv h) (fun _ : ℝ => (0 : ℝ)) (Set.Ioo (0 : ℝ) c) := by
    intro u hu
    have hz : h =ᶠ[𝓝 u] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
      exact hzero v hv.1 (by rw [hc]; exact le_of_lt hv.2)
    simpa using hz.deriv_eq
  have hcont : ContinuousOn (deriv h) (Set.Ioi (0 : ℝ)) :=
    H.continuousOn_deriv_of_isOpen isOpen_Ioi (by simp)
  intro s hs hsle
  rcases lt_or_eq_of_le hsle with hlt | heq
  · exact hzeroOn ⟨hs, hlt⟩
  · rw [heq]
    have hmem : c ∈ Set.Ioi (0 : ℝ) := hc0
    have hca : ContinuousAt (deriv h) c :=
      (hcont c hmem).continuousAt (isOpen_Ioi.mem_nhds hmem)
    have hev : (deriv h) =ᶠ[𝓝[<] c] (fun _ : ℝ => (0 : ℝ)) := by
      show ∀ᶠ u in 𝓝[<] c, deriv h u = (0 : ℝ)
      rw [eventually_nhdsWithin_iff]
      filter_upwards [isOpen_Ioi.mem_nhds hc0] with u hu
      intro huc
      exact hzeroOn ⟨hu, huc⟩
    have h1 : Tendsto (deriv h) (𝓝[<] c) (𝓝 (deriv h c)) :=
      hca.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (deriv h) (𝓝[<] c) (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds.congr' hev.symm
    exact tendsto_nhds_unique h1 h2

theorem momentEqs_lowSlopes_of_datum_ball (n : ℕ) (hn : 1 ≤ n) {h x y ρ : ℝ → ℝ} {b : ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hb0 : 0 < b) (hb1 : b ≤ 1 - 2 * Work.OddEnvelope.tau)
    (hzero : ∀ s : ℝ, 0 < s → s ≤ 1 - 2 * Work.OddEnvelope.tau → h s = 0)
    (hρpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hρsm : ContDiffOn ℝ 1 ρ (Set.Ioo (-1 : ℝ) 1))
    (hρmono : StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1))
    (hgraph : ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
      ρ u * Real.sqrt (1 - u ^ 2) = Work.OddEnvelope.envelopeProfile h x y (ρ u * u))
    (hball : ∀ c : ℝ, (Real.sqrt (1 + (1 - 2 * Work.OddEnvelope.tau) ^ 2))⁻¹ ≤ c → c < 1 →
      Work.OddCurve.LowSlope.radonPhi n ρ c = Work.OddCurve.LowSlope.ballPhiData n c ∧
        Work.OddCurve.LowSlope.radonPsi n ρ c = 0)
    (hval : Work.OddCurve.momentA n h x y (Work.OddEnvelope.envelopeProfile h x y) b =
      Work.OddCurve.refConst n / Real.sqrt (1 + b ^ 2)) :
    (∀ s : ℝ, 0 < s → s ≤ b →
      Work.OddCurve.momentA n h x y (Work.OddEnvelope.envelopeProfile h x y) s =
        Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2)) ∧
    (∀ s : ℝ, 0 < s → s ≤ b →
      Work.OddCurve.momentB n h x y (Work.OddEnvelope.envelopeProfile h x y) s = 0) := by
  have hder0 := deriv_eq_zero_of_hzero h H.smooth_h hzero
  have hci := Work.OddCurve.LowSlope.cent_inertia_of_datum_ball n hn H hzero hρpos hρsm hρmono
    hgraph hball
  have hval' : Work.OddCurve.momentA n h x y (Work.OddEnvelope.envelopeProfile h x y) b =
      ((2 * (n : ℝ) + 1) * Work.OddCurve.LowSlope.ballInertiaConst n) /
        Real.sqrt (1 + b ^ 2) := by
    rw [hval, Work.OddCurve.LowSlope.refConst_eq_inertia n hn]
  constructor
  · intro s hs hsle
    obtain ⟨hA, -⟩ := Work.OddCurve.LowSlope.lowSlope_momentEqs n hn H (a := s) (b := b)
      hs hsle
      (fun u hu => hzero u (lt_of_lt_of_le hs hu.1) (le_trans hu.2 hb1))
      (fun u hu => hder0 u (lt_of_lt_of_le hs hu.1) (le_trans hu.2 hb1))
      (fun u hu => (hci u (lt_of_lt_of_le hs hu.1) (le_trans hu.2 hb1)).1)
      (fun u hu => (hci u (lt_of_lt_of_le hs hu.1) (le_trans hu.2 hb1)).2)
      hval'
    have h := hA s ⟨le_refl s, hsle⟩
    rw [Work.OddCurve.LowSlope.refConst_eq_inertia n hn]
    exact h
  · intro s hs hsle
    obtain ⟨-, hB⟩ := Work.OddCurve.LowSlope.lowSlope_momentEqs n hn H (a := s) (b := b)
      hs hsle
      (fun u hu => hzero u (lt_of_lt_of_le hs hu.1) (le_trans hu.2 hb1))
      (fun u hu => hder0 u (lt_of_lt_of_le hs hu.1) (le_trans hu.2 hb1))
      (fun u hu => (hci u (lt_of_lt_of_le hs hu.1) (le_trans hu.2 hb1)).1)
      (fun u hu => (hci u (lt_of_lt_of_le hs hu.1) (le_trans hu.2 hb1)).2)
      hval'
    exact hB s ⟨le_refl s, hsle⟩

end Work.OddCurve.LowSlope
