import Mathlib
import Submission.Work.OddVolterra.Free.Defs
import Submission.Work.OddCurve.Free
import Submission.Work.OddCurve.LowSlope.momentEqs_lowSlopes_of_datum_ball
import Submission.Work.OddVolterra.Free.lowSlope_momentEqs_free
import Submission.Work.OddVolterra.Free.cent_inertia_of_datum_ball_free

namespace Work.OddVolterra.Free

theorem lowSlopesDatumFree (n : ℕ) (hn : 1 ≤ n) {h x y ρ : ℝ → ℝ} {b : ℝ}
    (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    (hb0 : 0 < b) (hb1 : b ≤ 1 - 2 * Work.OddEnvelope.tau)
    (hzero : ∀ s : ℝ, 0 < s → s ≤ 1 - 2 * Work.OddEnvelope.tau → h s = 0)
    (hρpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hρsm : ContDiffOn ℝ 1 ρ (Set.Ioo (-1 : ℝ) 1))
    (hρmono : StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1))
    (hgraph : ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
      ρ u * Real.sqrt (1 - u ^ 2) = Work.OddVolterra.Free.envProfileFree h x y (ρ u * u))
    (hball : ∀ c : ℝ, (Real.sqrt (1 + (1 - 2 * Work.OddEnvelope.tau) ^ 2))⁻¹ ≤ c → c < 1 →
      Work.OddCurve.LowSlope.radonPhi n ρ c = Work.OddCurve.LowSlope.ballPhiData n c ∧
        Work.OddCurve.LowSlope.radonPsi n ρ c = 0)
    (hval : Work.OddCurve.momentA n h x y (Work.OddVolterra.Free.envProfileFree h x y) b =
      Work.OddCurve.refConst n / Real.sqrt (1 + b ^ 2)) :
    (∀ s : ℝ, 0 < s → s ≤ b →
      Work.OddCurve.momentA n h x y (Work.OddVolterra.Free.envProfileFree h x y) s =
        Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2)) ∧
    (∀ s : ℝ, 0 < s → s ≤ b →
      Work.OddCurve.momentB n h x y (Work.OddVolterra.Free.envProfileFree h x y) s = 0) := by
  -- The bump and its derivative vanish on the whole low-slope window `(0, 1-2τ]`.
  have hder0 := Work.OddCurve.LowSlope.deriv_eq_zero_of_hzero h H.smooth_h hzero
  -- The ball's Radon datum gives the centroid and inertia conditions on the low slopes.
  have hci := cent_inertia_of_datum_ball_free n hn H hzero hρpos hρsm hρmono hgraph hball
  -- The single input at the slope `b`, in the `ballInertiaConst` normalisation.
  have hval' : Work.OddCurve.momentA n h x y (envProfileFree h x y) b =
      ((2 * (n : ℝ) + 1) * Work.OddCurve.LowSlope.ballInertiaConst n) /
        Real.sqrt (1 + b ^ 2) := by
    rw [hval, Work.OddCurve.LowSlope.refConst_eq_inertia n hn]
  constructor
  · intro s hs hsle
    obtain ⟨hA, -⟩ := lowSlope_momentEqs_free n hn H (a := s) (b := b) hs hsle
      (fun u hu => hzero u (lt_of_lt_of_le hs hu.1) (le_trans hu.2 hb1))
      (fun u hu => hder0 u (lt_of_lt_of_le hs hu.1) (le_trans hu.2 hb1))
      (fun u hu => (hci u (lt_of_lt_of_le hs hu.1) (le_trans hu.2 hb1)).1)
      (fun u hu => (hci u (lt_of_lt_of_le hs hu.1) (le_trans hu.2 hb1)).2)
      hval'
    have h := hA s ⟨le_refl s, hsle⟩
    rw [Work.OddCurve.LowSlope.refConst_eq_inertia n hn]
    exact h
  · intro s hs hsle
    obtain ⟨-, hB⟩ := lowSlope_momentEqs_free n hn H (a := s) (b := b) hs hsle
      (fun u hu => hzero u (lt_of_lt_of_le hs hu.1) (le_trans hu.2 hb1))
      (fun u hu => hder0 u (lt_of_lt_of_le hs hu.1) (le_trans hu.2 hb1))
      (fun u hu => (hci u (lt_of_lt_of_le hs hu.1) (le_trans hu.2 hb1)).1)
      (fun u hu => (hci u (lt_of_lt_of_le hs hu.1) (le_trans hu.2 hb1)).2)
      hval'
    exact hB s ⟨le_refl s, hsle⟩

end Work.OddVolterra.Free
