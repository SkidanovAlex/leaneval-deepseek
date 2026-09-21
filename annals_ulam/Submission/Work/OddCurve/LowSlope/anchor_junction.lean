import Mathlib
import Submission.Work.OddCurve.LowSlope.cl1_forward
import Submission.Work.OddCurve.LowSlope.reduction
import Submission.Work.OddCurve.LowSlope.radonProfile_data_semicircle
import Submission.Work.OddCurve.LowSlope.refConst_eq_inertia

/-!
# The junction identity of Step 3 (paper Ryabogin, odd case)

On the *overlap* of the transition window and the region where the bump vanishes — i.e. for
`tan α ∈ (1-3τ, 1-2τ)` — the anchor curve of the paper's Step 2 already determines the Radon data
of the body: its two moment equations there, together with Lemma 4.2 (`cl1_forward`, the *forward*
direction), give the inertia condition `(i1)`, and the ball's reference identity
(`radonProfile_data_semicircle`) identifies the resulting datum with the *ball's* datum.

Concretely, if `(X,Y)` is an envelope curve whose two moment equations hold on `[a,b]` with the
ball's constant and the bump vanishes (with its derivative) on `[a,b]`, then for every slope in
`(a,b)` the section datum of `(X,Y)`,

    φ_a(s) := (2n+2) |B^{2n-1}| √(1+s²) · inertiaIntegral n f X Y s,      f = envelopeProfile h X Y,

equals the ball's datum `radonProfile (2n+1) (·)² c` at `c = (√(1+s²))⁻¹`.

This is what makes the *junction* of the piecewise datum function of the low-slope construction
smooth: the datum coming from the anchor agrees with the ball's datum on a whole interval.

The hypothesis `h = h' = 0` on `[a,b]` is not a restriction in the application: the intended range
is `[a,b] ⊆ (1-3τ, 1-2τ)`, where the support hypothesis on `h` forces `h ≡ 0`.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- **The inertia condition on the overlap**, from the anchor's moment equations. -/
theorem anchor_inertiaIntegral (n : ℕ) (hn : 1 ≤ n) {h X Y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hzero : ∀ s ∈ Set.Icc a b, h s = 0) (hder0 : ∀ s ∈ Set.Icc a b, deriv h s = 0)
    (hA : ∀ s ∈ Set.Icc a b,
      Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
        Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2))
    (hB : ∀ s ∈ Set.Icc a b,
      Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0) :
    ∀ s ∈ Set.Ioo a b,
      (1 + s ^ 2) * Real.sqrt (1 + s ^ 2) *
        inertiaIntegral n (Work.OddEnvelope.envelopeProfile h X Y) X Y s = ballInertiaConst n := by
  intro s hs
  have hsI : s ∈ Set.Icc a b := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  have hfwd := cl1_forward n hn H ha hab hA hB s hs
  rw [inertiaIntegral_eq_shifted (n := n) (h := h) (f := Work.OddEnvelope.envelopeProfile h X Y)
    (x := X) (y := Y) (hzero s hsI) (hder0 s hsI)] at hfwd
  rw [hfwd, refConst_eq_inertia n hn]
  field_simp

/-- **The junction identity**: on the overlap the anchor's datum *is* the ball's datum. -/
theorem anchorPhi_eq_ballData (n : ℕ) (hn : 1 ≤ n) {h X Y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hzero : ∀ s ∈ Set.Icc a b, h s = 0) (hder0 : ∀ s ∈ Set.Icc a b, deriv h s = 0)
    (hA : ∀ s ∈ Set.Icc a b,
      Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
        Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2))
    (hB : ∀ s ∈ Set.Icc a b,
      Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0) :
    ∀ s ∈ Set.Ioo a b,
      (2 * (n : ℝ) + 2) * ballVol (2 * n - 1) * Real.sqrt (1 + s ^ 2) *
          inertiaIntegral n (Work.OddEnvelope.envelopeProfile h X Y) X Y s =
        Work.OddRadon.radonProfile (2 * n + 1) (fun u : ℝ => u ^ 2)
          ((Real.sqrt (1 + s ^ 2))⁻¹) := by
  intro s hs
  have hiner := anchor_inertiaIntegral n hn H ha hab hzero hder0 hA hB s hs
  have hspos : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hcpos : 0 < (Real.sqrt (1 + s ^ 2))⁻¹ := inv_pos.mpr hspos
  have hc1 : (Real.sqrt (1 + s ^ 2))⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hspos]; exact Real.one_le_sqrt.mpr (by linarith [sq_nonneg s])
  have hcsq : ((Real.sqrt (1 + s ^ 2))⁻¹) ^ 2 = (1 + s ^ 2)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  rw [radonProfile_data_semicircle n hn hcpos hc1, hcsq]
  have hne : (1 + s ^ 2) ≠ 0 := by positivity
  have h4 : Real.sqrt (1 + s ^ 2) *
      inertiaIntegral n (Work.OddEnvelope.envelopeProfile h X Y) X Y s =
        ballInertiaConst n / (1 + s ^ 2) := by
    refine (eq_div_iff hne).mpr ?_
    have hkey := hiner
    rw [mul_assoc] at hkey
    rw [mul_comm (1 + s ^ 2) (Real.sqrt (1 + s ^ 2) *
      inertiaIntegral n (Work.OddEnvelope.envelopeProfile h X Y) X Y s)] at hkey
    exact hkey
  have h4' : Real.sqrt (1 + s ^ 2) *
      inertiaIntegral n (Work.OddEnvelope.envelopeProfile h X Y) X Y s =
        ballInertiaConst n * (1 + s ^ 2)⁻¹ := by
    rw [h4, div_eq_mul_inv]
  calc (2 * (n : ℝ) + 2) * ballVol (2 * n - 1) * Real.sqrt (1 + s ^ 2) *
        inertiaIntegral n (Work.OddEnvelope.envelopeProfile h X Y) X Y s
      = (2 * (n : ℝ) + 2) * ballVol (2 * n - 1) *
          (Real.sqrt (1 + s ^ 2) *
            inertiaIntegral n (Work.OddEnvelope.envelopeProfile h X Y) X Y s) := by ring
    _ = (2 * (n : ℝ) + 2) * ballVol (2 * n - 1) *
          (ballInertiaConst n * (1 + s ^ 2)⁻¹) := by rw [h4']
    _ = (2 * (n : ℝ) + 2) * ballVol (2 * n - 1) * ballInertiaConst n * (1 + s ^ 2)⁻¹ := by
          ring

end

end Work.OddCurve.LowSlope
